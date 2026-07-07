import gi
import random
import time
import threading
import pygame
import json
import os
from midiutil import MIDIFile
from pydub import AudioSegment
from pydub.effects import normalize
import numpy as np
gi.require_version('Gtk', '3.0')
from gi.repository import Gtk, GLib, Gdk
import warnings
warnings.filterwarnings("ignore", category=SyntaxWarning)
import sqlite3
import librosa
import soundfile as sf

# MIDI OUT support (tylko fizyczne porty USB MIDI)
try:
    import rtmidi
    RTMIDI_AVAILABLE = True
except ImportError:
    RTMIDI_AVAILABLE = False
    print("python-rtmidi niedostępne. Zainstaluj: pip install python-rtmidi --break-system-packages")

class DrumSamplerApp(Gtk.Window):
    def __init__(self):
        Gtk.Window.__init__(self, title="Drum Sampler")
        self.set_border_width(10)
        self.set_default_size(1280, 720)
        self.is_fullscreen = False
        self.scale_factor = 1.0

        # MIDI OUT setup (tylko fizyczne porty USB)
        self.midi_out = None
        self.midi_enabled = False
        self.current_midi_port = None
        self.mute_samples = False  # Wyciszenie lokalnych sampli
        self.init_midi_out()

        pygame.mixer.init()

        # Main container
        scroll_window = Gtk.ScrolledWindow()
        scroll_window.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        self.main_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        scroll_window.add(self.main_box)
        self.add(scroll_window)

        # Base settings
        self.base_bpm = 80
        self.absolute_bpm = 120
        self.genre_bpm = {"House": 125, "Techno": 130, "Drum and Bass": 165, "Ambient": 80}
        self.instruments = ['Talerz', 'Stopa', 'Werbel', 'TomTom']
        self.advanced_sequencer_mode = False
        self.performer_mode = False  # Nowy tryb Performer
        self.simple_patterns = {inst: [0] * 16 for inst in self.instruments}
        self.advanced_patterns = {
            inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(16)]
            for inst in self.instruments
        }
        self.patterns = self.simple_patterns
        self.colors = ['red', 'green', 'blue', 'orange']
        self.midi_notes = {'Talerz': 49, 'Stopa': 36, 'Werbel': 38, 'TomTom': 45}
        
        # Mapowanie MIDI CC dla każdego instrumentu (CC per instrument)
        # Talerz (Hi-Hat): CC 20-24, Stopa (Kick): CC 30-34, Werbel (Snare): CC 40-44, TomTom: CC 50-54
        self.midi_cc_map = {
            'Talerz': {'volume': 20, 'pitch': 21, 'echo': 22, 'reverb': 23, 'pan': 24},
            'Stopa':  {'volume': 30, 'pitch': 31, 'echo': 32, 'reverb': 33, 'pan': 34},
            'Werbel': {'volume': 40, 'pitch': 41, 'echo': 42, 'reverb': 43, 'pan': 44},
            'TomTom': {'volume': 50, 'pitch': 51, 'echo': 52, 'reverb': 53, 'pan': 54}
        }
        
        self.buttons = {}
        self.samples = {}
        self.effects = {inst: {'volume': 0, 'pitch': 0, 'echo': 0, 'reverb': 0, 'pan': 0} for inst in self.instruments}
        self.last_button_pressed = None
        self.rhythm_types = {
            'single': {'notes': 1, 'speed': 1.0, 'swing': 0.0},  # Pojedyncza nuta
            'double': {'notes': 2, 'speed': 0.5, 'swing': 0.0},  # Dwie nuty w kroku
            'burst': {'notes': 3, 'speed': 0.25, 'swing': 0.0},  # Szybki burst (trzy nuty)
            'swing': {'notes': 2, 'speed': 0.5, 'swing': 0.2},   # Dwie nuty ze swingiem
            'accent': {'notes': 1, 'speed': 1.0, 'swing': 0.0}   # Pojedyncza nuta z akcentem
        }

        # Load samples
        self.load_samples_from_directory()

        # UI setup
        self.create_toolbar()
        self.create_midi_controls()
        self.grid = Gtk.Grid()
        self.main_box.pack_start(self.grid, True, True, 0)

        # Grid setup
        for step in range(16):
            label = Gtk.Label(label=str(step + 1))
            self.grid.attach(label, step + 1, 0, 1, 1)

        for idx, (instrument, color) in enumerate(zip(self.instruments, self.colors)):
            label = Gtk.Label(label=instrument)
            self.grid.attach(label, 0, idx + 1, 1, 1)
            self.buttons[instrument] = []
            for step in range(16):
                button = Gtk.ToggleButton()
                button.set_size_request(30, 30)
                context = button.get_style_context()
                context.add_class(f"circle-{color}")
                button.add_events(Gdk.EventMask.SCROLL_MASK | Gdk.EventMask.BUTTON_PRESS_MASK)
                button.connect("toggled", self.on_button_toggled, instrument, step)
                button.connect("scroll-event", self.on_scroll, instrument, step)
                button.connect("button-press-event", self.on_button_press, instrument, step)
                self.grid.attach(button, step + 1, idx + 1, 1, 1)
                self.buttons[instrument].append(button)

        self.loop_playing = False
        self.play_thread = None
        self.dynamic_bpm_list = []
        self.current_bpm_index = 0
        self.steps_per_bpm = 4

        # Connect scaling
        self.connect("size-allocate", self.scale_interface)

        self.effect_sliders = {}
        self.groove_type = 'simple'

        # Additional controls
        self.add_css()
        self.create_groove_controls()
        self.create_drummer_to_audio_button()
        self.create_bpm_controls()
        self.create_matched_bpm_control()
        self.create_dynamic_bpm_control()
        self.create_pattern_controls()
        self.create_pattern_length_control()
        self.create_instrument_randomization_controls()
        self.create_preset_selection()
        self.create_autolevel_button()
        self.create_effect_controls()
        self.create_sample_manipulation_area()

    def init_midi_out(self):
        """Inicjalizacja MIDI OUT - tylko fizyczne porty USB"""
        if not RTMIDI_AVAILABLE:
            print("MIDI OUT: python-rtmidi nie jest dostępne")
            return
        
        try:
            self.midi_out = rtmidi.MidiOut()
            available_ports = self.midi_out.get_ports()
            
            if available_ports:
                print(f"Dostępne porty MIDI OUT: {available_ports}")
                # Automatycznie otwórz pierwszy dostępny port
                self.midi_out.open_port(0)
                self.current_midi_port = 0
                self.midi_enabled = True
                print(f"MIDI OUT: Otwarto port 0 - {available_ports[0]}")
            else:
                print("MIDI OUT: Brak dostępnych portów USB MIDI")
                self.midi_out = None
                self.midi_enabled = False
        except Exception as e:
            print(f"MIDI OUT: Błąd inicjalizacji: {e}")
            self.midi_out = None
            self.midi_enabled = False

    def send_midi_note(self, instrument, velocity=100, duration_ms=50):
        """Wysyła notę MIDI na fizyczny port USB"""
        if not self.midi_enabled or not self.midi_out:
            return
        
        try:
            note = self.midi_notes.get(instrument, 36)
            
            # Wysyłaj Note ON (0x99 = Note On na kanale 10 dla perkusji)
            self.midi_out.send_message([0x99, note, velocity])
            
            # Zaplanuj Note OFF po określonym czasie
            def send_note_off():
                try:
                    if self.midi_out and self.midi_enabled:
                        self.midi_out.send_message([0x89, note, 0])
                except Exception as e:
                    print(f"Błąd wysyłania Note OFF: {e}")
                return False  # Nie powtarzaj
            
            # Użyj GLib.timeout_add do wysłania note off
            GLib.timeout_add(duration_ms, send_note_off)
            
        except Exception as e:
            print(f"Błąd wysyłania nuty MIDI: {e}")

    def send_midi_cc(self, instrument, effect_name, value):
        """Wysyła MIDI Control Change dla efektu instrumentu
        
        Args:
            instrument: nazwa instrumentu ('Talerz', 'Stopa', 'Werbel', 'TomTom')
            effect_name: nazwa efektu ('volume', 'pitch', 'echo', 'reverb', 'pan')
            value: wartość efektu (-100 do 100 lub 0 do 127)
        """
        if not self.midi_enabled or not self.midi_out:
            return
        
        try:
            # Pobierz numer CC dla instrumentu i efektu
            if instrument not in self.midi_cc_map or effect_name not in self.midi_cc_map[instrument]:
                return
            
            cc_number = self.midi_cc_map[instrument][effect_name]
            
            # Konwertuj wartość do zakresu MIDI (0-127)
            # Efekty mają zazwyczaj zakres -100 do 100 lub 0 do 100
            if value < 0:
                # Zakres -100 do 100 → 0 do 127
                midi_value = int((value + 100) * 127 / 200)
            else:
                # Zakres 0 do 100 → 0 do 127
                midi_value = int(value * 127 / 100)
            
            # Ogranicz do 0-127
            midi_value = max(0, min(127, midi_value))
            
            # Wyślij CC na kanale 10 (0xB9 = CC na kanale 10)
            self.midi_out.send_message([0xB9, cc_number, midi_value])
            
            print(f"MIDI CC: {instrument} {effect_name}={value} → CC{cc_number}={midi_value}")
            
        except Exception as e:
            print(f"Błąd wysyłania MIDI CC: {e}")

    def send_all_effects_as_cc(self, instrument):
        """Wysyła wszystkie efekty danego instrumentu jako MIDI CC"""
        if instrument not in self.effects:
            return
        
        for effect_name, value in self.effects[instrument].items():
            self.send_midi_cc(instrument, effect_name, value)

    def refresh_midi_ports(self):
        """Odśwież listę dostępnych portów MIDI"""
        self.midi_port_combo.remove_all()
        
        if RTMIDI_AVAILABLE and self.midi_out:
            try:
                available_ports = self.midi_out.get_ports()
                for i, port in enumerate(available_ports):
                    self.midi_port_combo.append_text(f"{i}: {port}")
                    
                if available_ports and self.current_midi_port is not None:
                    self.midi_port_combo.set_active(self.current_midi_port)
            except Exception as e:
                print(f"Błąd odświeżania portów: {e}")

    def on_midi_port_changed(self, combo):
        """Zmiana portu MIDI"""
        if not RTMIDI_AVAILABLE or not self.midi_out:
            return
        
        port_index = combo.get_active()
        if port_index < 0:
            return
        
        try:
            # Zamknij obecny port
            if self.current_midi_port is not None:
                try:
                    self.midi_out.close_port()
                except:
                    pass
            
            # Otwórz nowy port
            self.midi_out.open_port(port_index)
            self.current_midi_port = port_index
            self.midi_enabled = True
            self.midi_toggle.set_active(True)
            print(f"MIDI OUT: Otwarto port {port_index}")
            self.update_midi_status_label()
        except Exception as e:
            print(f"Błąd otwierania portu MIDI: {e}")
            self.midi_enabled = False
            self.midi_toggle.set_active(False)
            self.update_midi_status_label()

    def on_midi_toggle(self, switch, gparam):
        """Włącz/wyłącz MIDI OUT"""
        self.midi_enabled = switch.get_active()
        self.update_midi_status_label()
        print(f"MIDI OUT: {'włączone' if self.midi_enabled else 'wyłączone'}")

    def update_midi_status_label(self):
        """Aktualizuj etykietę statusu MIDI"""
        if not RTMIDI_AVAILABLE:
            self.midi_status_label.set_markup("<span color='red'>❌ rtmidi nie zainstalowane</span>")
        elif self.midi_enabled and self.midi_out and self.current_midi_port is not None:
            self.midi_status_label.set_markup("<span color='green'>✓ MIDI OUT aktywny</span>")
        else:
            self.midi_status_label.set_markup("<span color='orange'>○ MIDI OUT wyłączony</span>")

    def refresh_midi(self, widget=None):
        """Ponowna inicjalizacja MIDI OUT"""
        if self.midi_out:
            try:
                self.midi_out.close_port()
            except:
                pass
            try:
                del self.midi_out
            except:
                pass
        
        self.init_midi_out()
        self.refresh_midi_ports()
        self.update_midi_status_label()

    def create_midi_controls(self):
        """Tworzenie kontrolek MIDI OUT"""
        midi_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        self.main_box.pack_start(midi_box, False, False, 0)
        
        # Separator
        separator = Gtk.Separator(orientation=Gtk.Orientation.HORIZONTAL)
        midi_box.pack_start(separator, False, False, 0)
        
        midi_label = Gtk.Label()
        midi_label.set_markup("<b>MIDI OUT (USB):</b>")
        midi_box.pack_start(midi_label, False, False, 0)
        
        # Włącznik MIDI
        self.midi_toggle = Gtk.Switch()
        self.midi_toggle.set_active(self.midi_enabled)
        self.midi_toggle.connect("notify::active", self.on_midi_toggle)
        midi_box.pack_start(self.midi_toggle, False, False, 0)

        # Status
        self.midi_status_label = Gtk.Label()
        self.update_midi_status_label()
        midi_box.pack_start(self.midi_status_label, False, False, 0)

        # Separator
        sep_virt = Gtk.Separator(orientation=Gtk.Orientation.VERTICAL)
        midi_box.pack_start(sep_virt, False, False, 0)

        # Przycisk Virtual MIDI (snd-virmidi)
        virtual_midi_button = Gtk.Button(label="🎹 Virtual MIDI")
        virtual_midi_button.set_tooltip_text(
            "Sprawdza czy port virtualny istnieje; jeśli nie — ładuje snd-virmidi midi_devs=1"
        )
        virtual_midi_button.connect("clicked", self.setup_virtual_midi)
        midi_box.pack_start(virtual_midi_button, False, False, 0)

        self.virtual_midi_status = Gtk.Label()
        self.virtual_midi_status.set_markup("<span color='gray'>○ ?</span>")
        midi_box.pack_start(self.virtual_midi_status, False, False, 0)
        
        # Wybór portu MIDI
        self.midi_port_combo = Gtk.ComboBoxText()
        self.refresh_midi_ports()
        self.midi_port_combo.connect("changed", self.on_midi_port_changed)
        midi_box.pack_start(self.midi_port_combo, False, False, 0)
        
        # Przycisk odświeżania
        refresh_button = Gtk.Button(label="🔄 Odśwież MIDI")
        refresh_button.connect("clicked", self.refresh_midi)
        midi_box.pack_start(refresh_button, False, False, 0)
        
        # Separator
        separator2 = Gtk.Separator(orientation=Gtk.Orientation.VERTICAL)
        midi_box.pack_start(separator2, False, False, 0)
        
        # Mute Samples (wyciszenie lokalnych sampli)
        mute_label = Gtk.Label()
        mute_label.set_markup("<b>Mute Samples:</b>")
        midi_box.pack_start(mute_label, False, False, 0)
        
        self.mute_samples_toggle = Gtk.Switch()
        self.mute_samples_toggle.set_active(self.mute_samples)
        self.mute_samples_toggle.connect("notify::active", self.on_mute_samples_toggle)
        midi_box.pack_start(self.mute_samples_toggle, False, False, 0)
        
        self.mute_status_label = Gtk.Label()
        self.update_mute_status_label()
        midi_box.pack_start(self.mute_status_label, False, False, 0)
        
        # Separator
        separator3 = Gtk.Separator(orientation=Gtk.Orientation.VERTICAL)
        midi_box.pack_start(separator3, False, False, 0)
        
        # Przycisk wysyłania wszystkich CC
        send_cc_button = Gtk.Button(label="📤 Send All CC")
        send_cc_button.set_tooltip_text("Wyślij wszystkie ustawienia efektów jako MIDI CC do DAW")
        send_cc_button.connect("clicked", self.on_send_all_cc_clicked)
        midi_box.pack_start(send_cc_button, False, False, 0)

    def on_send_all_cc_clicked(self, button):
        """Ręczne wysłanie wszystkich CC"""
        if not self.midi_enabled:
            print("MIDI OUT wyłączone - włącz najpierw MIDI")
            return
        
        for instrument in self.instruments:
            self.send_all_effects_as_cc(instrument)
        
        print("Wysłano wszystkie ustawienia efektów jako MIDI CC")

    def on_mute_samples_toggle(self, switch, gparam):
        """Przełącznik wyciszenia sampli"""
        self.mute_samples = switch.get_active()
        self.update_mute_status_label()
        if self.mute_samples:
            print("Samples wyciszone - gra tylko MIDI OUT")
        else:
            print("Samples włączone - gra audio + MIDI OUT")
    
    def update_mute_status_label(self):
        """Aktualizuj etykietę statusu mute"""
        if self.mute_samples:
            self.mute_status_label.set_markup("<span color='orange'>🔇 Audio OFF</span>")
        else:
            self.mute_status_label.set_markup("<span color='green'>🔊 Audio ON</span>")

    def setup_virtual_midi(self, widget=None):
        """Sprawdza czy wirtualny port snd-virmidi już istnieje; jeśli nie — tworzy go."""
        import subprocess

        def _check_and_create():
            # 1. Sprawdź lsmod
            try:
                lsmod = subprocess.run(['lsmod'], capture_output=True, text=True, timeout=5)
                already_loaded = 'snd_virmidi' in lsmod.stdout
            except Exception:
                already_loaded = False

            # 2. Sprawdź przez aconnect (czy jest port o nazwie Virtual)
            if not already_loaded:
                try:
                    aconn = subprocess.run(['aconnect', '-l'], capture_output=True, text=True, timeout=5)
                    already_loaded = 'Virtual' in aconn.stdout or 'virmidi' in aconn.stdout.lower()
                except Exception:
                    pass

            if already_loaded:
                GLib.idle_add(
                    self.virtual_midi_status.set_markup,
                    "<span color='green'>✓ już istnieje</span>"
                )
                print("Virtual MIDI: snd-virmidi już załadowany — pomijam modprobe")
                GLib.idle_add(self.refresh_midi, None)
                return

            # 3. Załaduj moduł
            print("Virtual MIDI: ładuję snd-virmidi midi_devs=1 …")
            GLib.idle_add(
                self.virtual_midi_status.set_markup,
                "<span color='orange'>⏳ ładowanie…</span>"
            )
            try:
                result = subprocess.run(
                    ['sudo', 'modprobe', 'snd-virmidi', 'midi_devs=1'],
                    capture_output=True, text=True, timeout=15
                )
                if result.returncode == 0:
                    GLib.idle_add(
                        self.virtual_midi_status.set_markup,
                        "<span color='green'>✓ utworzony</span>"
                    )
                    print("Virtual MIDI: snd-virmidi załadowany pomyślnie")
                    import time as _time
                    _time.sleep(0.5)          # chwila na rejestrację urządzenia
                    GLib.idle_add(self.refresh_midi, None)
                else:
                    err = result.stderr.strip() or "nieznany błąd"
                    GLib.idle_add(
                        self.virtual_midi_status.set_markup,
                        f"<span color='red'>❌ {err[:40]}</span>"
                    )
                    print(f"Virtual MIDI błąd modprobe: {err}")
            except Exception as exc:
                GLib.idle_add(
                    self.virtual_midi_status.set_markup,
                    f"<span color='red'>❌ {str(exc)[:40]}</span>"
                )
                print(f"Virtual MIDI wyjątek: {exc}")

        threading.Thread(target=_check_and_create, daemon=True).start()

    def create_toolbar(self):
        toolbar = Gtk.Toolbar()
        self.main_box.pack_start(toolbar, False, False, 0)

        button_info = [
            ("media-playback-start", self.play_pattern, "Play"),
            ("media-playback-stop", self.stop_pattern, "Stop"),
            ("view-refresh", self.randomize_pattern, "Randomize"),
            ("document-open", self.load_samples, "Load Samples"),
            ("document-save", self.save_project, "Save Project"),
            ("document-open", self.load_project, "Load Project"),
            ("document-export", self.export_to_midi, "Export MIDI"),
            ("document-export", self.export_advanced_midi, "Export Advanced MIDI")
        ]

        for icon_name, callback, tooltip in button_info:
            button = Gtk.ToolButton()
            button.set_icon_name(icon_name)
            button.set_tooltip_text(tooltip)
            button.connect("clicked", callback)
            toolbar.insert(button, -1)

        fullscreen_button = Gtk.ToolButton.new(None, "Wejdź w pełny ekran")
        fullscreen_button.connect("clicked", self.toggle_fullscreen)
        toolbar.insert(fullscreen_button, -1)

        # Sequencer Mode
        sequencer_mode_label = Gtk.Label(label="Sequencer Mode:")
        toolbar.insert(Gtk.ToolItem(), -1)
        sequencer_mode_item = Gtk.ToolItem()
        sequencer_mode_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        self.sequencer_mode_switch = Gtk.Switch()
        self.sequencer_mode_switch.set_active(False)
        self.sequencer_mode_switch.connect("notify::active", self.on_sequencer_mode_switch)
        sequencer_mode_label_mode = Gtk.Label(label="Simple | Advanced")
        sequencer_mode_box.pack_start(sequencer_mode_label, False, False, 0)
        sequencer_mode_box.pack_start(self.sequencer_mode_switch, False, False, 5)
        sequencer_mode_box.pack_start(sequencer_mode_label_mode, False, False, 0)
        sequencer_mode_item.add(sequencer_mode_box)
        toolbar.insert(sequencer_mode_item, -1)

        # Performer Mode
        performer_mode_label = Gtk.Label(label="Performer Mode:")
        toolbar.insert(Gtk.ToolItem(), -1)
        performer_mode_item = Gtk.ToolItem()
        performer_mode_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        self.performer_mode_switch = Gtk.Switch()
        self.performer_mode_switch.set_active(False)
        self.performer_mode_switch.connect("notify::active", self.on_performer_mode_switch)
        performer_mode_label_mode = Gtk.Label(label="Off | On")
        performer_mode_box.pack_start(performer_mode_label, False, False, 0)
        performer_mode_box.pack_start(self.performer_mode_switch, False, False, 5)
        performer_mode_box.pack_start(performer_mode_label_mode, False, False, 0)
        performer_mode_item.add(performer_mode_box)
        toolbar.insert(performer_mode_item, -1)

        # Audio Backend
        audio_backend_label = Gtk.Label(label="Audio Backend:")
        toolbar.insert(Gtk.ToolItem(), -1)
        audio_backend_item = Gtk.ToolItem()
        backend_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        self.backend_combo = Gtk.ComboBoxText()
        self.backend_combo.append_text("PipeWire")
        self.backend_combo.append_text("JACK")
        self.backend_combo.set_active(0)
        backend_box.pack_start(audio_backend_label, False, False, 0)
        backend_box.pack_start(self.backend_combo, False, False, 0)
        audio_backend_item.add(backend_box)
        toolbar.insert(audio_backend_item, -1)
        toolbar.show_all()

    def add_css(self):
        css_provider = Gtk.CssProvider()
        css = """
        .circle-red, .circle-green, .circle-blue, .circle-orange {
            border-radius: 15px;
            background-color: white;
        }
        .circle-red:active { background-color: red; }
        .circle-green:active { background-color: green; }
        .circle-blue:active { background-color: blue; }
        .circle-orange:active { background-color: orange; }
        @keyframes blink-animation {
            0% { opacity: 1; }
            50% { opacity: 0; }
            100% { opacity: 1; }
        }
        .blink {
            animation: blink-animation 0.5s linear 2;
        }
        """
        css_provider.load_from_data(css.encode())
        Gtk.StyleContext.add_provider_for_screen(
            Gdk.Screen.get_default(),
            css_provider,
            Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION
        )

    def create_bpm_controls(self):
        bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(bpm_box, False, False, 0)

        bpm_label = Gtk.Label(label="Absolute BPM:")
        bpm_box.pack_start(bpm_label, False, False, 0)

        self.bpm_entry = Gtk.Entry()
        self.bpm_entry.set_text(str(self.absolute_bpm))
        self.bpm_entry.set_width_chars(4)
        bpm_box.pack_start(self.bpm_entry, False, False, 0)

        bpm_up_button = Gtk.Button()
        bpm_up_button.set_image(Gtk.Image.new_from_icon_name("go-up", Gtk.IconSize.SMALL_TOOLBAR))
        bpm_up_button.connect("clicked", self.bpm_step_up)
        bpm_box.pack_start(bpm_up_button, False, False, 0)

        bpm_down_button = Gtk.Button()
        bpm_down_button.set_image(Gtk.Image.new_from_icon_name("go-down", Gtk.IconSize.SMALL_TOOLBAR))
        bpm_down_button.connect("clicked", self.bpm_step_down)
        bpm_box.pack_start(bpm_down_button, False, False, 0)

    def create_matched_bpm_control(self):
        bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(bpm_box, False, False, 0)

        matched_bpm_button = Gtk.Button(label="Matched BPM")
        matched_bpm_button.connect("clicked", self.matched_bpm)
        bpm_box.pack_start(matched_bpm_button, False, False, 0)

        perfect_bpm_button = Gtk.Button(label="Perfect Tempo BPM")
        perfect_bpm_button.connect("clicked", self.perfect_tempo_bpm)
        bpm_box.pack_start(perfect_bpm_button, False, False, 0)

    def create_dynamic_bpm_control(self):
        dynamic_bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(dynamic_bpm_box, False, False, 0)

        dynamic_bpm_label = Gtk.Label(label="Dynamic BPM (%):")
        dynamic_bpm_box.pack_start(dynamic_bpm_label, False, False, 0)

        self.dynamic_bpm_entry = Gtk.Entry()
        self.dynamic_bpm_entry.set_text("100,110,90,105")
        self.dynamic_bpm_entry.set_width_chars(20)
        dynamic_bpm_box.pack_start(self.dynamic_bpm_entry, False, False, 0)

        apply_button = Gtk.Button(label="Apply Dynamic BPM")
        apply_button.connect("clicked", self.apply_dynamic_bpm)
        dynamic_bpm_box.pack_start(apply_button, False, False, 0)

    def create_pattern_controls(self):
        genre_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        genre_box.set_margin_top(10)
        genre_box.set_margin_bottom(10)
        genre_box.set_margin_start(10)
        genre_box.set_margin_end(10)
        self.main_box.pack_start(genre_box, False, False, 0)
    
        preset_label = Gtk.Label()
        preset_label.set_markup("<b>FX Genre:</b>")
        genre_box.pack_start(preset_label, False, False, 0)
    
        self.preset_genre_combo = Gtk.ComboBoxText()
        genres = ["House", "Techno", "Drum and Bass", "Ambient", "Trap", "Dubstep", "Jazz", "Breakbeat"]
        for genre in genres:
            self.preset_genre_combo.append_text(genre)
        self.preset_genre_combo.set_active(0)
        genre_box.pack_start(self.preset_genre_combo, False, False, 0)
    
        auto_fx_button = Gtk.Button(label="🎨 Apply Genre FX")
        auto_fx_button.set_size_request(150, 35)
        auto_fx_button.set_tooltip_text("Zastosuj preset efektów dla wybranego gatunku")
        auto_fx_button.connect("clicked", self.apply_auto_fx_for_selected_style)
        genre_box.pack_start(auto_fx_button, False, False, 0)
        
        # Wskaźnik zastosowanego genre
        self.genre_status_label = Gtk.Label()
        self.genre_status_label.set_markup("<span color='gray'>Brak FX</span>")
        genre_box.pack_start(self.genre_status_label, False, False, 0)
    
        reset_fx_button = Gtk.Button(label="Reset Genre FX")
        reset_fx_button.set_size_request(130, 35)
        reset_fx_button.connect("clicked", self.reset_genre_fx)
        genre_box.pack_start(reset_fx_button, False, False, 0)
    
        separator = Gtk.Separator(orientation=Gtk.Orientation.VERTICAL)
        genre_box.pack_start(separator, False, False, 10)
    
        # ── Custom Pattern Generator (parametryczny) ──────────────────────────
        custom_frame_label = Gtk.Label()
        custom_frame_label.set_markup("<b>Custom Pattern:</b>")
        genre_box.pack_start(custom_frame_label, False, False, 0)

        # Pattern Type (sekcja utworu)
        ptype_label = Gtk.Label(label="Type:")
        genre_box.pack_start(ptype_label, False, False, 0)
        self.pattern_type_combo = Gtk.ComboBoxText()
        for pt in ["intro", "verse", "chorus", "bridge", "break", "drop", "fill", "outro"]:
            self.pattern_type_combo.append_text(pt)
        self.pattern_type_combo.set_active(1)   # verse domyślnie
        genre_box.pack_start(self.pattern_type_combo, False, False, 0)

        # Rhythm Style
        rstyle_label = Gtk.Label(label="Rhythm:")
        genre_box.pack_start(rstyle_label, False, False, 0)
        self.rhythm_style_combo = Gtk.ComboBoxText()
        for rs in ["steady", "syncopated", "sparse", "dense", "triplet"]:
            self.rhythm_style_combo.append_text(rs)
        self.rhythm_style_combo.set_active(0)
        genre_box.pack_start(self.rhythm_style_combo, False, False, 0)

        # Complexity
        cplx_label = Gtk.Label(label="Complexity:")
        genre_box.pack_start(cplx_label, False, False, 0)
        self.complexity_combo = Gtk.ComboBoxText()
        for cx in ["low", "medium", "high"]:
            self.complexity_combo.append_text(cx)
        self.complexity_combo.set_active(1)
        genre_box.pack_start(self.complexity_combo, False, False, 0)

        # Intensity
        intensity_label = Gtk.Label(label="Intensity:")
        genre_box.pack_start(intensity_label, False, False, 0)
        self.intensity_spin = Gtk.SpinButton()
        self.intensity_spin.set_adjustment(
            Gtk.Adjustment(value=0.5, lower=0.0, upper=1.0, step_increment=0.1)
        )
        self.intensity_spin.set_numeric(True)
        self.intensity_spin.set_digits(1)
        genre_box.pack_start(self.intensity_spin, False, False, 0)

        # Occurrences (repetitions of seed pattern)
        occ_label = Gtk.Label(label="Repeat:")
        genre_box.pack_start(occ_label, False, False, 0)
        self.occurrences_spin = Gtk.SpinButton()
        self.occurrences_spin.set_adjustment(
            Gtk.Adjustment(value=4, lower=1, upper=16, step_increment=1)
        )
        genre_box.pack_start(self.occurrences_spin, False, False, 0)

        generate_button = Gtk.Button(label="▶ Generate")
        generate_button.connect("clicked", self.generate_custom_pattern)
        genre_box.pack_start(generate_button, False, False, 0)
    
        genre_box.show_all()

    def create_pattern_length_control(self):
        length_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(length_box, False, False, 0)

        length_label = Gtk.Label(label="Pattern Length:")
        length_box.pack_start(length_label, False, False, 0)

        self.length_adjustment = Gtk.Adjustment(value=16, lower=4, upper=32, step_increment=4)
        self.length_spinbutton = Gtk.SpinButton()
        self.length_spinbutton.set_adjustment(self.length_adjustment)
        self.length_spinbutton.connect("value-changed", self.on_pattern_length_changed)
        length_box.pack_start(self.length_spinbutton, False, False, 0)

    def create_instrument_randomization_controls(self):
        randomize_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(randomize_box, False, False, 0)

        randomize_label = Gtk.Label(label="Instrument Randomization:")
        randomize_box.pack_start(randomize_label, False, False, 0)

        self.randomize_probability_adjustment = Gtk.Adjustment(value=10, lower=0, upper=100, step_increment=1)
        self.randomize_probability_spin = Gtk.SpinButton()
        self.randomize_probability_spin.set_adjustment(self.randomize_probability_adjustment)
        self.randomize_probability_spin.set_value(10)
        randomize_box.pack_start(self.randomize_probability_spin, False, False, 0)

        randomize_button = Gtk.Button(label="Randomize Instruments")
        randomize_button.connect("clicked", self.randomize_instruments)
        randomize_box.pack_start(randomize_button, False, False, 0)

        autofill_button = Gtk.Button(label="Autofill")
        autofill_button.connect("clicked", lambda widget: self.autofill_pattern())
        randomize_box.pack_start(autofill_button, False, False, 0)

    def create_preset_selection(self):
        preset_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(preset_box, False, False, 0)

        preset_label = Gtk.Label(label="Genre Preset:")
        preset_box.pack_start(preset_label, False, False, 0)

        self.preset_combo = Gtk.ComboBoxText()
        self.preset_combo.append_text("None")
        self.preset_combo.append_text("Basic Techno")
        self.preset_combo.append_text("Minimal Techno")
        self.preset_combo.append_text("Hard Techno")
        self.preset_combo.set_active(0)
        preset_box.pack_start(self.preset_combo, False, False, 0)

        apply_preset_button = Gtk.Button(label="Apply Preset")
        apply_preset_button.connect("clicked", self.apply_preset)
        preset_box.pack_start(apply_preset_button, False, False, 0)

    def create_autolevel_button(self):
        autolevel_button = Gtk.Button(label="Auto Level")
        autolevel_button.connect("clicked", self.autolevel_samples)
        self.main_box.pack_start(autolevel_button, False, False, 0)

    def create_effect_controls(self):
        effect_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10)
        effect_box.set_hexpand(True)
        effect_box.set_margin_top(10)
        effect_box.set_margin_bottom(10)
        self.main_box.pack_start(effect_box, False, False, 0)

        effect_title = Gtk.Label()
        effect_title.set_markup("<b><big>Audio Effects</big></b>")
        effect_box.pack_start(effect_title, False, False, 0)

        effect_grid = Gtk.Grid()
        effect_grid.set_column_spacing(15)
        effect_grid.set_row_spacing(10)
        effect_grid.set_margin_start(10)
        effect_grid.set_margin_end(10)
        effect_box.pack_start(effect_grid, True, True, 0)

        effects = ['Volume', 'Pitch', 'Echo', 'Reverb', 'Pan']
        for col, effect in enumerate(effects, start=1):
            label = Gtk.Label()
            label.set_markup(f"<b>{effect}</b>")
            effect_grid.attach(label, col, 0, 1, 1)

        for row, instrument in enumerate(self.instruments, start=1):
            label = Gtk.Label()
            label.set_markup(f"<b>{instrument}</b>")
            effect_grid.attach(label, 0, row, 1, 1)
            self.effect_sliders[instrument] = {}

            for col, effect in enumerate(effects, start=1):
                adjustment = Gtk.Adjustment(value=0, lower=-5, upper=5, step_increment=0.1)
                slider = Gtk.Scale(orientation=Gtk.Orientation.HORIZONTAL, adjustment=adjustment)
                slider.set_digits(1)
                slider.set_hexpand(True)
                slider.set_size_request(150, 35)  # Minimalna szerokość i wysokość
                slider.set_draw_value(True)  # Pokaż wartość na suwa ku
                slider.set_value_pos(Gtk.PositionType.TOP)  # Wartość na górze
                slider.connect('value-changed', self.on_effect_changed, instrument, effect.lower())
                effect_grid.attach(slider, col, row, 1, 1)
                self.effect_sliders[instrument][effect.lower()] = slider

                reset_button = Gtk.Button(label="↺")
                reset_button.set_size_request(40, 35)
                reset_button.set_tooltip_text(f"Reset {effect}")
                reset_button.connect('clicked', self.reset_effect, slider, instrument, effect.lower())
                effect_grid.attach_next_to(reset_button, slider, Gtk.PositionType.RIGHT, 1, 1)

        button_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        button_box.set_halign(Gtk.Align.CENTER)
        effect_box.pack_start(button_box, False, False, 10)
        
        reset_all_button = Gtk.Button(label="Reset All Effects")
        reset_all_button.set_size_request(150, 40)
        reset_all_button.connect("clicked", self.reset_all_effects)
        button_box.pack_start(reset_all_button, False, False, 0)

    def create_groove_controls(self):
        groove_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        groove_box.set_margin_top(10)
        groove_box.set_margin_bottom(10)
        groove_box.set_margin_start(10)
        groove_box.set_margin_end(10)
        self.main_box.pack_start(groove_box, False, False, 0)

        groove_label = Gtk.Label()
        groove_label.set_markup("<b>Groove Type:</b>")
        groove_box.pack_start(groove_label, False, False, 0)

        self.groove_combo = Gtk.ComboBoxText()
        groove_types = ["simple", "stretch", "echoes", "bouncy", "relax"]
        for groove in groove_types:
            self.groove_combo.append_text(groove)
        self.groove_combo.set_active(0)
        self.groove_combo.connect("changed", self.on_groove_changed)  # Zmiana w czasie rzeczywistym
        groove_box.pack_start(self.groove_combo, False, False, 0)
        
        # Wskaźnik aktywnego groove
        self.groove_status_label = Gtk.Label()
        self.update_groove_status()
        groove_box.pack_start(self.groove_status_label, False, False, 0)

        groove_button = Gtk.Button(label="Apply & Play Groove")
        groove_button.set_size_request(150, 35)
        groove_button.connect("clicked", self.apply_groove)
        groove_box.pack_start(groove_button, False, False, 0)

        reset_groove_button = Gtk.Button(label="Reset Groove")
        reset_groove_button.set_size_request(120, 35)
        reset_groove_button.connect("clicked", self.reset_groove)
        groove_box.pack_start(reset_groove_button, False, False, 0)

    def on_groove_changed(self, combo):
        """Zmiana groove type w czasie rzeczywistym"""
        self.groove_type = combo.get_active_text()
        self.update_groove_status()
        print(f"Groove zmieniony na: {self.groove_type}")
    
    def update_groove_status(self):
        """Aktualizuj wskaźnik statusu groove"""
        if hasattr(self, 'groove_status_label'):
            status_text = f"<span color='green'>✓ {self.groove_type.upper()}</span>"
            self.groove_status_label.set_markup(status_text)

    def create_drummer_to_audio_button(self):
        drummer_button = Gtk.Button(label="Add Drummer to Audio")
        drummer_button.connect("clicked", self.add_drummer_to_audio)
        self.main_box.pack_start(drummer_button, False, False, 0)

    def add_drummer_to_audio(self, widget):
        file_dialog = Gtk.FileChooserDialog(title="Select Audio File", parent=self)
        file_dialog.add_buttons(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK)

        progress_dialog = Gtk.Dialog(title="Generating Percussion", transient_for=self, modal=True)
        progress_dialog.set_default_size(350, 120)

        progress_bar = Gtk.ProgressBar()
        progress_bar.set_show_text(True)
        progress_dialog.get_content_area().pack_start(progress_bar, True, True, 10)
        progress_dialog.show_all()

        def update_progress(fraction, message):
            GLib.idle_add(progress_bar.set_fraction, fraction)
            GLib.idle_add(progress_bar.set_text, message)

        def generate_drums_thread(audio_path):
            try:
                update_progress(0.05, "Loading audio and extracting spectrum...")
                y, sr = librosa.load(audio_path, sr=22050)
                
                # 1. Zaawansowana analiza频谱owa (zamiast prostego split)
                update_progress(0.15, "Analyzing frequency spectrum (Bass, Mid, High)...")
                spectral_map = self.analyze_spectral_layers(y, sr)
                
                update_progress(0.25, "Extracting tempo and beat grid...")
                tempo, beat_frames = librosa.beat.beat_track(y=y, sr=sr)
                beat_times = librosa.frames_to_time(beat_frames, sr=sr)
                
                update_progress(0.35, "Detecting structural segments (ignoring noise/reverb)...")
                # Używamy warstwy "Mid/Lead" do wykrywania struktury, ignorując tło
                valid_segments = self.detect_structure_from_music(spectral_map['mid'], sr)
                
                if len(valid_segments) < 2:
                    raise ValueError("Could not find enough musical structure (leads/bass) to generate drums. File might be pure noise/ambient.")

                update_progress(0.50, "Mapping song structure (Intro, Verse, Chorus)...")
                structure_map = self.map_song_structure(valid_segments, tempo, sr)

                update_progress(0.65, "Generating complementary drum track...")
                percussion_track = self.advanced_generate_drum_track(structure_map, spectral_map, tempo, sr)

                update_progress(0.80, "Synthesizing audio from samples...")
                percussion_audio = self.synthesize_percussion_audio(percussion_track, sr, tempo)

                update_progress(0.90, "Mixing and mastering tracks...")
                self.save_generated_tracks(audio_path, percussion_audio, y, sr)

                update_progress(1.0, "Done!")
                GLib.timeout_add(500, lambda: (progress_dialog.destroy(), 
                                                self.show_save_confirmation(
                                                    audio_path.replace(".mp3", "_drums_only.wav").replace(".wav", "_drums_only.wav"),
                                                    audio_path.replace(".mp3", "_mixed.wav").replace(".wav", "_mixed.wav")
                                                ))[0])
                                                
            except Exception as e:
                GLib.idle_add(progress_dialog.destroy)
                GLib.idle_add(self.show_error_dialog, str(e))

        response = file_dialog.run()
        if response == Gtk.ResponseType.OK:
            audio_path = file_dialog.get_filename()
            file_dialog.destroy()
            threading.Thread(target=generate_drums_thread, args=(audio_path,), daemon=True).start()
        else:
            file_dialog.destroy()

    def analyze_spectral_layers(self, y, sr):
        """
        Rozdziela频spektrum na warstwy: Bas (<250Hz), Mid/Lead (250-4kHz), Tło/High (>4kHz).
        Zwraca słownik z wyizolowanymi sygnałami dla każdej warstwy.
        """
        D = librosa.stft(y)
        magnitude = np.abs(D)
        freqs = librosa.fft_frequencies(sr=sr)

        # Maski频谱owe
        bass_mask = freqs < 250
        mid_mask = (freqs >= 250) & (freqs < 4000)
        high_mask = freqs >= 4000

        # Rekonstrukcja sygnałów w domenie czasu
        y_bass = librosa.istft(D * bass_mask)
        y_mid = librosa.istft(D * mid_mask)
        y_high = librosa.istft(D * high_mask)

        return {
            'bass': y_bass,
            'mid': y_mid,      # Głównie Lead / Wokal / Mid-range syntezatory
            'high': y_high,    # Tło, pogłos, szum, hi-haty oryginalne
            'full': y
        }

    def detect_structure_from_music(self, y_music, sr):
        """
        Zamiast używać prostego librosa.effects.split (który wyłapuje szum),
        szukamy "prawdziwych" onsetów w warstwie Mid/Bas na podstawie energii.
        """
        # Obliczamy energię ramek
        frame_length = 2048
        energy = np.array([
            np.sum(np.abs(y_music[i:i+frame_length])**2)
            for i in range(0, len(y_music) - frame_length, frame_length // 2)
        ])
        
        # Prosta normalizacja
        if np.max(energy) > 0:
            energy = energy / np.max(energy)

        # Wykrywamy punkty, w których energia gwałtownie rośnie (Onset Detection)
        onset_env = librosa.onset.onset_strength(y=y_music, sr=sr)
        peaks = librosa.util.peak_pick(onset_env, pre_max=3, post_max=5, pre_avg=5, post_avg=5)

        if len(peaks) < 2:
            # Fallback na równe podziały, jeśli brak wyraźnych peaków
            total_frames = len(y_music)
            num_segments = max(2, int(librosa.get_duration(y=y_music, sr=sr) / 4.0)) # Segment co ~4 sekundy
            return [(i * total_frames // num_segments, (i+1) * total_frames // num_segments) for i in range(num_segments)]

        # Grupujemy peaki w segmenty
        frames = librosa.time_to_frames(peaks, sr=sr)
        segments = []
        start_frame = 0
        
        for i in range(1, len(frames)):
            # Jeśli przerwa między peakami jest większa niż 1.5 sekundy, kończymy segment
            time_diff = peaks[i] - peaks[i-1]
            if time_diff > 1.5:
                end_frame = frames[i]
                segments.append((start_frame, end_frame))
                start_frame = end_frame
                
        # Dodaj ostatni segment
        segments.append((start_frame, len(y_music)))
        
        return segments

    def map_song_structure(self, segments, tempo, sr):
        """
        Analizuje listę segmentów i przypisuje im tagi struktury (intro, verse, chorus)
        na podstawie gęstości onsetów (energii) w danym segmencie.
        """
        structure = []
        total_segments = len(segments)
        
        # Obliczamy "gęstość" muzyczną dla każdego segmentu (ile nut na sekundę)
        segment_densities = []
        for start, end in segments:
            duration = librosa.frames_to_time(end - start, sr=sr)
            if duration == 0: duration = 0.1
            # Przybliżona gęstość (zakładając średnią rozdzielczość onsetów)
            density = (end - start) / (duration * 100)
            segment_densities.append(density)

        max_density = max(segment_densities) if max(segment_densities) > 0 else 1
        min_density = min(segment_densities)

        for i, (start, end) in enumerate(segments):
            duration = librosa.frames_to_time(end - start, sr=sr)
            norm_density = (segment_densities[i] - min_density) / (max_density - min_density + 0.001)
            
            # Logika struktury
            if i == 0:
                tag = "intro"
            elif i == total_segments - 1:
                tag = "outro"
            elif norm_density > 0.7:
                tag = "chorus"  # Największa gęstość = Chorus/Drop
            elif norm_density < 0.3:
                tag = "break"   # Najmniejsza gęstość = Break/Outro
            else:
                tag = "verse"   # Środek = Verse/Bridge

            structure.append({
                'start_frame': start,
                'end_frame': end,
                'duration_sec': duration,
                'tag': tag,
                'density': norm_density
            })
            
        return structure

    def advanced_generate_drum_track(self, structure_map, spectral_map, tempo, sr):
        """
        Generuje ścieżkę perkusyjną OPARTĄ O STRUKTURĘ I ANALIZĘ频谱OWĄ.
        Zamiast losowości, używa reguł muzycznych zależnych od tagu (verse/chorus).
        """
        steps_per_beat = 4  # 16th notes
        beats_per_second = tempo / 60.0
        
        # Inicjalizacja pustej ścieżki
        total_duration = structure_map[-1]['end_frame'] / sr
        total_steps = int(total_duration * beats_per_second * steps_per_beat)
        
        percussion_track = {inst: [0] * total_steps for inst in self.instruments}
        
        # Reguły generowania per tag struktury
        rules = {
            "intro":  {'Stopa': 0.2, 'Werbel': 0.1, 'Talerz': 0.3, 'TomTom': 0.0, 'style': 'sparse'},
            "verse":  {'Stopa': 0.6, 'Werbel': 0.4, 'Talerz': 0.6, 'TomTom': 0.1, 'style': 'groove'},
            "chorus": {'Stopa': 0.9, 'Werbel': 0.8, 'Talerz': 0.9, 'TomTom': 0.4, 'style': 'dense'},
            "break":  {'Stopa': 0.0, 'Werbel': 0.0, 'Talerz': 0.1, 'TomTom': 0.0, 'style': 'fill'},
            "outro": {'Stopa': 0.3, 'Werbel': 0.2, 'Talerz': 0.4, 'TomTom': 0.0, 'style': 'sparse'}
        }

        for segment in structure_map:
            tag = segment['tag']
            rule = rules.get(tag, rules['verse'])
            
            start_step = int((segment['start_frame'] / sr) * beats_per_second * steps_per_beat)
            end_step = int((segment['end_frame'] / sr) * beats_per_second * steps_per_beat)
            
            for step in range(start_step, min(end_step, total_steps)):
                beat_pos = step % steps_per_beat  # Pozycja w uderzeniu (0-3)
                
                # GENEROWANIE STOPY (Zależne od basu)
                if rule['Stopa'] > 0:
                    if rule['style'] == 'dense' and beat_pos == 0: percussion_track['Stopa'][step] = 1
                    elif rule['style'] == 'groove' and beat_pos in [0, 2]: percussion_track['Stopa'][step] = 1
                    elif rule['style'] == 'sparse' and beat_pos == 0 and random.random() < rule['Stopa']: percussion_track['Stopa'][step] = 1
                
                # GENEROWANIE WERBLA (Zależne od warstwy Mid/Lead - unika kolizji)
                if rule['Werbel'] > 0:
                    if beat_pos == 2: # Typowo na "2" i "4"
                        # Sprawdzamy czy w oryginalnym leadzie jest duża energia w tym momencie
                        mid_energy = self.get_local_energy(spectral_map['mid'], segment['start_frame'], segment['end_frame'], step, start_step, end_step, sr)
                        # Akcentujemy werbel tam, gdzie lead gra ciszej (uzupełnianie)
                        if mid_energy < 0.5 or random.random() < rule['Werbel']:
                            percussion_track['Werbel'][step] = 1

                # GENEROWANIE TALERZA
                if rule['Talerz'] > 0 and random.random() < rule['Talerz']:
                    if rule['style'] == 'dense': percussion_track['Talerz'][step] = 1
                    elif rule['style'] in ['groove', 'sparse'] and step % 2 == 0: percussion_track['Talerz'][step] = 1

                # GENEROWANIE TOMTOMÓW (Tylko w chorus lub jako fill)
                if rule['TomTom'] > 0:
                    if tag == 'chorus' and beat_pos == 3 and random.random() < rule['TomTom']: percussion_track['TomTom'][step] = 1
                    if tag == 'break' and step % 2 == 0: percussion_track['TomTom'][step] = 1 # Errotyczne przejście

        return percussion_track

    def get_local_energy(self, y_segment, seg_start_f, seg_end_f, current_step, start_step, end_step, sr):
        """
        Pomocnicza funkcja zwracająca względną energię w konkretnym momencie czasu.
        Zapobiega generowaniu perkusji w miejscach, gdzie oryginał ma już za dużo dźwięku.
        """
        if start_step == end_step: return 0.5
        progress = (current_step - start_step) / (end_step - start_step)
        start_f = int(seg_start_f + progress * (seg_end_f - seg_start_f))
        end_f = min(start_f + int(sr * 0.05), seg_end_f, len(y_segment)) # Okno 50ms
        
        if start_f >= end_f or end_f > len(y_segment): return 0.5
        
        chunk = y_segment[start_f:end_f]
        if len(chunk) == 0: return 0.0
        return np.sqrt(np.mean(chunk**2)) # RMS

    def synthesize_percussion_audio(self, percussion_track, sr, tempo):
        """Optymalizowana synteza audio z sampli"""
        total_length = len(percussion_track['Stopa'])
        step_duration_samples = int(sr * 60.0 / tempo / 4) # 16th note
        
        audio = np.zeros(total_length * step_duration_samples, dtype=np.float32)

        for inst in self.instruments:
            if inst not in self.samples: continue
            
            trigger_steps = np.where(np.array(percussion_track[inst]) == 1)[0]
            if len(trigger_steps) == 0: continue

    def create_sample_manipulation_area(self):
        sample_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(10 * self.scale_factor))
        sample_box.set_hexpand(True)
        self.main_box.pack_start(sample_box, False, False, int(10 * self.scale_factor))

        self.nominal_adsr = {
            'Talerz': {'attack': 0.01, 'decay': 0.1, 'sustain': 0.8, 'release': 0.6},
            'Stopa': {'attack': 0.01, 'decay': 0.2, 'sustain': 0.3, 'release': 0.1},
            'Werbel': {'attack': 0.02, 'decay': 0.2, 'sustain': 0.4, 'release': 0.3},
            'TomTom': {'attack': 0.03, 'decay': 0.3, 'sustain': 0.5, 'release': 0.4}
        }
        self.current_adsr = {inst: self.nominal_adsr[inst].copy() for inst in self.instruments}
        self.preview_active = {inst: False for inst in self.instruments}

        self.adsr_entries = {}
        for inst in self.instruments:
            inst_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
            inst_label = Gtk.Label(label=inst)
            inst_box.pack_start(inst_label, False, False, 0)

            adsr_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            self.adsr_entries[inst] = {}
            for param in ['attack', 'decay', 'sustain', 'release']:
                param_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(2 * self.scale_factor))
                minus_btn = Gtk.Button(label="-")
                minus_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
                minus_btn.connect("clicked", self.adjust_adsr, inst, param, -0.1)
                param_box.pack_start(minus_btn, False, False, 0)

                entry = Gtk.Entry()
                entry.set_width_chars(int(4 * self.scale_factor))
                entry.set_text(f"{self.current_adsr[inst][param]:.2f}")
                entry.connect("changed", self.on_adsr_entry_changed, inst, param)
                param_box.pack_start(entry, False, False, 0)
                self.adsr_entries[inst][param] = entry

                plus_btn = Gtk.Button(label="+")
                plus_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
                plus_btn.connect("clicked", self.adjust_adsr, inst, param, 0.1)
                param_box.pack_start(plus_btn, False, False, 0)

                adsr_box.pack_start(param_box, False, False, 0)

            inst_box.pack_start(adsr_box, False, False, 0)

            btn_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            reset_btn = Gtk.Button(label="R")
            reset_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            reset_btn.connect("clicked", self.reset_adsr, inst)
            btn_box.pack_start(reset_btn, False, False, 0)

            rand_btn = Gtk.Button(label="?")
            rand_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            rand_btn.connect("clicked", self.randomize_adsr, inst)
            btn_box.pack_start(rand_btn, False, False, 0)

            preview_check = Gtk.CheckButton()
            preview_check.connect("toggled", self.toggle_preview, inst)
            btn_box.pack_start(preview_check, False, False, 0)
            inst_box.pack_start(btn_box, False, False, 0)

            sample_box.pack_start(inst_box, False, False, 0)

        bank_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        bank_label = Gtk.Label(label="Bank:")
        bank_box.pack_start(bank_label, False, False, 0)

        self.bank_combo = Gtk.ComboBoxText()
        self.bank_combo.append_text("Default")
        self.bank_combo.set_active(0)
        bank_box.pack_start(self.bank_combo, False, False, 0)

        load_btn = Gtk.Button(label="L")
        load_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
        load_btn.connect("clicked", self.load_sample_bank)
        bank_box.pack_start(load_btn, False, False, 0)

        export_btn = Gtk.Button(label="E")
        export_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
        export_btn.connect("clicked", self.export_sample_bank)
        bank_box.pack_start(export_btn, False, False, 0)

        sample_box.pack_end(bank_box, False, False, 0)

        if not self.samples:
            self.generate_default_samples()

    def scale_interface(self, widget, allocation):
        width, height = allocation.width, allocation.height
        self.scale_factor = min(width / 1280, height / 720)

        button_size = int(30 * self.scale_factor)
        for row in self.buttons.values():
            for button in row:
                button.set_size_request(button_size, button_size)

        self.grid.set_row_spacing(int(6 * self.scale_factor))
        self.grid.set_column_spacing(int(6 * self.scale_factor))
        self.main_box.set_spacing(int(6 * self.scale_factor))

        if hasattr(self, 'adsr_entries'):
            for inst in self.instruments:
                for param, entry in self.adsr_entries[inst].items():
                    entry.set_width_chars(int(4 * self.scale_factor))
                for child in self.main_box.get_children()[-1].get_children():
                    if isinstance(child, Gtk.Box):
                        for subchild in child.get_children():
                            if isinstance(subchild, Gtk.Button):
                                subchild.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))

    # Event Handlers and Helper Methods
    def on_button_toggled(self, button, instrument, step):
        if self.advanced_sequencer_mode:
            is_active = button.get_active()
            step_data = self.patterns[instrument][step]
            step_data['active'] = is_active
            if is_active and step_data['rhythm_type'] == 'single':
                step_data['rhythm_type'] = 'single'
            self.update_button_visual(button, instrument, step)
        else:
            self.patterns[instrument][step] = int(button.get_active())

    def update_buttons(self):
        pattern_length = int(self.length_spinbutton.get_value())
        for inst in self.instruments:
            if self.advanced_sequencer_mode:
                if len(self.patterns[inst]) < pattern_length:
                    self.patterns[inst].extend([{'active': False, 'rhythm_type': 'single'} for _ in range(pattern_length - len(self.patterns[inst]))])
                elif len(self.patterns[inst]) > pattern_length:
                    self.patterns[inst] = self.patterns[inst][:pattern_length]
            else:
                if len(self.patterns[inst]) < pattern_length:
                    self.patterns[inst].extend([0] * (pattern_length - len(self.patterns[inst])))
                elif len(self.patterns[inst]) > pattern_length:
                    self.patterns[inst] = self.patterns[inst][:pattern_length]
    
        for inst in self.instruments:
            for i in range(pattern_length):
                try:
                    button = self.buttons[inst][i]
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[inst][i]
                        button.set_active(step_data['active'])
                        self.update_button_visual(button, inst, i)
                    else:
                        button.set_active(bool(self.patterns[inst][i]))
                        button.set_label("")
                except IndexError:
                    self.reinitialize_buttons()
                    return
        self.grid.queue_draw()

    def update_button_visual(self, button, instrument, step):
        if self.advanced_sequencer_mode:
            step_data = self.patterns[instrument][step]
            if step_data['active']:
                button.set_label(step_data['rhythm_type'].capitalize())
            else:
                button.set_label("")
        else:
            button.set_label("")

    def reinitialize_buttons(self):
        pattern_length = int(self.length_spinbutton.get_value())
        for inst in self.instruments:
            self.buttons[inst] = []
            for i in range(pattern_length):
                button = Gtk.ToggleButton()
                button.set_size_request(30, 30)
                context = button.get_style_context()
                context.add_class(f"circle-{self.colors[self.instruments.index(inst)]}")
                button.add_events(Gdk.EventMask.SCROLL_MASK | Gdk.EventMask.BUTTON_PRESS_MASK)
                button.connect("toggled", self.on_button_toggled, inst, i)
                button.connect("scroll-event", self.on_scroll, inst, i)
                button.connect("button-press-event", self.on_button_press, inst, i)
                self.grid.attach(button, i + 1, self.instruments.index(inst) + 1, 1, 1)
                self.buttons[inst].append(button)
        self.grid.show_all()
        self.update_buttons()

    def on_button_press(self, widget, event, instrument, step):
        self.last_button_pressed = event.button

    def on_scroll(self, widget, event, instrument, step):
        if not self.advanced_sequencer_mode or not self.patterns[instrument][step]['active']:
            return
        scroll_direction = event.direction
        step_data = self.patterns[instrument][step]
        rhythm_types = list(self.rhythm_types.keys())
        current_idx = rhythm_types.index(step_data['rhythm_type'])
        
        if scroll_direction == Gdk.ScrollDirection.UP:
            new_idx = (current_idx + 1) % len(rhythm_types)
        else:
            new_idx = (current_idx - 1) % len(rhythm_types)
        
        step_data['rhythm_type'] = rhythm_types[new_idx]
        self.update_button_visual(widget, instrument, step)

    def on_sequencer_mode_switch(self, switch, gparam):
        self.advanced_sequencer_mode = switch.get_active()
        self.patterns = self.advanced_patterns if self.advanced_sequencer_mode else self.simple_patterns
        self.update_buttons()

    def on_performer_mode_switch(self, switch, gparam):
        self.performer_mode = switch.get_active()
        self.update_buttons()

    def bpm_step_up(self, widget):
        self.absolute_bpm = min(300, self.absolute_bpm + 5)
        self.bpm_entry.set_text(str(self.absolute_bpm))
        self.update_dynamic_bpm()

    def bpm_step_down(self, widget):
        self.absolute_bpm = max(60, self.absolute_bpm - 5)
        self.bpm_entry.set_text(str(self.absolute_bpm))
        self.update_dynamic_bpm()

    def calculate_pattern_density(self):
        total_active_steps = 0
        total_steps = len(self.instruments) * len(self.patterns[self.instruments[0]])
        if self.advanced_sequencer_mode:
            for inst in self.instruments:
                for step in self.patterns[inst]:
                    if step['active']:
                        total_active_steps += self.rhythm_types[step['rhythm_type']]['notes']
        else:
            for inst in self.instruments:
                total_active_steps += sum(self.patterns[inst])
        return total_active_steps / total_steps if total_steps > 0 else 0

    def matched_bpm(self, widget):
        density = self.calculate_pattern_density()
        new_bpm = self.base_bpm + (density - 0.5) * 80
        self.absolute_bpm = int(new_bpm)
        self.bpm_entry.set_text(str(self.absolute_bpm))

    def perfect_tempo_bpm(self, widget):
        self.matched_bpm(widget)
        genre = self.custom_genre_entry.get_text()
        avg_bpm = self.genre_bpm.get(genre, self.base_bpm)
        self.absolute_bpm = int((self.absolute_bpm + avg_bpm) / 2)
        self.bpm_entry.set_text(str(self.absolute_bpm))

    def apply_dynamic_bpm(self, widget):
        bpm_string = self.dynamic_bpm_entry.get_text()
        try:
            percentages = [float(bpm.strip()) for bpm in bpm_string.split(',')]
            self.dynamic_bpm_list = [self.absolute_bpm * (p / 100) for p in percentages]
            self.current_bpm_index = 0
        except ValueError:
            print("Invalid BPM input.")

    def update_dynamic_bpm(self):
        if self.dynamic_bpm_list:
            percentages = [float(bpm.strip()) for bpm in self.dynamic_bpm_entry.get_text().split(',')]
            self.dynamic_bpm_list = [self.absolute_bpm * (p / 100) for p in percentages]

    def get_next_bpm(self):
        if not self.dynamic_bpm_list:
            return self.absolute_bpm
        current_bpm = self.dynamic_bpm_list[self.current_bpm_index]
        return current_bpm

    def advance_bpm(self):
        if self.dynamic_bpm_list:
            self.current_bpm_index = (self.current_bpm_index + 1) % len(self.dynamic_bpm_list)

    def generate_custom_pattern(self, widget):
        """Generuje wzorzec na podstawie parametrów: type, rhythm, complexity, intensity."""
        pattern_type  = self.pattern_type_combo.get_active_text()   # intro/verse/…
        rhythm_style  = self.rhythm_style_combo.get_active_text()    # steady/syncopated/…
        complexity    = self.complexity_combo.get_active_text()       # low/medium/high
        intensity     = self.intensity_spin.get_value()               # 0.0–1.0
        repeats       = int(self.occurrences_spin.get_value())        # 1–16
        pattern_length = int(self.length_spinbutton.get_value())

        new_pat = self._build_parametric_pattern(
            pattern_type, rhythm_style, complexity, intensity, pattern_length
        )

        # Zapisz wygenerowany wzorzec
        if self.advanced_sequencer_mode:
            for inst in self.instruments:
                self.advanced_patterns[inst] = new_pat[inst]
            self.patterns = self.advanced_patterns
        else:
            for inst in self.instruments:
                self.simple_patterns[inst] = [
                    1 if new_pat[inst][i]['active'] else 0
                    for i in range(pattern_length)
                ]
            self.patterns = self.simple_patterns

        self.update_buttons()
        print(f"[Custom] type={pattern_type} rhythm={rhythm_style} "
              f"complexity={complexity} intensity={intensity:.1f} repeat={repeats}")

    def _build_parametric_pattern(self, pattern_type, rhythm_style, complexity,
                                   intensity, pattern_length):
        """
        Buduje wzorzec perkusyjny wg parametrów.
        Zwraca dict {inst: [{'active':bool, 'rhythm_type':str}, ...]}
        """
        pat = {inst: [{'active': False, 'rhythm_type': 'single'}
                      for _ in range(pattern_length)]
               for inst in self.instruments}

        # Mapa złożoności → prawdopodobieństwo aktywacji poszczególnych instrumentów
        complexity_map = {
            'low':    {'Stopa': 0.50, 'Werbel': 0.25, 'Talerz': 0.15, 'TomTom': 0.05},
            'medium': {'Stopa': 0.70, 'Werbel': 0.45, 'Talerz': 0.35, 'TomTom': 0.20},
            'high':   {'Stopa': 0.90, 'Werbel': 0.65, 'Talerz': 0.55, 'TomTom': 0.40},
        }
        probs = complexity_map.get(complexity, complexity_map['medium'])

        # Mapa sekcji → modyfikator gęstości i domyślny rhythm_type
        section_map = {
            'intro':   {'density': 0.40, 'rt': {'Stopa': 'single',  'Werbel': 'single', 'Talerz': 'single', 'TomTom': 'single'}},
            'verse':   {'density': 0.70, 'rt': {'Stopa': 'single',  'Werbel': 'swing',  'Talerz': 'double', 'TomTom': 'single'}},
            'chorus':  {'density': 1.00, 'rt': {'Stopa': 'double',  'Werbel': 'swing',  'Talerz': 'burst',  'TomTom': 'accent'}},
            'bridge':  {'density': 0.55, 'rt': {'Stopa': 'single',  'Werbel': 'single', 'Talerz': 'swing',  'TomTom': 'double'}},
            'break':   {'density': 0.30, 'rt': {'Stopa': 'single',  'Werbel': 'single', 'Talerz': 'single', 'TomTom': 'single'}},
            'drop':    {'density': 1.00, 'rt': {'Stopa': 'burst',   'Werbel': 'accent', 'Talerz': 'burst',  'TomTom': 'accent'}},
            'fill':    {'density': 0.80, 'rt': {'Stopa': 'double',  'Werbel': 'burst',  'Talerz': 'double', 'TomTom': 'accent'}},
            'outro':   {'density': 0.35, 'rt': {'Stopa': 'single',  'Werbel': 'single', 'Talerz': 'single', 'TomTom': 'single'}},
        }
        section_cfg = section_map.get(pattern_type, section_map['verse'])
        density     = section_cfg['density']
        rt_map      = section_cfg['rt']

        # Mapa stylu rytmu → funkcja decydująca o aktywacji kroku
        def should_activate(inst, step, p):
            if rhythm_style == 'steady':
                # silne bity
                if inst == 'Stopa'  and step % 4 == 0: return random.random() < p
                if inst == 'Werbel' and step % 4 == 2: return random.random() < p
                if inst == 'Talerz' and step % 2 == 0: return random.random() < p * 0.6
                if inst == 'TomTom' and step % 8 == 7: return random.random() < p * 0.4
            elif rhythm_style == 'syncopated':
                # przesunięcia off-beat
                if inst == 'Stopa'  and step % 4 in [0, 3]: return random.random() < p
                if inst == 'Werbel' and step % 4 in [1, 3]: return random.random() < p
                if inst == 'Talerz': return random.random() < p * intensity * 0.7
                if inst == 'TomTom' and step % 6 == 4:      return random.random() < p * 0.5
            elif rhythm_style == 'sparse':
                threshold = p * intensity * density * 0.4
                return random.random() < threshold
            elif rhythm_style == 'dense':
                threshold = p * intensity * density * 1.3
                return random.random() < min(0.95, threshold)
            elif rhythm_style == 'triplet':
                # rytm triolowy co 3 kroki
                if step % 3 == 0: return random.random() < p * intensity
            return random.random() < p * intensity * density

        for inst in self.instruments:
            p = probs[inst]
            for step in range(pattern_length):
                if should_activate(inst, step, p):
                    pat[inst][step]['active'] = True
                    pat[inst][step]['rhythm_type'] = rt_map[inst]

        return pat

    def on_pattern_length_changed(self, spinbutton):
        new_length = int(spinbutton.get_value())
        current_length = len(self.patterns[self.instruments[0]])

        for instrument in self.instruments:
            if new_length > current_length:
                if self.advanced_sequencer_mode:
                    self.patterns[instrument].extend([{'active': False, 'rhythm_type': 'single'} for _ in range(new_length - current_length)])
                else:
                    self.patterns[instrument].extend([0] * (new_length - current_length))
                for i in range(current_length, new_length):
                    button = Gtk.ToggleButton()
                    button.set_size_request(30, 30)
                    context = button.get_style_context()
                    context.add_class(f"circle-{self.colors[self.instruments.index(instrument)]}")
                    button.connect("toggled", self.on_button_toggled, instrument, i)
                    button.connect("scroll-event", self.on_scroll, instrument, i)
                    button.connect("button-press-event", self.on_button_press, instrument, i)
                    self.grid.attach(button, i + 1, self.instruments.index(instrument) + 1, 1, 1)
                    self.buttons[instrument].append(button)
            elif new_length < current_length:
                self.patterns[instrument] = self.patterns[instrument][:new_length]
                for button in self.buttons[instrument][new_length:]:
                    self.grid.remove(button)
                self.buttons[instrument] = self.buttons[instrument][:new_length]

        for i in range(new_length):
            label = self.grid.get_child_at(i + 1, 0)
            if label is None:
                label = Gtk.Label(label=str(i + 1))
                self.grid.attach(label, i + 1, 0, 1, 1)
            else:
                label.set_visible(True)

        for i in range(new_length, 32):
            label = self.grid.get_child_at(i + 1, 0)
            if label:
                label.set_visible(False)

        self.grid.show_all()

    def randomize_instruments(self, widget):
        probability = self.randomize_probability_spin.get_value() / 100
        pattern_length = int(self.length_spinbutton.get_value())

        for step in range(pattern_length):
            if random.random() < probability:
                inst1, inst2 = random.sample(self.instruments, 2)
                self.patterns[inst1][step], self.patterns[inst2][step] = self.patterns[inst2][step], self.patterns[inst1][step]

        self.update_buttons()

    def autofill_pattern(self):
        pattern_length = int(self.length_spinbutton.get_value())
        genre = self.custom_genre_entry.get_text() or self.preset_genre_combo.get_active_text() or "Generic"
        rhythm_styles = {
            "Techno": {'Stopa': ['single'], 'Werbel': ['swing'], 'Talerz': ['burst'], 'TomTom': ['accent']},
            "House": {'Stopa': ['double'], 'Werbel': ['single'], 'Talerz': ['swing'], 'TomTom': ['single']}
        }
        rules = rhythm_styles.get(genre, {'Stopa': ['single'], 'Werbel': ['single'], 'Talerz': ['single'], 'TomTom': ['single']})
    
        for instrument in self.instruments:
            if self.advanced_sequencer_mode:
                active_steps = [i for i, step in enumerate(self.patterns[instrument]) if step['active']]
                for i in range(pattern_length):
                    if i not in active_steps and random.random() < 0.3:
                        self.patterns[instrument][i]['active'] = True
                        self.patterns[instrument][i]['rhythm_type'] = random.choice(rules[instrument])
            else:
                active_steps = [i for i, step in enumerate(self.patterns[instrument]) if step == 1]
                for i in range(pattern_length):
                    if i not in active_steps and random.random() < 0.3:
                        self.patterns[instrument][i] = 1
    
        self.update_buttons()

    def apply_preset(self, widget):
        preset = self.preset_combo.get_active_text()
        if preset == "Basic Techno":
            self.generate_basic_techno()
        elif preset == "Minimal Techno":
            self.generate_minimal_techno()
        elif preset == "Hard Techno":
            self.generate_hard_techno()
        self.update_buttons()

    def generate_basic_techno(self):
        pattern_length = int(self.length_spinbutton.get_value())
        for i in range(pattern_length):
            if self.advanced_sequencer_mode:
                self.patterns['Stopa'][i]['active'] = True if i % 4 == 0 else False
                self.patterns['Stopa'][i]['rhythm_type'] = 'single'
                self.patterns['Werbel'][i]['active'] = True if i % 8 == 4 else False
                self.patterns['Werbel'][i]['rhythm_type'] = 'swing'
                self.patterns['Talerz'][i]['active'] = True if i % 4 == 2 else False
                self.patterns['Talerz'][i]['rhythm_type'] = 'burst'
                self.patterns['TomTom'][i]['active'] = True if i % 16 == 14 else False
                self.patterns['TomTom'][i]['rhythm_type'] = 'accent'
            else:
                self.patterns['Stopa'][i] = 1 if i % 4 == 0 else 0
                self.patterns['Werbel'][i] = 1 if i % 8 == 4 else 0
                self.patterns['Talerz'][i] = 1 if i % 4 == 2 else 0
                self.patterns['TomTom'][i] = 1 if i % 16 == 14 else 0

    def generate_minimal_techno(self):
        pattern_length = int(self.length_spinbutton.get_value())
        for i in range(pattern_length):
            if self.advanced_sequencer_mode:
                self.patterns['Stopa'][i]['active'] = True if i % 4 == 0 or i % 16 == 14 else False
                self.patterns['Stopa'][i]['rhythm_type'] = 'single'
                self.patterns['Werbel'][i]['active'] = True if i % 8 == 4 else False
                self.patterns['Werbel'][i]['rhythm_type'] = 'swing'
                self.patterns['Talerz'][i]['active'] = True if i % 2 == 0 else False
                self.patterns['Talerz'][i]['rhythm_type'] = 'double'
                self.patterns['TomTom'][i]['active'] = True if i % 16 == 10 else False
                self.patterns['TomTom'][i]['rhythm_type'] = 'accent'
            else:
                self.patterns['Stopa'][i] = 1 if i % 4 == 0 or i % 16 == 14 else 0
                self.patterns['Werbel'][i] = 1 if i % 8 == 4 else 0
                self.patterns['Talerz'][i] = 1 if i % 2 == 0 else 0
                self.patterns['TomTom'][i] = 1 if i % 16 == 10 else 0

    def generate_hard_techno(self):
        pattern_length = int(self.length_spinbutton.get_value())
        for i in range(pattern_length):
            if self.advanced_sequencer_mode:
                self.patterns['Stopa'][i]['active'] = True if i % 2 == 0 else False
                self.patterns['Stopa'][i]['rhythm_type'] = 'burst'
                self.patterns['Werbel'][i]['active'] = True if i % 8 == 4 or i % 8 == 6 else False
                self.patterns['Werbel'][i]['rhythm_type'] = 'swing'
                self.patterns['Talerz'][i]['active'] = True if i % 4 == 0 else False
                self.patterns['Talerz'][i]['rhythm_type'] = 'double'
                self.patterns['TomTom'][i]['active'] = True if i % 8 == 7 else False
                self.patterns['TomTom'][i]['rhythm_type'] = 'accent'
            else:
                self.patterns['Stopa'][i] = 1 if i % 2 == 0 else 0
                self.patterns['Werbel'][i] = 1 if i % 8 == 4 or i % 8 == 6 else 0
                self.patterns['Talerz'][i] = 1 if i % 4 == 0 else 0
                self.patterns['TomTom'][i] = 1 if i % 8 == 7 else 0

    def on_effect_changed(self, slider, instrument, effect):
        value = slider.get_value()
        self.effects[instrument][effect] = value
        
        # Wysyłaj MIDI CC przy zmianie efektu
        # Konwertuj wartość z zakresu -5 do 5 na 0 do 100
        midi_value = (value + 5) * 10  # -5→0, 0→50, 5→100
        self.send_midi_cc(instrument, effect, midi_value)

    def reset_effect(self, button, slider, instrument, effect):
        slider.set_value(0)
        self.effects[instrument][effect] = 0
        
        # Wysyłaj MIDI CC przy resecie
        self.send_midi_cc(instrument, effect, 50)  # 50 = środek (0 w zakresie -5 do 5)

    def reset_all_effects(self, widget):
        for instrument in self.instruments:
            for effect in self.effects[instrument]:
                self.effects[instrument][effect] = 0
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(0)
                
                # Wysyłaj MIDI CC przy resecie wszystkich
                self.send_midi_cc(instrument, effect, 50)

    def reset_genre_fx(self, widget):
        for instrument in self.instruments:
            for effect in self.effects[instrument]:
                self.effects[instrument][effect] = 0
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(0)
                
                # Wysyłaj MIDI CC przy resecie gatunku
                self.send_midi_cc(instrument, effect, 50)
        
        # Resetuj status genre
        if hasattr(self, 'genre_status_label'):
            self.genre_status_label.set_markup("<span color='gray'>Brak FX</span>")
        
        print("🔄 Genre FX zresetowane - wszystkie efekty na 0")

    def apply_effects(self, sound, instrument):
        sound = self.apply_adsr_to_sound(sound, instrument)
        effects = self.effects[instrument]
        sound_array = pygame.sndarray.array(sound)
        sample_width = sound_array.dtype.itemsize
        channels = 1 if sound_array.ndim == 1 else 2

        audio_segment = AudioSegment(
            sound_array.tobytes(),
            frame_rate=44100,
            sample_width=sample_width,
            channels=channels
        )

        if effects['volume'] != 0:
            audio_segment = audio_segment + (effects['volume'] * 10)

        if effects['pitch'] != 0:
            new_rate = int(audio_segment.frame_rate * (2 ** (effects['pitch'] / 12)))
            audio_segment = audio_segment._spawn(audio_segment.raw_data, overrides={'frame_rate': new_rate})
            audio_segment = audio_segment.set_frame_rate(44100)

        if effects['echo'] > 0:
            delay_ms = int(200 * effects['echo'])
            echo_segment = audio_segment - 10
            audio_segment = audio_segment.overlay(echo_segment, position=delay_ms)

        if effects['reverb'] > 0:
            reverb_amount = effects['reverb'] * 300
            audio_segment = audio_segment.fade_in(50).fade_out(int(reverb_amount))

        if effects['pan'] != 0:
            audio_segment = audio_segment.pan(effects['pan'])

        audio_segment = normalize(audio_segment)

        samples = np.array(audio_segment.get_array_of_samples())
        if channels == 2:
            samples = samples.reshape((-1, 2))

        return pygame.sndarray.make_sound(samples)

    def apply_adsr_to_sound(self, sound, instrument):
        sound_array = pygame.sndarray.array(sound)
        sample_rate = 44100
        total_samples = len(sound_array)
        adsr = self.current_adsr[instrument]
        is_stereo = sound_array.ndim == 2
    
        if is_stereo:
            channels = sound_array.shape[1]
        else:
            channels = 1
            sound_array = sound_array.reshape(-1, 1)
    
        attack_samples = int(adsr['attack'] * sample_rate)
        decay_samples = int(adsr['decay'] * sample_rate)
        release_samples = int(adsr['release'] * sample_rate)
        sustain_samples = total_samples - attack_samples - decay_samples - release_samples
    
        if sustain_samples < 0:
            excess = -sustain_samples
            total_adsr = attack_samples + decay_samples + release_samples
            scale_factor = (total_samples - excess) / total_adsr
            attack_samples = int(attack_samples * scale_factor)
            decay_samples = int(decay_samples * scale_factor)
            release_samples = int(release_samples * scale_factor)
            sustain_samples = total_samples - attack_samples - decay_samples - release_samples
    
        envelope = np.zeros(total_samples, dtype=np.float32)
        if attack_samples > 0:
            envelope[:attack_samples] = np.linspace(0, 1, min(attack_samples, total_samples))
        if decay_samples > 0 and attack_samples < total_samples:
            decay_end = min(attack_samples + decay_samples, total_samples)
            envelope[attack_samples:decay_end] = np.linspace(1, adsr['sustain'], decay_end - attack_samples)
        if sustain_samples > 0 and attack_samples + decay_samples < total_samples:
            sustain_end = min(attack_samples + decay_samples + sustain_samples, total_samples)
            envelope[attack_samples + decay_samples:sustain_end] = adsr['sustain']
        if release_samples > 0 and total_samples - release_samples > 0:
            release_start = max(0, total_samples - release_samples)
            envelope[release_start:] = np.linspace(adsr['sustain'], 0, total_samples - release_start)
    
        if is_stereo:
            sound_array[:, 0] = sound_array[:, 0] * envelope
            sound_array[:, 1] = sound_array[:, 1] * envelope
        else:
            sound_array[:, 0] = sound_array[:, 0] * envelope
            sound_array = np.hstack((sound_array, sound_array))
    
        return pygame.sndarray.make_sound(sound_array.astype(np.int16))

    def apply_auto_fx_for_style(self, style):
        fx_settings = {
            "Techno": {'volume': 0.5, 'pitch': 0.2, 'echo': 1.0, 'reverb': 1.2, 'pan': 0.0},
            "House": {'volume': 0.3, 'pitch': 0.0, 'echo': 0.5, 'reverb': 1.0, 'pan': 0.2},
            "Drum and Bass": {'volume': 1.0, 'pitch': -0.5, 'echo': 0.8, 'reverb': 0.7, 'pan': -0.1},
            "Ambient": {'volume': -0.5, 'pitch': 0.0, 'echo': 1.0, 'reverb': 1.5, 'pan': 0.3},
            "Trap": {'volume': 0.8, 'pitch': -1.0, 'echo': 0.6, 'reverb': 0.5, 'pan': -0.2},
            "Dubstep": {'volume': 1.2, 'pitch': -0.8, 'echo': 1.2, 'reverb': 1.0, 'pan': 0.1},
            "Jazz": {'volume': 0.4, 'pitch': 0.3, 'echo': 0.2, 'reverb': 0.8, 'pan': 0.4},
            "Breakbeat": {'volume': 0.7, 'pitch': 0.1, 'echo': 0.9, 'reverb': 0.6, 'pan': -0.3}
        }
        settings = fx_settings.get(style, {})
        
        if not settings:
            print(f"Brak presetu dla gatunku: {style}")
            return
        
        print(f"\n✨ Zastosowano preset FX dla gatunku: {style}")
        for instrument in self.instruments:
            for effect, value in settings.items():
                self.effects[instrument][effect] = value
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(value)
                    # Wysyłaj MIDI CC przy zastosowaniu genre FX
                    midi_value = (value + 5) * 10
                    self.send_midi_cc(instrument, effect, midi_value)
                print(f"  {instrument} - {effect}: {value}")
        
        # Aktualizuj status genre
        if hasattr(self, 'genre_status_label'):
            self.genre_status_label.set_markup(f"<span color='blue'>✓ {style}</span>")

    def apply_auto_fx_for_selected_style(self, widget):
        selected_style = self.preset_genre_combo.get_active_text()
        if selected_style:
            self.apply_auto_fx_for_style(selected_style)
            print(f"✅ Genre FX '{selected_style}' zastosowane - sprawdź suwaki efektów!")

    def apply_groove(self, widget):
        self.groove_type = self.groove_combo.get_active_text()
        self.update_groove_status()
        print(f"🎵 Groove '{self.groove_type}' będzie zastosowany podczas odtwarzania")
        self.play_pattern(widget)

    def reset_groove(self, widget):
        self.groove_type = 'simple'
        self.groove_combo.set_active(0)
        self.update_groove_status()
        print("🔄 Groove zresetowany do 'simple'")

    def apply_groove_effects(self, sound, instrument, step):
        if self.groove_type == "simple":
            return self.apply_simple_groove(sound, instrument, step)
        elif self.groove_type == "stretch":
            return self.apply_stretch_groove(sound, instrument, step)
        elif self.groove_type == "echoes":
            return self.apply_echoes_groove(sound, instrument, step)
        elif self.groove_type == "bouncy":
            return self.apply_bouncy_groove(sound, instrument, step)
        elif self.groove_type == "relax":
            return self.apply_relax_groove(sound, instrument, step)
        return sound

    def apply_simple_groove(self, sound, instrument, step):
        repeat_chance = random.randint(1, 3)
        if repeat_chance == 2:
            sound.play()
        return sound

    def apply_stretch_groove(self, sound, instrument, step):
        stretched_bpm = self.get_next_bpm() * random.uniform(0.9, 1.1)
        self.advance_bpm()
        return sound

    def apply_echoes_groove(self, sound, instrument, step):
        return self.apply_effects_with_echo(sound, instrument)

    def apply_bouncy_groove(self, sound, instrument, step):
        volume_factor = random.choice([0.8, 1.2])
        sound.set_volume(volume_factor)
        return sound

    def apply_relax_groove(self, sound, instrument, step):
        return self.apply_effects_with_echo(sound, instrument)

    def apply_effects_with_echo(self, sound, instrument):
        effect_sound = pygame.mixer.Sound(self.samples[instrument])
        effect_sound.play(maxtime=500)
        return sound

    def advanced_generate_drum_track(self, audio_path, tempo, beat_frames):
        y, sr = librosa.load(audio_path, sr=22050)
        total_duration = librosa.get_duration(y=y, sr=sr)
        
        steps_per_beat = 1
        beats_per_second = tempo / 60
        total_steps = int(float(total_duration) * beats_per_second * steps_per_beat)

        percussion_track = {inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(total_steps)] for inst in self.instruments}

        beat_steps = [int(float(frame) * steps_per_beat * beats_per_second * sr / 22050) for frame in beat_frames]

        for i in range(total_steps):
            if i in beat_steps:
                percussion_track['Stopa'][i]['active'] = True
                percussion_track['Stopa'][i]['rhythm_type'] = 'single'
                percussion_track['Werbel'][i]['active'] = True if i % (steps_per_beat * 4) == steps_per_beat else False
                percussion_track['Werbel'][i]['rhythm_type'] = 'swing'
            if random.random() < 0.3:
                percussion_track['Talerz'][i]['active'] = True
                percussion_track['Talerz'][i]['rhythm_type'] = 'double'
            if i % (steps_per_beat * 2) == steps_per_beat * 1 and random.random() < 0.2:
                percussion_track['TomTom'][i]['active'] = True
                percussion_track['TomTom'][i]['rhythm_type'] = 'accent'

        return percussion_track, y, sr

    def add_drummer_to_audio(self, widget):
        file_dialog = Gtk.FileChooserDialog(title="Select Audio File", parent=self)
        file_dialog.add_buttons(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK)
    
        progress_dialog = Gtk.Dialog(title="Enhancing Percussion", transient_for=self, modal=True)
        progress_dialog.set_default_size(300, 100)
        progress_bar = Gtk.ProgressBar()
        progress_bar.set_show_text(True)
        progress_dialog.get_content_area().pack_start(progress_bar, True, True, 0)
        progress_dialog.show_all()
    
        def update_progress(fraction, message):
            GLib.idle_add(progress_bar.set_fraction, fraction)
            GLib.idle_add(progress_bar.set_text, message)
    
        def enhance_drums_thread(audio_path):
            try:
                update_progress(0.1, "Loading and analyzing audio...")
                y, sr = librosa.load(audio_path, sr=22050)
                tempo, beat_frames = librosa.beat.beat_track(y=y, sr=sr)
    
                update_progress(0.3, "Detecting existing percussion...")
                percussion_events = self.detect_existing_percussion(y, sr, beat_frames)
    
                update_progress(0.5, "Enhancing percussion track...")
                # Przekazujemy audio_path bezpośrednio zamiast polegać na self.current_audio_path
                percussion_track = self.enhance_percussion_track(percussion_events, tempo, len(y) / sr, audio_path, y, sr)
    
                update_progress(0.7, "Synthesizing enhanced audio...")
                percussion_audio = self.synthesize_enhanced_audio(percussion_track, sr, y, tempo)
    
                update_progress(0.9, "Saving tracks...")
                self.save_generated_tracks(audio_path, percussion_track, y, sr, percussion_audio)
    
                GLib.idle_add(progress_dialog.destroy)
                GLib.idle_add(self.show_save_confirmation,
                              audio_path.replace(".mp3", "_enhanced_drums.wav"),
                              audio_path.replace(".mp3", "_combined.wav"))
            except Exception as e:
                GLib.idle_add(progress_dialog.destroy)
                GLib.idle_add(self.show_error_dialog, str(e))
    
        response = file_dialog.run()
        if response == Gtk.ResponseType.OK:
            audio_path = file_dialog.get_filename()
            file_dialog.destroy()
            threading.Thread(target=enhance_drums_thread, args=(audio_path,), daemon=True).start()
        else:
            file_dialog.destroy()
    
    def detect_existing_percussion(self, y, sr, beat_frames):
        """Wykrywa istniejące elementy perkusyjne w audio."""
        onset_env = librosa.onset.onset_strength(y=y, sr=sr)
        onsets = librosa.onset.onset_detect(onset_envelope=onset_env, sr=sr)
        onset_times = librosa.frames_to_time(onsets, sr=sr)
    
        percussion_events = {'Stopa': [], 'Werbel': [], 'Talerz': [], 'TomTom': []}
        for onset_time in onset_times:
            start_sample = int(max(0, onset_time * sr - 0.05 * sr))
            end_sample = int(min(len(y), onset_time * sr + 0.05 * sr))
            segment = y[start_sample:end_sample]
            freqs = np.abs(librosa.stft(segment))
            mean_freq = np.mean(np.argmax(freqs, axis=0))
    
            if mean_freq < 100:
                percussion_events['Stopa'].append(onset_time)
            elif 100 <= mean_freq < 500:
                percussion_events['Werbel'].append(onset_time) if random.random() < 0.7 else percussion_events['TomTom'].append(onset_time)
            else:
                percussion_events['Talerz'].append(onset_time)
    
        return percussion_events
    
    def enhance_percussion_track(self, percussion_events, tempo, total_duration, audio_path, y, sr):
        """Wzbogaca perkusję z wykrywaniem complexity_factor i mniej gęstym rytmem."""
        beats_per_second = tempo / 60
        steps_per_beat = 4
        total_steps = int(total_duration * beats_per_second * steps_per_beat)
        percussion_track = {inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(total_steps)] for inst in self.instruments}
    
        # Mapuj istniejące zdarzenia na kroki
        for inst, times in percussion_events.items():
            for t in times:
                step = int(t * beats_per_second * steps_per_beat)
                if step < total_steps:
                    percussion_track[inst][step]['active'] = True
                    percussion_track[inst][step]['rhythm_type'] = 'single'
    
        # Analiza audio do wykrycia complexity_factor
        if not audio_path or not os.path.exists(audio_path):
            raise ValueError("Brak poprawnej ścieżki audio (audio_path)")
    
        beats_per_measure = 4
        measures = total_steps // (beats_per_measure * steps_per_beat)
        samples_per_measure = int(sr * beats_per_measure / beats_per_second)
    
        rms = librosa.feature.rms(y=y, frame_length=samples_per_measure, hop_length=samples_per_measure)
        onset_env = librosa.onset.onset_strength(y=y, sr=sr, hop_length=samples_per_measure)
        onset_density = [np.sum(onset_env[i:i+1]) for i in range(0, len(onset_env), 1)]
    
        rms_normalized = (rms[0] - np.min(rms)) / (np.max(rms) - np.min(rms) + 1e-6)
        onset_normalized = [(d - min(onset_density)) / (max(onset_density) - min(onset_density) + 1e-6) for d in onset_density]
    
        style = self.preset_genre_combo.get_active_text() or "Techno"
        for measure in range(measures):
            measure_start = measure * beats_per_measure * steps_per_beat
            measure_end = min((measure + 1) * beats_per_measure * steps_per_beat, total_steps)
    
            # Oblicz complexity_factor
            rms_factor = rms_normalized[min(measure, len(rms_normalized) - 1)]
            onset_factor = onset_normalized[min(measure, len(onset_normalized) - 1)]
            complexity_factor = min(0.7, (rms_factor + onset_factor) / 2)
    
            # Stabilna podstawa rytmiczna z większymi odstępami
            for step in range(measure_start, measure_end, steps_per_beat):  # Krok co beat, nie co step
                beat_in_measure = (step % (beats_per_measure * steps_per_beat)) // steps_per_beat
                if beat_in_measure == 0 and not percussion_track['Stopa'][step]['active']:
                    percussion_track['Stopa'][step]['active'] = True
                    percussion_track['Stopa'][step]['rhythm_type'] = 'single'
                if beat_in_measure == 2 and not percussion_track['Werbel'][step]['active'] and random.random() < 0.5 * (1 + complexity_factor):
                    percussion_track['Werbel'][step]['active'] = True
                    percussion_track['Werbel'][step]['rhythm_type'] = 'single'
    
            # Subtelna ewolucja z mniejszą gęstością
            if complexity_factor > 0.3:  # Dodajemy elementy tylko w bardziej intensywnych sekcjach
                for step in range(measure_start, measure_end, steps_per_beat * 2):  # Co 2 beaty
                    offbeat = step % (steps_per_beat * 2) != 0
                    if style == "Techno":
                        if measure % 4 == 0 and random.random() < complexity_factor * 0.08 and not percussion_track['Talerz'][step]['active']:
                            percussion_track['Talerz'][step]['active'] = True
                            percussion_track['Talerz'][step]['rhythm_type'] = 'double'
                        if measure % 8 == 7 and random.random() < complexity_factor * 0.1 and not percussion_track['TomTom'][step]['active']:
                            percussion_track['TomTom'][step]['active'] = True
                            percussion_track['TomTom'][step]['rhythm_type'] = 'accent'
                    elif style == "House":
                        if measure % 4 == 2 and random.random() < complexity_factor * 0.08 and not percussion_track['Talerz'][step]['active']:
                            percussion_track['Talerz'][step]['active'] = True
                            percussion_track['Talerz'][step]['rhythm_type'] = 'swing'
                        if measure % 8 == 4 and random.random() < complexity_factor * 0.05 and not percussion_track['Stopa'][step]['active']:
                            percussion_track['Stopa'][step]['active'] = True
                            percussion_track['Stopa'][step]['rhythm_type'] = 'single'
    
        return percussion_track
    
    def synthesize_enhanced_audio(self, percussion_track, sr, original_audio, tempo):
        """Syntetyzuje perkusję z dłuższym wybrzmieniem i mniejszą gęstością."""
        beats_per_second = tempo / 60
        steps_per_beat = 4
        step_duration = int(sr / (beats_per_second * steps_per_beat))
        total_length = len(percussion_track['Stopa'])
        audio = np.zeros(total_length * step_duration, dtype=np.float32)
    
        for inst in self.instruments:
            for step in range(total_length):
                step_data = percussion_track[inst][step]
                if step_data['active']:
                    rhythm = self.rhythm_types[step_data['rhythm_type']]
                    sample = pygame.mixer.Sound(self.samples[inst])
                    sample_array = pygame.sndarray.array(sample)
                    if sample_array.ndim > 1:
                        sample_array = sample_array.mean(axis=1)
                    
                    # Dłuższe trwanie nuty, minimum połowa beatu
                    note_duration = max(int(step_duration * 2 * rhythm['speed'] / rhythm['notes']), int(sr / beats_per_second / 2))
                    for i in range(rhythm['notes']):
                        start = int(step * step_duration + i * note_duration)
                        end = min(start + note_duration, len(audio))
                        if len(sample_array) > note_duration:
                            sample_array_adj = sample_array[:note_duration]
                        else:
                            sample_array_adj = np.pad(sample_array, (0, note_duration - len(sample_array)))
                        if end <= len(audio):
                            audio[start:end] += sample_array_adj * 0.5
                        else:
                            audio[start:] += sample_array_adj[:len(audio) - start] * 0.5
    
        original_rms = np.sqrt(np.mean(original_audio**2))
        percussion_rms = np.sqrt(np.mean(audio**2))
        if percussion_rms > 0:
            audio *= (original_rms / percussion_rms) * 0.3
    
        return audio
    
    def save_generated_tracks(self, audio_path, percussion_track, original_audio, sr, percussion_audio):
        """Zapisuje wzbogacone ścieżki."""
        max_length = len(original_audio)
        percussion_audio = librosa.util.fix_length(percussion_audio, size=max_length)
        combined_audio = original_audio * 0.4 + percussion_audio * 0.5
        combined_audio = librosa.util.normalize(combined_audio)
    
        percussion_path = audio_path.replace(".mp3", "_enhanced_drums.wav")
        combined_path = audio_path.replace(".mp3", "_combined.wav")
        sf.write(percussion_path, percussion_audio, sr)
        sf.write(combined_path, combined_audio, sr)

    def show_save_confirmation(self, percussion_path, combined_path):
        dialog = Gtk.MessageDialog(
            parent=self,
            flags=Gtk.DialogFlags.MODAL,
            type=Gtk.MessageType.INFO,
            buttons=Gtk.ButtonsType.OK,
            message_format="Tracks successfully saved!"
        )
        dialog.format_secondary_text(f"Percussion Track: {percussion_path}\nCombined Track: {combined_path}")
        dialog.run()
        dialog.destroy()

    def show_error_dialog(self, message):
        dialog = Gtk.MessageDialog(
            parent=self,
            flags=Gtk.DialogFlags.MODAL,
            type=Gtk.MessageType.ERROR,
            buttons=Gtk.ButtonsType.OK,
            message_format="Error occurred!"
        )
        dialog.format_secondary_text(message)
        dialog.run()
        dialog.destroy()

    def load_samples_from_directory(self):
        sample_dir = "sample"
        if not os.path.exists(sample_dir):
            print("Katalog 'sample' nie istnieje. Pomijam automatyczne wczytywanie.")
            return

        for instrument in self.instruments:
            file_path = os.path.join(sample_dir, f"{instrument}.wav")
            if os.path.isfile(file_path):
                self.samples[instrument] = file_path
                print(f"Załadowano sample dla {instrument}: {file_path}")

    def toggle_fullscreen(self, button):
        if self.is_fullscreen:
            self.unfullscreen()
            self.is_fullscreen = False
            button.set_label("Wejdź w pełny ekran")
        else:
            self.fullscreen()
            self.is_fullscreen = True
            button.set_label("Wyjdź z pełnego ekranu")

    def init_audio(self):
        selected_backend = self.backend_combo.get_active_text()
        if selected_backend == "PipeWire":
            pygame.mixer.quit()
            pygame.mixer.init()
        elif selected_backend == "JACK":
            os.environ['SDL_AUDIODRIVER'] = 'jack'
            pygame.mixer.quit()
            pygame.mixer.init()

    def prepare_performance_play(self):
        """Przygotowuje wzorce dla trybu Performer, symulując ograniczenia ludzkiego perkusisty."""
        if not self.performer_mode or not self.advanced_sequencer_mode:
            return self.patterns

        pattern_length = int(self.length_spinbutton.get_value())
        performance_patterns = {
            inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(pattern_length)]
            for inst in self.instruments
        }

        # Priorytety instrumentów: Stopa i Werbel jako podstawa rytmu, potem Talerz i TomTom
        priority_order = ['Stopa', 'Werbel', 'Talerz', 'TomTom']

        for step in range(pattern_length):
            active_instruments = [
                inst for inst in self.instruments if self.patterns[inst][step]['active']
            ]
            
            # Ograniczamy do maksymalnie 4 instrumentów jednocześnie
            if len(active_instruments) > 4:
                active_instruments = active_instruments[:4]
            elif len(active_instruments) == 0:
                continue

            # Przypisanie instrumentów do "rąk" i "nóg"
            hands = 2
            feet = 2
            assigned = []

            # Najpierw przypisujemy Stopę i TomTom do nóg
            for inst in ['Stopa', 'TomTom']:
                if inst in active_instruments and feet > 0:
                    performance_patterns[inst][step] = self.patterns[inst][step].copy()
                    assigned.append(inst)
                    feet -= 1

            # Następnie przypisujemy Werbel i Talerz do rąk
            for inst in ['Werbel', 'Talerz']:
                if inst in active_instruments and inst not in assigned and hands > 0:
                    performance_patterns[inst][step] = self.patterns[inst][step].copy()
                    assigned.append(inst)
                    hands -= 1

            # Jeśli zostały miejsca, przypisujemy pozostałe instrumenty
            for inst in active_instruments:
                if inst not in assigned and (hands > 0 or feet > 0):
                    performance_patterns[inst][step] = self.patterns[inst][step].copy()
                    if hands > 0:
                        hands -= 1
                    else:
                        feet -= 1

        return performance_patterns

    def play_pattern(self, widget):
        self.init_audio()
        if not self.loop_playing:
            self.loop_playing = True
            
            # Wysyłaj aktualne ustawienia efektów jako MIDI CC na start
            if self.midi_enabled:
                for instrument in self.instruments:
                    self.send_all_effects_as_cc(instrument)
            
            self.performance_patterns = self.prepare_performance_play()
            self.play_thread = threading.Thread(target=self.loop_play)
            self.play_thread.start()

    def blink_button(self, instrument, step):
        button = self.buttons[instrument][step]
        context = button.get_style_context()
        context.add_class("blink")
        GLib.timeout_add(500, lambda: context.remove_class("blink"))

    def loop_play(self):
        pattern_length = int(self.length_spinbutton.get_value())
        step_counter = 0
        intensity_tracker = 0

        active_patterns = self.performance_patterns if self.performer_mode and self.advanced_sequencer_mode else self.patterns

        while self.loop_playing:
            current_bpm = self.get_next_bpm()
            base_step_duration = 60 / current_bpm / 4

            for _ in range(self.steps_per_bpm):
                if step_counter >= pattern_length:
                    step_counter = 0
                    intensity_tracker = 0

                start_time = time.time()

                for inst in self.instruments:
                    if self.advanced_sequencer_mode:
                        step_data = active_patterns[inst][step_counter]
                        # Sprawdź czy step_data to słownik (advanced mode) czy int (simple mode)
                        if isinstance(step_data, dict) and step_data.get('active', False):
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            
                            # Odtwarzanie audio (jeśli nie jest wyciszone)
                            if not self.mute_samples and inst in self.samples:
                                original_sound = pygame.mixer.Sound(self.samples[inst])
                                modified_sound = self.apply_effects(original_sound, inst)
                            
                            intensity_tracker += rhythm['notes']
                            note_duration = base_step_duration * rhythm['speed'] / rhythm['notes']
                            
                            for i in range(rhythm['notes']):
                                swing_offset = note_duration * rhythm['swing'] if i % 2 == 1 else 0
                                
                                # Odtwarzanie audio (jeśli nie jest wyciszone)
                                if not self.mute_samples and inst in self.samples:
                                    volume = 1.2 if step_data['rhythm_type'] == 'accent' else 1.0
                                    modified_sound.set_volume(volume)
                                    if self.performer_mode:
                                        human_delay = random.uniform(0, 0.01)
                                        time.sleep(human_delay)
                                    modified_sound.play()
                                
                                # Wysyłanie MIDI OUT (zawsze)
                                midi_velocity = 120 if step_data['rhythm_type'] == 'accent' else 100
                                self.send_midi_note(inst, velocity=midi_velocity, duration_ms=int(note_duration * 1000))
                                
                                time.sleep(note_duration + swing_offset)
                            
                            # TomTom fill (jeśli nie jest wyciszone)
                            if inst != 'TomTom' and intensity_tracker > 3 and step_counter % 4 == 3:
                                if not self.mute_samples and 'TomTom' in self.samples:
                                    tomtom_sound = pygame.mixer.Sound(self.samples['TomTom'])
                                    tomtom_sound.set_volume(1.2)
                                    tomtom_sound.play()
                                
                                # Wysyłanie MIDI dla TomTom (zawsze)
                                self.send_midi_note('TomTom', velocity=110, duration_ms=100)
                                
                                intensity_tracker = 0
                            
                            GLib.idle_add(self.blink_button, inst, step_counter)
                        elif isinstance(step_data, int) and step_data == 1:
                            # Fallback dla prostego trybu gdy advanced_sequencer_mode jest True ale dane są int
                            if not self.mute_samples and inst in self.samples:
                                original_sound = pygame.mixer.Sound(self.samples[inst])
                                modified_sound = self.apply_effects(original_sound, inst)
                                modified_sound = self.apply_groove_effects(modified_sound, inst, step_counter)
                                modified_sound.play()
                            
                            # Wysyłanie MIDI OUT (zawsze)
                            self.send_midi_note(inst, velocity=100, duration_ms=50)
                            
                            GLib.idle_add(self.blink_button, inst, step_counter)
                    else:
                        if active_patterns[inst][step_counter] == 1:
                            # Odtwarzanie audio (jeśli nie jest wyciszone)
                            if not self.mute_samples and inst in self.samples:
                                original_sound = pygame.mixer.Sound(self.samples[inst])
                                modified_sound = self.apply_effects(original_sound, inst)
                                modified_sound = self.apply_groove_effects(modified_sound, inst, step_counter)
                                modified_sound.play()
                            
                            # Wysyłanie MIDI OUT (zawsze)
                            self.send_midi_note(inst, velocity=100, duration_ms=50)
                            
                            GLib.idle_add(self.blink_button, inst, step_counter)

                elapsed_time = time.time() - start_time
                sleep_time = max(0, base_step_duration - elapsed_time)
                time.sleep(sleep_time)

                step_counter += 1
            self.advance_bpm()

    def stop_pattern(self, widget):
        self.loop_playing = False
        if self.play_thread is not None:
            self.play_thread.join()

    def load_samples(self, widget):
        for inst in self.instruments:
            file_dialog = Gtk.FileChooserDialog(
                title=f"Wybierz sample dla {inst}",
                action=Gtk.FileChooserAction.OPEN,
                buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK)
            )
            response = file_dialog.run()
            if response == Gtk.ResponseType.OK:
                filename = file_dialog.get_filename()
                self.samples[inst] = filename
                print(f"Loaded sample for {inst}: {filename}")
            file_dialog.destroy() 
        self.analyze_sample_volume()

    def analyze_sample_volume(self):
        total_volume = 0
        sample_count = 0

        for instrument, sample_path in self.samples.items():
            if sample_path:
                audio = AudioSegment.from_file(sample_path)
                volume = audio.dBFS
                total_volume += volume
                sample_count += 1

        avg_volume = total_volume / sample_count if sample_count > 0 else 0
        return avg_volume

    def autolevel_samples(self, widget):
        avg_volume = self.analyze_sample_volume()
        for instrument in self.effects:
            normalized_volume = max(min((self.effects[instrument]['volume'] - avg_volume) / 16, 5), -5)
            self.effects[instrument]['volume'] = normalized_volume
            if instrument in self.effect_sliders and 'volume' in self.effect_sliders[instrument]:
                self.effect_sliders[instrument]['volume'].set_value(normalized_volume)

    def save_project(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Zapisz Projekt",
            parent=self,
            action=Gtk.FileChooserAction.SAVE
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL,
            Gtk.STOCK_SAVE, Gtk.ResponseType.OK
        )
        dialog.set_current_name("projekt.drsmp")
        response = dialog.run()

        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            project_data = {
                "simple_patterns": self.simple_patterns,
                "advanced_patterns": self.advanced_patterns,
                "advanced_sequencer_mode": self.advanced_sequencer_mode,
                "performer_mode": self.performer_mode,
                "samples": self.samples,
                "absolute_bpm": self.absolute_bpm,
                "dynamic_bpm_list": self.dynamic_bpm_list
            }

            with open(filename, 'w') as f:
                json.dump(project_data, f)

        dialog.destroy()

    def load_project(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Wczytaj Projekt",
            action=Gtk.FileChooserAction.OPEN,
            buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK)
        )
        dialog.set_current_name("projekt.drsmp")
        response = dialog.run()

        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()

            with open(filename, 'r') as f:
                project_data = json.load(f)

            self.simple_patterns = project_data.get("simple_patterns", {inst: [0] * 16 for inst in self.instruments})
            self.advanced_patterns = project_data.get("advanced_patterns", {inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(16)] for inst in self.instruments})
            self.advanced_sequencer_mode = project_data.get("advanced_sequencer_mode", False)
            self.performer_mode = project_data.get("performer_mode", False)
            self.patterns = self.advanced_patterns if self.advanced_sequencer_mode else self.simple_patterns
            self.sequencer_mode_switch.set_active(self.advanced_sequencer_mode)
            self.performer_mode_switch.set_active(self.performer_mode)
            self.samples = project_data["samples"]
            self.absolute_bpm = project_data.get("absolute_bpm", 120)
            self.dynamic_bpm_list = project_data.get("dynamic_bpm_list", [])
            self.bpm_entry.set_text(str(self.absolute_bpm))
            self.dynamic_bpm_entry.set_text(','.join(map(str, [bpm * 100 / self.absolute_bpm for bpm in self.dynamic_bpm_list])))
            self.update_buttons()

        dialog.destroy()

    def export_to_midi(self, widget):
        midi = MIDIFile(1)
        track = 0
        time = 0
        midi.addTrackName(track, time, "Drum Pattern")
        midi.addTempo(track, time, self.absolute_bpm)

        pattern_length = int(self.length_spinbutton.get_value())
        active_patterns = self.prepare_performance_play() if self.performer_mode and self.advanced_sequencer_mode else self.patterns

        for step in range(pattern_length):
            current_bpm = self.get_next_bpm()
            step_duration = 60 / current_bpm / 4

            for inst in self.instruments:
                if self.advanced_sequencer_mode:
                    step_data = active_patterns[inst][step]
                    if step_data['active']:
                        rhythm = self.rhythm_types[step_data['rhythm_type']]
                        note_duration = step_duration * rhythm['speed'] / rhythm['notes']
                        for _ in range(rhythm['notes']):
                            midi.addNote(track, 9, self.midi_notes[inst], time, note_duration, 100 if step_data['rhythm_type'] != 'accent' else 120)
                            time += note_duration
                else:
                    if active_patterns[inst][step] == 1:
                        midi.addNote(track, 9, self.midi_notes[inst], time, 0.25, 100)
            if not self.advanced_sequencer_mode:
                time += step_duration

        file_dialog = Gtk.FileChooserDialog(
            title="Export MIDI",
            action=Gtk.FileChooserAction.SAVE,
            buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK))
        file_dialog.set_current_name("drum_pattern.mid")

        response = file_dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = file_dialog.get_filename()
            with open(filename, "wb") as output_file:
                midi.writeFile(output_file)
        file_dialog.destroy()

    def export_advanced_midi(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export Advanced MIDI",
            parent=self,
            action=Gtk.FileChooserAction.SAVE,
            buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK)
        )
        dialog.set_current_name("unique_track.mid")

        grid = Gtk.Grid()
        dialog.set_extra_widget(grid)

        style_label = Gtk.Label(label="Style:")
        grid.attach(style_label, 0, 0, 1, 1)
        style_combo = Gtk.ComboBoxText()
        styles = ["Techno", "House", "Drum and Bass", "Ambient", "Trap", "Dubstep"]
        for style in styles:
            style_combo.append_text(style)
        style_combo.set_active(0)
        grid.attach(style_combo, 1, 0, 1, 1)

        bpm_label = Gtk.Label(label="Target BPM:")
        grid.attach(bpm_label, 0, 1, 1, 1)
        bpm_entry = Gtk.Entry()
        bpm_entry.set_text(str(self.absolute_bpm))
        grid.attach(bpm_entry, 1, 1, 1, 1)

        dynamic_bpm_label = Gtk.Label(label="Dynamic BPM (%):")
        grid.attach(dynamic_bpm_label, 0, 2, 1, 1)
        dynamic_bpm_entry = Gtk.Entry()
        dynamic_bpm_entry.set_text(self.dynamic_bpm_entry.get_text())
        grid.attach(dynamic_bpm_entry, 1, 2, 1, 1)

        dialog.show_all()
        response = dialog.run()

        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            style = style_combo.get_active_text()
            target_bpm = float(bpm_entry.get_text())
            dynamic_bpm = [float(x) for x in dynamic_bpm_entry.get_text().split(',')]

            midi = MIDIFile(3)
            for i, name in enumerate(["Drums", "Bass", "Lead"]):
                midi.addTrackName(i, 0, name)
            midi.addTempo(0, 0, target_bpm)

            duration = 720
            patterns = self.generate_structured_patterns(style, duration, target_bpm, unique=True)
            self.add_structured_notes(midi, patterns, dynamic_bpm)

            with open(filename, "wb") as output_file:
                midi.writeFile(output_file)

        dialog.destroy()

    def generate_structured_patterns(self, style, duration, bpm, unique=False):
        structure = {
            "intro": random.randint(4, 6) if unique else 4,
            "verse1": random.randint(12, 14) if unique else 14,
            "chorus1": random.randint(6, 8) if unique else 8,
            "verse2": random.randint(12, 14) if unique else 14,
            "chorus2": random.randint(6, 8) if unique else 8,
            "development": random.randint(12, 14) if unique else 12,
            "chorus3": random.randint(6, 8) if unique else 8,
            "outro": random.randint(4, 6) if unique else 4
        }

        total_measures = int(duration * bpm / 60 / 4)
        total_structure_measures = sum(structure.values())
        if total_structure_measures < total_measures:
            structure["outro"] += total_measures - total_structure_measures
        elif total_structure_measures > total_measures:
            structure["outro"] = max(4, structure["outro"] - (total_structure_measures - total_measures))

        patterns = {}
        current_measure = 0

        for section, section_measures in structure.items():
            section_duration = section_measures * 4 * 60 / bpm
            drum_pattern = self.generate_drum_pattern(style, section_duration, bpm)
            bass_pattern = self.generate_bass_pattern(style, section_duration, bpm)
            lead_pattern = self.generate_lead_pattern(style, section_duration, bpm)

            intensity = 0.3 if "intro" in section or "outro" in section else 0.7 if "development" in section else 0.5
            drum_pattern = self.adjust_pattern_intensity(drum_pattern, intensity)
            bass_pattern = self.adjust_pattern_intensity(bass_pattern, intensity)
            lead_pattern = self.adjust_pattern_intensity(lead_pattern, intensity)

            patterns[section] = {
                "drums": drum_pattern,
                "bass": bass_pattern,
                "lead": lead_pattern,
                "start_measure": current_measure,
                "duration": section_measures
            }
            current_measure += section_measures

        return patterns

    def adjust_pattern_intensity(self, pattern, intensity):
        if isinstance(pattern, dict):
            for inst in pattern:
                for step in pattern[inst]:
                    step['active'] = step['active'] and random.random() < intensity
        else:
            pattern = [x if random.random() < intensity else 0 for x in pattern]
        return pattern

    def generate_drum_pattern(self, style, duration, bpm):
        pattern_length = int(duration * bpm / 60 / 4)
        pattern = {inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(pattern_length)] for inst in self.instruments}

        if style == "Techno":
            for i in range(pattern_length):
                pattern['Stopa'][i]['active'] = True if i % 4 == 0 else False
                pattern['Stopa'][i]['rhythm_type'] = 'single'
                pattern['Werbel'][i]['active'] = True if i % 8 == 4 else False
                pattern['Werbel'][i]['rhythm_type'] = 'swing'
                pattern['Talerz'][i]['active'] = True if i % 4 == 2 and random.random() < 0.3 else False
                pattern['Talerz'][i]['rhythm_type'] = 'burst'
                pattern['TomTom'][i]['active'] = True if i % 16 == 14 and random.random() < 0.3 else False
                pattern['TomTom'][i]['rhythm_type'] = 'accent'
        elif style == "House":
            for i in range(pattern_length):
                pattern['Stopa'][i]['active'] = True if i % 4 in [0, 2] else False
                pattern['Stopa'][i]['rhythm_type'] = 'double'
                pattern['Werbel'][i]['active'] = True if i % 8 == 4 else False
                pattern['Werbel'][i]['rhythm_type'] = 'single'
                pattern['Talerz'][i]['active'] = True if i % 8 == 4 and random.random() < 0.25 else False
                pattern['Talerz'][i]['rhythm_type'] = 'swing'
                pattern['TomTom'][i]['active'] = True if i % 16 == 12 else False
                pattern['TomTom'][i]['rhythm_type'] = 'single'
        # Możesz dodać więcej stylów według potrzeb
        return pattern

    def generate_bass_pattern(self, style, duration, bpm):
        pattern_length = int(duration * bpm / 60 / 4)
        pattern = [0] * pattern_length

        if style == "Techno":
            for i in range(pattern_length):
                pattern[i] = random.choice([36, 38, 41, 43]) if i % 4 == 0 else 0
        elif style == "House":
            for i in range(pattern_length):
                pattern[i] = random.choice([36, 38, 41, 43]) if i % 2 == 0 else 0
        # Możesz dodać więcej stylów według potrzeb
        return pattern

    def generate_lead_pattern(self, style, duration, bpm):
        pattern_length = int(duration * bpm / 60 / 4)
        pattern = [0] * pattern_length

        if style == "Techno":
            for i in range(pattern_length):
                pattern[i] = random.choice([60, 62, 64, 65, 67]) if i % 8 in [0, 3, 5] else 0
        elif style == "House":
            for i in range(pattern_length):
                pattern[i] = random.choice([60, 62, 64, 65]) if i % 4 in [0, 2] else 0
        # Możesz dodać więcej stylów według potrzeb
        return pattern

    def add_structured_notes(self, midi, structured_patterns, dynamic_bpm):
        time = 0
        current_bpm_index = 0
        steps_per_bpm = 4

        for section, patterns in structured_patterns.items():
            drum_pattern = patterns['drums']
            bass_pattern = patterns['bass']
            lead_pattern = patterns['lead']
            section_duration = patterns['duration'] * 4

            for step in range(section_duration):
                if step % steps_per_bpm == 0:
                    current_bpm = dynamic_bpm[current_bpm_index] * self.absolute_bpm / 100
                    current_bpm_index = (current_bpm_index + 1) % len(dynamic_bpm)

                step_duration = 60 / current_bpm / 4
                for inst in self.instruments:
                    step_data = drum_pattern[inst][step % len(drum_pattern[inst])]
                    if step_data['active']:
                        rhythm = self.rhythm_types[step_data['rhythm_type']]
                        note_duration = step_duration * rhythm['speed'] / rhythm['notes']
                        for _ in range(rhythm['notes']):
                            midi.addNote(0, 9, self.midi_notes[inst], time, note_duration, 100 if step_data['rhythm_type'] != 'accent' else 120)
                            time += note_duration

                bass_note = bass_pattern[step % len(bass_pattern)]
                if bass_note != 0:
                    midi.addNote(1, 0, bass_note, time, 0.5, 80)

                lead_note = lead_pattern[step % len(lead_pattern)]
                if lead_note != 0:
                    midi.addNote(2, 1, lead_note, time, 0.25, 90)

                time += step_duration

    def randomize_pattern(self, widget):
        pattern_length = int(self.length_spinbutton.get_value())
        for inst in self.instruments:
            if self.advanced_sequencer_mode:
                for i in range(pattern_length):
                    step_data = self.patterns[inst][i]
                    if inst == 'Stopa':
                        step_data['active'] = random.choice([True, False]) if i % 4 == 0 else False
                        step_data['rhythm_type'] = random.choice(['single', 'double']) if step_data['active'] else 'single'
                    elif inst == 'Werbel':
                        step_data['active'] = True if i % 4 == 2 else False
                        step_data['rhythm_type'] = 'swing' if step_data['active'] and random.random() < 0.3 else 'single'
                    elif inst == 'Talerz':
                        step_data['active'] = random.choice([True, False]) if i % 2 == 0 else False
                        step_data['rhythm_type'] = random.choice(['single', 'burst']) if step_data['active'] else 'single'
                    elif inst == 'TomTom':
                        step_data['active'] = True if i % 8 == 7 and random.random() < 0.5 else False
                        step_data['rhythm_type'] = 'accent' if step_data['active'] else 'single'
            else:
                for i in range(pattern_length):
                    if inst == 'Stopa':
                        self.patterns[inst][i] = random.choice([1, 0]) if i % 4 == 0 else 0
                    elif inst == 'Werbel':
                        self.patterns[inst][i] = 1 if i % 4 == 2 else 0
                    elif inst == 'Talerz':
                        self.patterns[inst][i] = random.choice([0, 1]) if i % 2 == 0 else 0
                    elif inst == 'TomTom':
                        self.patterns[inst][i] = random.choice([0, 1]) if i % 8 == 7 else 0
    
        self.randomize_instruments(None)
        self.update_buttons()

    # Sample Manipulation Handlers
    def on_adsr_entry_changed(self, entry, instrument, param):
        try:
            value = float(entry.get_text())
            self.current_adsr[instrument][param] = max(0.0, min(value, 1.0 if param == 'sustain' else 5.0))
            entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")
            if self.preview_active[instrument]:
                self.preview_sample(instrument)
        except ValueError:
            entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")

    def adjust_adsr(self, button, instrument, param, step):
        current_value = self.current_adsr[instrument][param]
        new_value = max(0.0, min(current_value + step, 1.0 if param == 'sustain' else 5.0))
        self.current_adsr[instrument][param] = new_value
        self.adsr_entries[instrument][param].set_text(f"{new_value:.2f}")
        if self.preview_active[instrument]:
            self.preview_sample(instrument)

    def reset_adsr(self, button, instrument):
        self.current_adsr[instrument] = self.nominal_adsr[instrument].copy()
        for param, entry in self.adsr_entries[instrument].items():
            entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")
        if self.preview_active[instrument]:
            self.preview_sample(instrument)

    def randomize_adsr(self, button, instrument):
        for param in ['attack', 'decay', 'sustain', 'release']:
            if param == 'sustain':
                self.current_adsr[instrument][param] = random.uniform(0.1, 1.0)
            else:
                self.current_adsr[instrument][param] = random.uniform(0.01, 2.0)
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        if self.preview_active[instrument]:
            self.preview_sample(instrument)

    def toggle_preview(self, checkbutton, instrument):
        self.preview_active[instrument] = checkbutton.get_active()
        if self.preview_active[instrument]:
            self.preview_sample(instrument)

    def preview_sample(self, instrument):
        if instrument in self.samples:
            sound = pygame.mixer.Sound(self.samples[instrument])
            sound = self.apply_effects(sound, instrument)
            sound.play()

    def generate_default_samples(self):
        sample_rate = 44100
        duration = 0.5
        for inst in self.instruments:
            if inst not in self.samples:
                t = np.linspace(0, duration, int(sample_rate * duration), False)
                if inst == 'Talerz':
                    base = np.sin(2 * np.pi * 2000 * t) * np.exp(-3 * t)
                    noise = np.random.normal(0, 0.3, len(t)) * np.exp(-2 * t)
                    sound = base + noise
                elif inst == 'Stopa':
                    sound = np.sin(2 * np.pi * 60 * t) * np.exp(-10 * t)
                elif inst == 'Werbel':
                    base = np.sin(2 * np.pi * 300 * t) * np.exp(-6 * t)
                    noise = np.random.normal(0, 0.1, len(t)) * np.exp(-4 * t)
                    sound = base * 0.7 + noise * 0.3
                elif inst == 'TomTom':
                    base = np.sin(2 * np.pi * 100 * t) * np.exp(-4 * t)
                    echo = np.sin(2 * np.pi * 100 * t) * np.exp(-6 * t) * 0.4
                    sound = base + np.pad(echo, (int(sample_rate * 0.1), 0))[:len(t)]
                
                sound = (sound / np.max(np.abs(sound)) * 32767).astype(np.int16)
                self.samples[inst] = f"{inst}_default.wav"
                sf.write(self.samples[inst], sound, sample_rate)

    def export_sample_bank(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export Sample Bank",
            action=Gtk.FileChooserAction.SAVE,
            buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK))
        dialog.set_current_name("sample_bank.zip")

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            import zipfile
            filename = dialog.get_filename()
            with zipfile.ZipFile(filename, 'w') as zipf:
                for inst in self.instruments:
                    if inst in self.samples:
                        zipf.write(self.samples[inst], os.path.basename(self.samples[inst]))
                adsr_data = json.dumps(self.current_adsr)
                zipf.writestr("adsr_settings.json", adsr_data)
            self.bank_combo.append_text(os.path.basename(filename).replace(".zip", ""))
        dialog.destroy()

    def load_sample_bank(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Load Sample Bank",
            action=Gtk.FileChooserAction.OPEN,
            buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK))
        response = dialog.run()
    
        if response == Gtk.ResponseType.OK:
            import zipfile
            filename = dialog.get_filename()
            try:
                with zipfile.ZipFile(filename, 'r') as zipf:
                    zipf.extractall("sample_bank_temp")
                    for inst in self.instruments:
                        sample_path = f"sample_bank_temp/{inst}.wav"
                        if os.path.exists(sample_path):
                            self.samples[inst] = sample_path
                    adsr_file = "sample_bank_temp/adsr_settings.json"
                    if os.path.exists(adsr_file):
                        with open(adsr_file, 'r') as f:
                            self.current_adsr = json.load(f)
                        for inst in self.instruments:
                            for param, entry in self.adsr_entries[inst].items():
                                entry.set_text(str(self.current_adsr[inst][param]))
            except Exception as e:
                self.show_error_dialog(f"Error loading bank: {str(e)}")
        dialog.destroy()

# Main execution
if __name__ == "__main__":
    win = DrumSamplerApp()
    
    def cleanup_and_quit(widget):
        """Zamknij port MIDI przed wyjściem"""
        if hasattr(win, 'midi_out') and win.midi_out:
            try:
                win.midi_out.close_port()
                print("MIDI OUT: Port zamknięty")
            except:
                pass
        Gtk.main_quit()
    
    win.connect("destroy", cleanup_and_quit)
    win.show_all()
    Gtk.main()
