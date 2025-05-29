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

class DrumSamplerApp(Gtk.Window):
    def __init__(self):
        Gtk.Window.__init__(self, title="Drum Sampler")
        self.set_border_width(10)
        self.set_default_size(1280, 720)
        self.is_fullscreen = False
        self.scale_factor = 1.0

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
        self.performer_mode = False
        self.simple_patterns = {inst: [0] * 16 for inst in self.instruments}
        self.advanced_patterns = {
            inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(16)]
            for inst in self.instruments
        }
        self.patterns = self.simple_patterns
        self.colors = ['red', 'green', 'blue', 'orange']
        self.midi_notes = {'Talerz': 49, 'Stopa': 36, 'Werbel': 38, 'TomTom': 45}
        self.buttons = {}
        self.samples = {}
        self.effects = {inst: {'volume': 0, 'pitch': 0, 'echo': 0, 'reverb': 0, 'pan': 0} for inst in self.instruments}
        self.last_button_pressed = None
        self.rhythm_types = {
            'single': {'notes': 1, 'speed': 1.0, 'swing': 0.0},
            'double': {'notes': 2, 'speed': 0.5, 'swing': 0.0},
            'burst': {'notes': 3, 'speed': 0.25, 'swing': 0.0},
            'swing': {'notes': 2, 'speed': 0.5, 'swing': 0.2},
            'accent': {'notes': 1, 'speed': 1.0, 'swing': 0.0}
        }

        # Load samples
        self.load_samples_from_directory()

        # UI setup
        self.create_toolbar()
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
        genre_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(genre_box, False, False, 0)

        preset_label = Gtk.Label(label="FX Genre:")
        genre_box.pack_start(preset_label, False, False, 0)

        self.preset_genre_combo = Gtk.ComboBoxText()
        genres = ["House", "Techno", "Drum and Bass", "Ambient", "Trap", "Dubstep", "Jazz", "Breakbeat"]
        for genre in genres:
            self.preset_genre_combo.append_text(genre)
        self.preset_genre_combo.set_active(0)
        genre_box.pack_start(self.preset_genre_combo, False, False, 0)

        auto_fx_button = Gtk.Button(label="Auto FX Style")
        auto_fx_button.connect("clicked", self.apply_auto_fx_for_selected_style)
        genre_box.pack_start(auto_fx_button, False, False, 0)

        reset_fx_button = Gtk.Button(label="Reset Genre FX")
        reset_fx_button.connect("clicked", self.reset_genre_fx)
        genre_box.pack_start(reset_fx_button, False, False, 0)

        separator = Gtk.Separator(orientation=Gtk.Orientation.VERTICAL)
        genre_box.pack_start(separator, False, False, 10)

        custom_label = Gtk.Label(label="Custom Genre:")
        genre_box.pack_start(custom_label, False, False, 0)

        self.custom_genre_entry = Gtk.Entry()
        genre_box.pack_start(self.custom_genre_entry, False, False, 0)

        progression_label = Gtk.Label(label="Progression:")
        genre_box.pack_start(progression_label, False, False, 0)
        self.progression_combo = Gtk.ComboBoxText()
        progressions = ["Linear", "Dense", "Sparse", "Random"]
        for p in progressions:
            self.progression_combo.append_text(p)
        self.progression_combo.set_active(0)
        genre_box.pack_start(self.progression_combo, False, False, 0)

        mod_label = Gtk.Label(label="Mod:")
        genre_box.pack_start(mod_label, False, False, 0)
        self.mod_combo = Gtk.ComboBoxText()
        mods = ["None", "Simplify", "More Complex"]
        for m in mods:
            self.mod_combo.append_text(m)
        self.mod_combo.set_active(0)
        genre_box.pack_start(self.mod_combo, False, False, 0)

        occurrences_label = Gtk.Label(label="Occurrences:")
        genre_box.pack_start(occurrences_label, False, False, 0)
        self.occurrences_spin = Gtk.SpinButton()
        self.occurrences_spin.set_adjustment(Gtk.Adjustment(value=4, lower=1, upper=16, step_increment=1))
        genre_box.pack_start(self.occurrences_spin, False, False, 0)

        intensity_label = Gtk.Label(label="Intensity:")
        genre_box.pack_start(intensity_label, False, False, 0)
        self.intensity_spin = Gtk.SpinButton()
        self.intensity_spin.set_adjustment(Gtk.Adjustment(value=0.5, lower=0, upper=1, step_increment=0.1))
        self.intensity_spin.set_numeric(True)
        self.intensity_spin.set_digits(1)
        genre_box.pack_start(self.intensity_spin, False, False, 0)

        generate_button = Gtk.Button(label="Generate Pattern")
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
        effect_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        effect_box.set_hexpand(True)
        self.main_box.pack_start(effect_box, False, False, 0)

        effect_label = Gtk.Label(label="Audio Effects")
        effect_box.pack_start(effect_label, False, False, 0)

        effect_grid = Gtk.Grid()
        effect_grid.set_column_spacing(10)
        effect_box.pack_start(effect_grid, True, True, 0)

        effects = ['Volume', 'Pitch', 'Echo', 'Reverb', 'Pan']
        for col, effect in enumerate(effects, start=1):
            label = Gtk.Label(label=effect)
            effect_grid.attach(label, col, 0, 1, 1)

        for row, instrument in enumerate(self.instruments, start=1):
            label = Gtk.Label(label=instrument)
            effect_grid.attach(label, 0, row, 1, 1)
            self.effect_sliders[instrument] = {}

            for col, effect in enumerate(effects, start=1):
                adjustment = Gtk.Adjustment(value=0, lower=-5, upper=5, step_increment=0.1)
                slider = Gtk.Scale(orientation=Gtk.Orientation.HORIZONTAL, adjustment=adjustment)
                slider.set_digits(1)
                slider.set_hexpand(True)
                slider.connect('value-changed', self.on_effect_changed, instrument, effect.lower())
                effect_grid.attach(slider, col, row, 1, 1)
                self.effect_sliders[instrument][effect.lower()] = slider

                reset_button = Gtk.Button(label="Reset")
                reset_button.set_size_request(60, 35)
                reset_button.connect('clicked', self.reset_effect, slider, instrument, effect.lower())
                effect_grid.attach_next_to(reset_button, slider, Gtk.PositionType.RIGHT, 1, 1)

        reset_all_button = Gtk.Button(label="Reset All Effects")
        reset_all_button.connect("clicked", self.reset_all_effects)
        effect_box.pack_start(reset_all_button, False, False, 0)

    def create_groove_controls(self):
        groove_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(groove_box, False, False, 0)

        groove_label = Gtk.Label(label="Groove Type:")
        groove_box.pack_start(groove_label, False, False, 0)

        self.groove_combo = Gtk.ComboBoxText()
        groove_types = ["simple", "stretch", "echoes", "bouncy", "relax"]
        for groove in groove_types:
            self.groove_combo.append_text(groove)
        self.groove_combo.set_active(0)
        groove_box.pack_start(self.groove_combo, False, False, 0)

        groove_button = Gtk.Button(label="Apply Groove")
        groove_button.connect("clicked", self.apply_groove)
        groove_box.pack_start(groove_button, False, False, 0)

        reset_groove_button = Gtk.Button(label="Reset Groove")
        reset_groove_button.connect("clicked", self.reset_groove)
        groove_box.pack_start(reset_groove_button, False, False, 0)

    def create_drummer_to_audio_button(self):
        drummer_button = Gtk.Button(label="Add Drummer to Audio")
        drummer_button.connect("clicked", self.add_drummer_to_audio)
        self.main_box.pack_start(drummer_button, False, False, 0)

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
        self.swap_buttons = {}  # Dictionary to store swap buttons for each instrument
        self.selected_sample = None  # Track the currently selected sample in the browser

        # Instrument controls
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

            # Add Swap button for each instrument
            swap_btn = Gtk.Button(label="<-")
            swap_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            swap_btn.connect("clicked", self.swap_sample, inst)
            btn_box.pack_start(swap_btn, False, False, 0)
            self.swap_buttons[inst] = swap_btn

            inst_box.pack_start(btn_box, False, False, 0)

            sample_box.pack_start(inst_box, False, False, 0)

        # Sample browser
        browser_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
        browser_label = Gtk.Label(label="Sample Browser")
        browser_box.pack_start(browser_label, False, False, 0)

        # Current directory label
        self.current_dir_label = Gtk.Label(label=os.getcwd())
        browser_box.pack_start(self.current_dir_label, False, False, 0)

        # TreeView for file browsing
        self.sample_store = Gtk.ListStore(str, str)  # Name, Full Path
        self.sample_tree = Gtk.TreeView(model=self.sample_store)
        self.sample_tree.set_headers_visible(True)

        name_column = Gtk.TreeViewColumn("Sample Name", Gtk.CellRendererText(), text=0)
        self.sample_tree.append_column(name_column)

        self.sample_tree.connect("row-activated", self.on_sample_activated)
        self.sample_selection = self.sample_tree.get_selection()
        self.sample_selection.connect("changed", self.on_sample_selected)

        tree_scrolled = Gtk.ScrolledWindow()
        tree_scrolled.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        tree_scrolled.set_min_content_height(int(150 * self.scale_factor))
        tree_scrolled.add(self.sample_tree)
        browser_box.pack_start(tree_scrolled, True, True, 0)

        # Navigation buttons
        nav_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        up_button = Gtk.Button(label="Up")
        up_button.connect("clicked", self.navigate_up)
        nav_box.pack_start(up_button, False, False, 0)

        refresh_button = Gtk.Button(label="Refresh")
        refresh_button.connect("clicked", self.refresh_sample_browser)
        nav_box.pack_start(refresh_button, False, False, 0)

        browser_box.pack_start(nav_box, False, False, 0)

        sample_box.pack_end(browser_box, True, True, 0)

        # Bank controls
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

        # Initialize sample browser
        self.current_directory = os.getcwd()
        self.refresh_sample_browser(None)

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
        genre = self.custom_genre_entry.get_text() or "Generic"
        progression = self.progression_combo.get_active_text()
        occurrences = int(self.occurrences_spin.get_value())
        intensity = self.intensity_spin.get_value()
        pattern_length = int(self.length_spinbutton.get_value())
        mod = self.mod_combo.get_active_text()

        rhythm_styles = {
            "Techno": {'Stopa': ['single'], 'Werbel': ['swing'], 'Talerz': ['burst'], 'TomTom': ['accent']},
            "House": {'Stopa': ['double'], 'Werbel': ['single'], 'Talerz': ['swing'], 'TomTom': ['single']},
            "Drum and Bass": {'Stopa': ['burst'], 'Werbel': ['swing'], 'Talerz': ['double'], 'TomTom': ['accent']},
            "Ambient": {'Stopa': ['single'], 'Werbel': ['double'], 'Talerz': ['swing'], 'TomTom': ['single']},
            "Trap": {'Stopa': ['double'], 'Werbel': ['burst'], 'Talerz': ['single'], 'TomTom': ['accent']},
            "Dubstep": {'Stopa': ['single'], 'Werbel': ['swing'], 'Talerz': ['burst'], 'TomTom': ['double']},
            "Jazz": {'Stopa': ['swing'], 'Werbel': ['double'], 'Talerz': ['single'], 'TomTom': ['accent']},
            "Breakbeat": {'Stopa': ['burst'], 'Werbel': ['swing'], 'Talerz': ['double'], 'TomTom': ['single']}
        }
        rules = rhythm_styles.get(genre, {'Stopa': ['single'], 'Werbel': ['single'], 'Talerz': ['single'], 'TomTom': ['single']})

        if self.advanced_sequencer_mode:
            for inst in self.instruments:
                self.patterns[inst] = [{'active': False, 'rhythm_type': 'single'} for _ in range(pattern_length)]
        else:
            for inst in self.instruments:
                self.patterns[inst] = [0] * pattern_length

        if progression == "Linear":
            for inst in self.instruments:
                step_interval = pattern_length // occurrences
                for i in range(0, pattern_length, step_interval):
                    if random.random() < intensity:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['active'] = True
                            self.patterns[inst][i]['rhythm_type'] = random.choice(rules[inst])
                        else:
                            self.patterns[inst][i] = 1
        elif progression == "Dense":
            for inst in self.instruments:
                for i in range(pattern_length):
                    if random.random() < intensity * 0.8:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['active'] = True
                            self.patterns[inst][i]['rhythm_type'] = random.choice(rules[inst])
                        else:
                            self.patterns[inst][i] = 1
        elif progression == "Sparse":
            for inst in self.instruments:
                for i in range(pattern_length):
                    if random.random() < intensity * 0.3:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['active'] = True
                            self.patterns[inst][i]['rhythm_type'] = random.choice(rules[inst])
                        else:
                            self.patterns[inst][i] = 1
        elif progression == "Random":
            for inst in self.instruments:
                for i in range(pattern_length):
                    if random.random() < intensity:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['active'] = True
                            self.patterns[inst][i]['rhythm_type'] = random.choice(rules[inst])
                        else:
                            self.patterns[inst][i] = 1

        if mod == "Simplify":
            for inst in self.instruments:
                for i in range(pattern_length):
                    if self.advanced_sequencer_mode:
                        if self.patterns[inst][i]['active'] and random.random() < 0.5:
                            self.patterns[inst][i]['active'] = False
                    else:
                        if self.patterns[inst][i] == 1 and random.random() < 0.5:
                            self.patterns[inst][i] = 0
        elif mod == "More Complex":
            for inst in self.instruments:
                for i in range(pattern_length):
                    if random.random() < intensity * 0.2:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['active'] = True
                            self.patterns[inst][i]['rhythm_type'] = random.choice(rules[inst])
                        else:
                            self.patterns[inst][i] = 1

        self.update_buttons()

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

    def reset_effect(self, button, slider, instrument, effect):
        slider.set_value(0)
        self.effects[instrument][effect] = 0

    def reset_all_effects(self, widget):
        for instrument in self.instruments:
            for effect in self.effects[instrument]:
                self.effects[instrument][effect] = 0
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(0)

    def reset_genre_fx(self, widget):
        for instrument in self.instruments:
            for effect in self.effects[instrument]:
                self.effects[instrument][effect] = 0
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(0)

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
        for instrument in self.instruments:
            for effect, value in settings.items():
                self.effects[instrument][effect] = value
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(value)

    def apply_auto_fx_for_selected_style(self, widget):
        selected_style = self.preset_genre_combo.get_active_text()
        if selected_style:
            self.apply_auto_fx_for_style(selected_style)

    def apply_groove(self, widget):
        self.groove_type = self.groove_combo.get_active_text()
        self.play_pattern(widget)

    def reset_groove(self, widget):
        self.groove_type = 'simple'
        self.groove_combo.set_active(0)

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
        beats_per_second = tempo / 60
        steps_per_beat = 4
        total_steps = int(total_duration * beats_per_second * steps_per_beat)
        percussion_track = {inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(total_steps)] for inst in self.instruments}

        for inst, times in percussion_events.items():
            for t in times:
                step = int(t * beats_per_second * steps_per_beat)
                if step < total_steps:
                    percussion_track[inst][step]['active'] = True
                    percussion_track[inst][step]['rhythm_type'] = 'single'

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

            rms_factor = rms_normalized[min(measure, len(rms_normalized) - 1)]
            onset_factor = onset_normalized[min(measure, len(onset_normalized) - 1)]
            complexity_factor = min(0.7, (rms_factor + onset_factor) / 2)

            for step in range(measure_start, measure_end, steps_per_beat):
                beat_in_measure = (step % (beats_per_measure * steps_per_beat)) // steps_per_beat
                if beat_in_measure == 0 and not percussion_track['Stopa'][step]['active']:
                    percussion_track['Stopa'][step]['active'] = True
                    percussion_track['Stopa'][step]['rhythm_type'] = 'single'
                if beat_in_measure == 2 and not percussion_track['Werbel'][step]['active'] and random.random() < 0.5 * (1 + complexity_factor):
                    percussion_track['Werbel'][step]['active'] = True
                    percussion_track['Werbel'][step]['rhythm_type'] = 'single'

            if complexity_factor > 0.3:
                for step in range(measure_start, measure_end, steps_per_beat * 2):
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
            button.set_label("Wejdź w pełny ekran")
            self.is_fullscreen = False
        else:
            self.fullscreen()
            button.set_label("Wyjdź z pełnego ekranu")
            self.is_fullscreen = True

    def play_pattern(self, widget):
        if self.loop_playing:
            return
        self.loop_playing = True
        self.play_thread = threading.Thread(target=self.play_loop)
        self.play_thread.daemon = True
        self.play_thread.start()

    def play_loop(self):
        pattern_length = int(self.length_spinbutton.get_value())
        step_duration = 60 / (self.get_bpm() * 4)

        while self.loop_playing:
            for step in range(pattern_length):
                if not self.loop_playing:
                    break
                for instrument in self.instruments:
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            sound = pygame.mixer.Sound(self.samples[instrument])
                            sound = self.apply_effects(sound, instrument)
                            sound = self.apply_groove_effects(sound, instrument, step)
                            for i in range(rhythm['notes']):
                                if not self.loop_playing:
                                    break
                                sound.play()
                                time.sleep(step_duration * rhythm['speed'] / rhythm['notes'])
                    else:
                        if self.patterns[instrument][step]:
                            sound = pygame.mixer.Sound(self.samples[instrument])
                            sound = self.apply_effects(sound, instrument)
                            sound = self.apply_groove_effects(sound, instrument, step)
                            sound.play()
                time.sleep(step_duration)
                if (step + 1) % self.steps_per_bpm == 0:
                    self.advance_bpm()

    def stop_pattern(self, widget):
        self.loop_playing = False
        if self.play_thread:
            self.play_thread.join()
            self.play_thread = None

    def get_bpm(self):
        return self.get_next_bpm()

    def randomize_pattern(self, widget):
        pattern_length = int(self.length_spinbutton.get_value())
        for instrument in self.instruments:
            for i in range(pattern_length):
                if self.advanced_sequencer_mode:
                    self.patterns[instrument][i]['active'] = random.random() < 0.3
                    if self.patterns[instrument][i]['active']:
                        self.patterns[instrument][i]['rhythm_type'] = random.choice(list(self.rhythm_types.keys()))
                else:
                    self.patterns[instrument][i] = 1 if random.random() < 0.3 else 0
        self.update_buttons()

    def load_samples(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Wybierz próbki", parent=self, action=Gtk.FileChooserAction.OPEN
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK
        )
        dialog.set_select_multiple(True)
        filter_wav = Gtk.FileFilter()
        filter_wav.set_name("Pliki WAV")
        filter_wav.add_mime_type("audio/wav")
        dialog.add_filter(filter_wav)

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filenames = dialog.get_filenames()
            for filename in filenames:
                for instrument in self.instruments:
                    if instrument.lower() in os.path.basename(filename).lower():
                        self.samples[instrument] = filename
                        break
        dialog.destroy()

    def save_project(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Zapisz projekt", parent=self, action=Gtk.FileChooserAction.SAVE
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK
        )
        dialog.set_current_name("project.json")

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            project_data = {
                'patterns': self.patterns,
                'samples': self.samples,
                'effects': self.effects,
                'bpm': self.absolute_bpm,
                'groove_type': self.groove_type,
                'advanced_sequencer_mode': self.advanced_sequencer_mode,
                'adsr': self.current_adsr
            }
            with open(dialog.get_filename(), 'w') as f:
                json.dump(project_data, f, indent=2)
        dialog.destroy()

    def load_project(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Wczytaj projekt", parent=self, action=Gtk.FileChooserAction.OPEN
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK
        )
        filter_json = Gtk.FileFilter()
        filter_json.set_name("Pliki JSON")
        filter_json.add_mime_type("application/json")
        dialog.add_filter(filter_json)

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            with open(dialog.get_filename(), 'r') as f:
                project_data = json.load(f)
                self.patterns = project_data.get('patterns', self.patterns)
                self.samples = project_data.get('samples', self.samples)
                self.effects = project_data.get('effects', self.effects)
                self.absolute_bpm = project_data.get('bpm', self.absolute_bpm)
                self.groove_type = project_data.get('groove_type', self.groove_type)
                self.advanced_sequencer_mode = project_data.get('advanced_sequencer_mode', self.advanced_sequencer_mode)
                self.current_adsr = project_data.get('adsr', self.current_adsr)
                self.bpm_entry.set_text(str(self.absolute_bpm))
                self.groove_combo.set_active(
                    [t for t in self.groove_combo.get_model()][0].index(self.groove_type)
                )
                self.sequencer_mode_switch.set_active(self.advanced_sequencer_mode)
                for inst in self.instruments:
                    for param, value in self.current_adsr[inst].items():
                        self.adsr_entries[inst][param].set_text(f"{value:.2f}")
                self.update_buttons()
        dialog.destroy()

    def export_to_midi(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Eksportuj MIDI", parent=self, action=Gtk.FileChooserAction.SAVE
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK
        )
        dialog.set_current_name("pattern.mid")

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            midi = MIDIFile(1)
            track = 0
            time = 0
            midi.addTrackName(track, time, "Drum Pattern")
            midi.addTempo(track, time, self.absolute_bpm)

            pattern_length = int(self.length_spinbutton.get_value())
            beat_duration = 1

            for instrument in self.instruments:
                for step in range(pattern_length):
                    if self.patterns[instrument][step]:
                        midi.addNote(
                            track,
                            9,
                            self.midi_notes[instrument],
                            time + step * beat_duration,
                            beat_duration,
                            100
                        )

            with open(dialog.get_filename(), 'wb') as f:
                midi.writeFile(f)
        dialog.destroy()

    def export_advanced_midi(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Eksportuj zaawansowany MIDI", parent=self, action=Gtk.FileChooserAction.SAVE
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK
        )
        dialog.set_current_name("advanced_pattern.mid")

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            midi = MIDIFile(1)
            track = 0
            time = 0
            midi.addTrackName(track, time, "Advanced Drum Pattern")
            midi.addTempo(track, time, self.absolute_bpm)

            pattern_length = int(self.length_spinbutton.get_value())
            beat_duration = 1

            for instrument in self.instruments:
                for step in range(pattern_length):
                    step_data = self.patterns[instrument][step]
                    if step_data['active']:
                        rhythm = self.rhythm_types[step_data['rhythm_type']]
                        note_duration = beat_duration * rhythm['speed'] / rhythm['notes']
                        for i in range(rhythm['notes']):
                            midi.addNote(
                                track,
                                9,
                                self.midi_notes[instrument],
                                time + step * beat_duration + i * note_duration,
                                note_duration,
                                100
                            )

            with open(dialog.get_filename(), 'wb') as f:
                midi.writeFile(f)
        dialog.destroy()

    def autolevel_samples(self, widget):
        max_amplitude = 0
        for instrument in self.instruments:
            sound = pygame.mixer.Sound(self.samples[instrument])
            samples = pygame.sndarray.array(sound)
            amp = np.max(np.abs(samples))
            if amp > max_amplitude:
                max_amplitude = amp

        for instrument in self.instruments:
            sound = pygame.mixer.Sound(self.samples[instrument])
            samples = pygame.sndarray.array(sound)
            if max_amplitude > 0:
                samples = samples * (32767 / max_amplitude)
                new_sound = pygame.sndarray.make_sound(samples.astype(np.int16))
                temp_wav = f"temp_{instrument}.wav"
                pygame.sndarray.save(new_sound, temp_wav)
                self.samples[instrument] = temp_wav

    def generate_default_samples(self):
        sample_rate = 44100
        duration = 0.5
        t = np.linspace(0, duration, int(sample_rate * duration), False)

        for instrument in self.instruments:
            if instrument == 'Talerz':
                noise = np.random.normal(0, 0.5, len(t))
                envelope = np.exp(-5 * t / duration)
                sample = noise * envelope
            elif instrument == 'Stopa':
                freq = 60
                sine = np.sin(2 * np.pi * freq * t)
                envelope = np.exp(-10 * t / duration)
                sample = sine * envelope
            elif instrument == 'Werbel':
                noise = np.random.normal(0, 0.5, len(t))
                sine = np.sin(2 * np.pi * 200 * t)
                envelope = np.exp(-15 * t / duration)
                sample = (noise * 0.5 + sine * 0.5) * envelope
            elif instrument == 'TomTom':
                freq = 100
                sine = np.sin(2 * np.pi * freq * t)
                envelope = np.exp(-8 * t / duration)
                sample = sine * envelope

            sample = np.int16(sample / np.max(np.abs(sample)) * 32767)
            temp_wav = f"temp_{instrument}.wav"
            sf.write(temp_wav, sample, sample_rate)
            self.samples[instrument] = temp_wav

    def adjust_adsr(self, button, instrument, param, delta):
        current_value = self.current_adsr[instrument][param]
        new_value = max(0, min(1, current_value + delta))
        self.current_adsr[instrument][param] = new_value
        self.adsr_entries[instrument][param].set_text(f"{new_value:.2f}")

    def on_adsr_entry_changed(self, entry, instrument, param):
        try:
            value = float(entry.get_text())
            value = max(0, min(1, value))
            self.current_adsr[instrument][param] = value
            entry.set_text(f"{value:.2f}")
        except ValueError:
            entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")

    def reset_adsr(self, button, instrument):
        self.current_adsr[instrument] = self.nominal_adsr[instrument].copy()
        for param in ['attack', 'decay', 'sustain', 'release']:
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")

    def randomize_adsr(self, button, instrument):
        for param in ['attack', 'decay', 'sustain', 'release']:
            self.current_adsr[instrument][param] = random.uniform(0, 1)
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")

    def toggle_preview(self, checkbutton, instrument):
        self.preview_active[instrument] = checkbutton.get_active()
        if self.preview_active[instrument]:
            sound = pygame.mixer.Sound(self.samples[instrument])
            sound = self.apply_effects(sound, instrument)
            sound.play()

    def swap_sample(self, button, instrument):
        if self.selected_sample and os.path.splitext(self.selected_sample)[1].lower() == '.wav':
            self.samples[instrument] = self.selected_sample
            print(f"Przypisano próbkę {self.selected_sample} do instrumentu {instrument}")
            if self.preview_active[instrument]:
                sound = pygame.mixer.Sound(self.samples[instrument])
                sound = self.apply_effects(sound, instrument)
                sound.play()
        else:
            print("Nie wybrano poprawnego pliku WAV")

    def on_sample_selected(self, selection):
        model, treeiter = selection.get_selected()
        if treeiter:
            self.selected_sample = model[treeiter][1]
            if os.path.isfile(self.selected_sample) and self.selected_sample.lower().endswith('.wav'):
                try:
                    sound = pygame.mixer.Sound(self.selected_sample)
                    sound.play()
                except Exception as e:
                    print(f"Błąd podczas odtwarzania próbki: {e}")

    def on_sample_activated(self, treeview, path, column):
        model = treeview.get_model()
        treeiter = model.get_iter(path)
        full_path = model[treeiter][1]
        if os.path.isdir(full_path):
            self.current_directory = full_path
            self.refresh_sample_browser(None)
        elif os.path.isfile(full_path) and full_path.lower().endswith('.wav'):
            self.selected_sample = full_path
            try:
                sound = pygame.mixer.Sound(self.selected_sample)
                sound.play()
            except Exception as e:
                print(f"Błąd podczas odtwarzania próbki: {e}")

    def navigate_up(self, button):
        parent_dir = os.path.dirname(self.current_directory)
        if os.path.isdir(parent_dir):
            self.current_directory = parent_dir
            self.refresh_sample_browser(None)

    def refresh_sample_browser(self, button):
        self.sample_store.clear()
        self.current_dir_label.set_text(self.current_directory)
        try:
            for item in os.listdir(self.current_directory):
                full_path = os.path.join(self.current_directory, item)
                if os.path.isdir(full_path) or (os.path.isfile(full_path) and item.lower().endswith('.wav')):
                    self.sample_store.append([item, full_path])
        except Exception as e:
            print(f"Błąd podczas odświeżania przeglądarki: {e}")

    def load_sample_bank(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Wczytaj bank próbek", parent=self, action=Gtk.FileChooserAction.OPEN
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK
        )
        filter_json = Gtk.FileFilter()
        filter_json.set_name("Pliki JSON")
        filter_json.add_mime_type("application/json")
        dialog.add_filter(filter_json)

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            with open(dialog.get_filename(), 'r') as f:
                bank_data = json.load(f)
                for instrument, sample_path in bank_data.items():
                    if instrument in self.instruments and os.path.exists(sample_path):
                        self.samples[instrument] = sample_path
        dialog.destroy()

    def export_sample_bank(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Eksportuj bank próbek", parent=self, action=Gtk.FileChooserAction.SAVE
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_SAVE, Gtk.ResponseType.OK
        )
        dialog.set_current_name("sample_bank.json")

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            with open(dialog.get_filename(), 'w') as f:
                json.dump(self.samples, f, indent=2)
        dialog.destroy()

if __name__ == '__main__':
    win = DrumSamplerApp()
    win.connect("destroy", Gtk.main_quit)
    win.show_all()
    Gtk.main()
