import gi
import random
import time
import threading
import pygame
import platform
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
        self.current_directory = 'samples'
        self.instruments = ['Talerz', 'Stopa', 'Werbel', 'TomTom']
        self.advanced_sequencer_mode = False
        self.performer_mode = False
        self.simple_patterns = {inst: [0] * 16 for inst in self.instruments}
        self.advanced_patterns = {
            inst: [{'active': False, 'rhythm_type': 'single'} for _ in range(16)]
            for inst in self.instruments
        }
        self.patterns = self.simple_patterns
        self.base_colors = {'Talerz': '#FF5555', 'Stopa': '#55FF55', 'Werbel': '#5555FF', 'TomTom': '#FFAA00'}
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
        # Sample generation parameters
        self.sample_params = {
            'Talerz': {'waveform': 'sine', 'frequency': 8000, 'amplitude': 0.8, 'duration': 1.0, 'attack_curve': 'exponential'},
            'Stopa': {'waveform': 'sine', 'frequency': 100, 'amplitude': 1.0, 'duration': 0.3, 'attack_curve': 'linear'},
            'Werbel': {'waveform': 'noise', 'frequency': 4000, 'amplitude': 0.9, 'duration': 0.4, 'attack_curve': 'exponential'},
            'TomTom': {'waveform': 'sine', 'frequency': 200, 'amplitude': 0.9, 'duration': 0.5, 'attack_curve': 'linear'}
        }
        # Initialize ADSR parameters
        self.nominal_adsr = {
            'Talerz': {'attack': 0.01, 'decay': 0.1, 'sustain': 0.8, 'release': 0.6},
            'Stopa': {'attack': 0.01, 'decay': 0.2, 'sustain': 0.3, 'release': 0.1},
            'Werbel': {'attack': 0.02, 'decay': 0.2, 'sustain': 0.4, 'release': 0.3},
            'TomTom': {'attack': 0.03, 'decay': 0.3, 'sustain': 0.5, 'release': 0.4}
        }
        self.current_adsr = {inst: self.nominal_adsr[inst].copy() for inst in self.instruments}
        self.preview_active = {inst: False for inst in self.instruments}
        self.swap_buttons = {}

        # Load or generate samples
        self.load_samples_from_directory()
        if not self.samples:
            self.generate_parametric_samples()

        # UI setup
        self.create_toolbar()
        self.grid = Gtk.Grid()
        self.main_box.pack_start(self.grid, True, True, 0)

        # Grid setup with instrument labels
        self.instrument_labels = {}
        for step in range(16):
            label = Gtk.Label(label=str(step + 1))
            self.grid.attach(label, step + 1, 0, 1, 1)

        for idx, instrument in enumerate(self.instruments):
            label = Gtk.Label(label=instrument)
            context = label.get_style_context()
            context.add_class(f"instrument-{instrument.lower()}")
            self.instrument_labels[instrument] = label
            self.grid.attach(label, 0, idx + 1, 1, 1)
            self.buttons[instrument] = []
            for step in range(16):
                button = Gtk.ToggleButton()
                button.set_size_request(30, 30)
                context = button.get_style_context()
                context.add_class(f"circle-{instrument.lower()}")
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

    # The following methods are unchanged from the provided drumpatterns_sampler.py
    def generate_parametric_samples(self):
        sample_rate = 44100
        for inst in self.instruments:
            params = self.sample_params[inst]
            duration = params['duration']
            t = np.linspace(0, duration, int(sample_rate * duration), False)

            # Generate waveform based on type
            if params['waveform'] == 'sine':
                signal = params['amplitude'] * np.sin(2 * np.pi * params['frequency'] * t)
            elif params['waveform'] == 'square':
                signal = params['amplitude'] * np.sign(np.sin(2 * np.pi * params['frequency'] * t))
            elif params['waveform'] == 'sawtooth':
                signal = params['amplitude'] * (2 * (t * params['frequency'] - np.floor(0.5 + t * params['frequency'])))
            elif params['waveform'] == 'noise':
                signal = params['amplitude'] * np.random.normal(0, 1, len(t))
            else:
                signal = np.zeros(len(t))

            # Apply ADSR envelope with curve
            signal = self.apply_adsr_to_signal(signal, inst, sample_rate)
            
            # Normalize and convert to stereo
            signal = normalize(AudioSegment(
                (signal * 32767).astype(np.int16).tobytes(),
                frame_rate=sample_rate,
                sample_width=2,
                channels=1
            ))
            signal = np.array(signal.get_array_of_samples()).reshape(-1, 1)
            signal = np.hstack((signal, signal))  # Stereo
            self.samples[inst] = pygame.sndarray.make_sound(signal.astype(np.int16))

    def apply_adsr_to_signal(self, signal, instrument, sample_rate):
        adsr = self.current_adsr[instrument]
        total_samples = len(signal)
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
        curve_type = self.sample_params[instrument]['attack_curve']

        # Apply curved envelopes
        if attack_samples > 0:
            if curve_type == 'exponential':
                envelope[:attack_samples] = np.power(np.linspace(0, 1, attack_samples), 2)
            elif curve_type == 'logarithmic':
                envelope[:attack_samples] = np.log1p(np.linspace(0, 9, attack_samples)) / np.log1p(9)
            else:  # linear
                envelope[:attack_samples] = np.linspace(0, 1, attack_samples)

        if decay_samples > 0 and attack_samples < total_samples:
            decay_end = min(attack_samples + decay_samples, total_samples)
            if curve_type == 'exponential':
                envelope[attack_samples:decay_end] = np.power(np.linspace(1, adsr['sustain'], decay_end - attack_samples), 2)
            elif curve_type == 'logarithmic':
                envelope[attack_samples:decay_end] = adsr['sustain'] + (1 - adsr['sustain']) * np.log1p(np.linspace(9, 0, decay_end - attack_samples)) / np.log1p(9)
            else:
                envelope[attack_samples:decay_end] = np.linspace(1, adsr['sustain'], decay_end - attack_samples)

        if sustain_samples > 0 and attack_samples + decay_samples < total_samples:
            sustain_end = min(attack_samples + decay_samples + sustain_samples, total_samples)
            envelope[attack_samples + decay_samples:sustain_end] = adsr['sustain']

        if release_samples > 0 and total_samples - release_samples > 0:
            release_start = max(0, total_samples - release_samples)
            if curve_type == 'exponential':
                envelope[release_start:] = adsr['sustain'] * np.power(np.linspace(1, 0, total_samples - release_start), 2)
            elif curve_type == 'logarithmic':
                envelope[release_start:] = adsr['sustain'] * np.log1p(np.linspace(9, 0, total_samples - release_start)) / np.log1p(9)
            else:
                envelope[release_start:] = np.linspace(adsr['sustain'], 0, total_samples - release_start)

        return signal * envelope

    def create_sample_manipulation_area(self):
        sample_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(10 * self.scale_factor))
        sample_box.set_hexpand(True)
        self.main_box.pack_start(sample_box, False, False, int(10 * self.scale_factor))

        self.adsr_entries = {}
        self.sample_param_controls = {}
        for inst in self.instruments:
            inst_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
            inst_label = Gtk.Label(label=inst)
            context = inst_label.get_style_context()
            context.add_class(f"instrument-{inst.lower()}")
            inst_box.pack_start(inst_label, False, False, 0)

            # ADSR controls
            adsr_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            self.adsr_entries[inst] = {}
            for param in ['attack', 'decay', 'sustain', 'release']:
                param_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(2 * self.scale_factor))
                minus_btn = Gtk.Button()
                minus_btn.set_image(Gtk.Image.new_from_icon_name("list-remove", Gtk.IconSize.SMALL_TOOLBAR))
                minus_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
                minus_btn.set_tooltip_text(f"Decrease {param}")
                minus_btn.connect("clicked", self.adjust_adsr, inst, param, -0.1)
                param_box.pack_start(minus_btn, False, False, 0)

                entry = Gtk.Entry()
                entry.set_width_chars(int(4 * self.scale_factor))
                entry.set_text(f"{self.current_adsr[inst][param]:.2f}")
                entry.connect("changed", self.on_adsr_entry_changed, inst, param)
                param_box.pack_start(entry, False, False, 0)
                self.adsr_entries[inst][param] = entry

                plus_btn = Gtk.Button()
                plus_btn.set_image(Gtk.Image.new_from_icon_name("list-add", Gtk.IconSize.SMALL_TOOLBAR))
                plus_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
                plus_btn.set_tooltip_text(f"Increase {param}")
                plus_btn.connect("clicked", self.adjust_adsr, inst, param, 0.1)
                param_box.pack_start(plus_btn, False, False, 0)

                adsr_box.pack_start(param_box, False, False, 0)

            inst_box.pack_start(adsr_box, False, False, 0)

            # Sample parameter controls
            self.sample_param_controls[inst] = {}
            param_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
            param_box.pack_start(Gtk.Label(label="Sample Parameters"), False, False, 0)

            # Waveform type
            waveform_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            waveform_label = Gtk.Label(label="Waveform:")
            waveform_box.pack_start(waveform_label, False, False, 0)
            waveform_combo = Gtk.ComboBoxText()
            waveform_types = ['sine', 'square', 'sawtooth', 'noise']
            for wtype in waveform_types:
                waveform_combo.append_text(wtype)
            waveform_combo.set_active(waveform_types.index(self.sample_params[inst]['waveform']))
            waveform_combo.connect("changed", self.on_sample_param_changed, inst, 'waveform')
            waveform_box.pack_start(waveform_combo, False, False, 0)
            self.sample_param_controls[inst]['waveform'] = waveform_combo
            param_box.pack_start(waveform_box, False, False, 0)

            # Frequency
            freq_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            freq_label = Gtk.Label(label="Frequency (Hz):")
            freq_box.pack_start(freq_label, False, False, 0)
            freq_entry = Gtk.Entry()
            freq_entry.set_width_chars(int(6 * self.scale_factor))
            freq_entry.set_text(str(self.sample_params[inst]['frequency']))
            freq_entry.connect("changed", self.on_sample_param_changed, inst, 'frequency')
            freq_box.pack_start(freq_entry, False, False, 0)
            self.sample_param_controls[inst]['frequency'] = freq_entry
            param_box.pack_start(freq_box, False, False, 0)

            # Amplitude
            amp_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            amp_label = Gtk.Label(label="Amplitude:")
            amp_box.pack_start(amp_label, False, False, 0)
            amp_adjustment = Gtk.Adjustment(value=self.sample_params[inst]['amplitude'], lower=0.1, upper=1.0, step_increment=0.1)
            amp_scale = Gtk.Scale(orientation=Gtk.Orientation.HORIZONTAL, adjustment=amp_adjustment)
            amp_scale.set_digits(2)
            amp_scale.connect("value-changed", self.on_sample_param_changed, inst, 'amplitude')
            amp_box.pack_start(amp_scale, True, True, 0)
            self.sample_param_controls[inst]['amplitude'] = amp_scale
            param_box.pack_start(amp_box, False, False, 0)

            # Duration
            dur_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            dur_label = Gtk.Label(label="Duration (s):")
            dur_box.pack_start(dur_label, False, False, 0)
            dur_entry = Gtk.Entry()
            dur_entry.set_width_chars(int(6 * self.scale_factor))
            dur_entry.set_text(str(self.sample_params[inst]['duration']))
            dur_entry.connect("changed", self.on_sample_param_changed, inst, 'duration')
            dur_box.pack_start(dur_entry, False, False, 0)
            self.sample_param_controls[inst]['duration'] = dur_entry
            param_box.pack_start(dur_box, False, False, 0)

            # Attack curve
            curve_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            curve_label = Gtk.Label(label="Attack Curve:")
            curve_box.pack_start(curve_label, False, False, 0)
            curve_combo = Gtk.ComboBoxText()
            curve_types = ['linear', 'exponential', 'logarithmic']
            for ctype in curve_types:
                curve_combo.append_text(ctype)
            curve_combo.set_active(curve_types.index(self.sample_params[inst]['attack_curve']))
            curve_combo.connect("changed", self.on_sample_param_changed, inst, 'attack_curve')
            curve_box.pack_start(curve_combo, False, False, 0)
            self.sample_param_controls[inst]['attack_curve'] = curve_combo
            param_box.pack_start(curve_box, False, False, 0)

            inst_box.pack_start(param_box, False, False, 0)

            btn_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            reset_btn = Gtk.Button()
            reset_btn.set_image(Gtk.Image.new_from_icon_name("edit-undo", Gtk.IconSize.SMALL_TOOLBAR))
            reset_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            reset_btn.set_tooltip_text("Reset ADSR")
            reset_btn.connect("clicked", self.reset_adsr, inst)
            btn_box.pack_start(reset_btn, False, False, 0)

            rand_btn = Gtk.Button()
            rand_btn.set_image(Gtk.Image.new_from_icon_name("view-refresh", Gtk.IconSize.SMALL_TOOLBAR))
            rand_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            rand_btn.set_tooltip_text("Randomize ADSR")
            rand_btn.connect("clicked", self.randomize_adsr, inst)
            btn_box.pack_start(rand_btn, False, False, 0)

            preview_check = Gtk.CheckButton()
            preview_check.set_label("")
            preview_check.set_tooltip_text("Toggle Preview")
            preview_check.connect("toggled", self.toggle_preview, inst)
            btn_box.pack_start(preview_check, False, False, 0)

            swap_btn = Gtk.Button()
            swap_btn.set_image(Gtk.Image.new_from_icon_name("object-flip-horizontal", Gtk.IconSize.SMALL_TOOLBAR))
            swap_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            swap_btn.set_tooltip_text("Swap Sample")
            swap_btn.connect("clicked", self.swap_sample, inst)
            btn_box.pack_start(swap_btn, False, False, 0)
            self.swap_buttons[inst] = swap_btn

            inst_box.pack_start(btn_box, False, False, 0)

            sample_box.pack_start(inst_box, False, False, 0)

        # Sample browser
        browser_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
        browser_label = Gtk.Label(label="Sample Browser")
        browser_box.pack_start(browser_label, False, False, 0)

        self.current_dir_label = Gtk.Label(label=os.getcwd())
        browser_box.pack_start(self.current_dir_label, False, False, 0)

        self.sample_store = Gtk.ListStore(str, str)
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

        nav_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        up_button = Gtk.Button()
        up_button.set_image(Gtk.Image.new_from_icon_name("go-up", Gtk.IconSize.BUTTON))
        up_button.set_tooltip_text("Navigate Up")
        up_button.connect("clicked", self.navigate_up)
        nav_box.pack_start(up_button, False, False, 0)

        refresh_button = Gtk.Button()
        refresh_button.set_image(Gtk.Image.new_from_icon_name("view-refresh", Gtk.IconSize.BUTTON))
        refresh_button.set_tooltip_text("Refresh Browser")
        refresh_button.connect("clicked", self.refresh_sample_browser)
        nav_box.pack_start(refresh_button, False, False, 0)

        browser_box.pack_start(nav_box, False, False, 0)

        sample_box.pack_end(browser_box, True, True, 0)

        bank_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        bank_label = Gtk.Label(label="Bank:")
        bank_box.pack_start(bank_label, False, False, 0)

        self.bank_combo = Gtk.ComboBoxText()
        self.bank_combo.append_text("Default")
        self.bank_combo.set_active(0)
        bank_box.pack_start(self.bank_combo, False, False, 0)

        load_btn = Gtk.Button()
        load_btn.set_image(Gtk.Image.new_from_icon_name("document-open", Gtk.IconSize.SMALL_TOOLBAR))
        load_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
        load_btn.set_tooltip_text("Load Sample Bank")
        load_btn.connect("clicked", self.load_sample_bank)
        bank_box.pack_start(load_btn, False, False, 0)

        export_btn = Gtk.Button()
        export_btn.set_image(Gtk.Image.new_from_icon_name("document-save", Gtk.IconSize.SMALL_TOOLBAR))
        export_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
        export_btn.set_tooltip_text("Export Sample Bank")
        export_btn.connect("clicked", self.export_sample_bank)
        bank_box.pack_start(export_btn, False, False, 0)

        sample_box.pack_end(bank_box, False, False, 0)

        self.current_directory = os.getcwd()
        self.refresh_sample_browser(None)

    def on_sample_param_changed(self, widget, instrument, param):
        try:
            if param == 'waveform':
                self.sample_params[instrument][param] = widget.get_active_text()
            elif param == 'frequency':
                self.sample_params[instrument][param] = float(widget.get_text())
            elif param == 'amplitude':
                self.sample_params[instrument][param] = widget.get_value()
            elif param == 'duration':
                self.sample_params[instrument][param] = float(widget.get_text())
            elif param == 'attack_curve':
                self.sample_params[instrument][param] = widget.get_active_text()
            self.generate_parametric_samples()
            if self.preview_active[instrument]:
                self.samples[instrument].play()
        except ValueError:
            print(f"Invalid input for {param}")

    def create_toolbar(self):
        toolbar = Gtk.Toolbar()
        self.main_box.pack_start(toolbar, False, False, 0)

        button_info = [
            ("media-playback-start", self.play_pattern, "Play Pattern"),
            ("media-playback-stop", self.stop_pattern, "Stop Pattern"),
            ("view-refresh", self.randomize_pattern, "Randomize Pattern"),
            ("document-open", self.load_samples, "Load Samples"),
            ("document-save", self.save_project, "Save Project"),
            ("document-open", self.load_project, "Load Project"),
            ("document-export", self.export_to_midi, "Export MIDI"),
            ("document-export", self.export_advanced_midi, "Export Advanced MIDI"),
            ("view-fullscreen", self.toggle_fullscreen, "Toggle Fullscreen")
        ]

        for icon_name, callback, tooltip in button_info:
            button = Gtk.ToolButton()
            button.set_icon_name(icon_name)
            button.set_tooltip_text(tooltip)
            button.connect("clicked", callback)
            toolbar.insert(button, -1)

        # Sequencer Mode
        sequencer_mode_item = Gtk.ToolItem()
        sequencer_mode_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=5)
        sequencer_mode_label = Gtk.Label(label="Sequencer:")
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
        performer_mode_item = Gtk.ToolItem()
        performer_mode_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=5)
        performer_mode_label = Gtk.Label(label="Performer:")
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
        audio_backend_item = Gtk.ToolItem()
        backend_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=5)
        audio_backend_label = Gtk.Label(label="Backend:")
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
        .circle-talerz, .circle-stopa, .circle-werbel, .circle-tomtom {
            border-radius: 15px;
            background-color: white;
        }
        .circle-talerz:active { background-color: #FF5555; }
        .circle-stopa:active { background-color: #55FF55; }
        .circle-werbel:active { background-color: #5555FF; }
        .circle-tomtom:active { background-color: #FFAA00; }
        .instrument-talerz { background-color: #FF5555; color: white; padding: 2px; }
        .instrument-stopa { background-color: #55FF55; color: black; padding: 2px; }
        .instrument-werbel { background-color: #5555FF; color: white; padding: 2px; }
        .instrument-tomtom { background-color: #FFAA00; color: black; padding: 2px; }
        @keyframes blink-animation {
            0% { opacity: 1; }
            50% { opacity: 0.5; }
            100% { opacity: 1; }
        }
        .blink {
            animation: blink-animation 0.3s linear 1;
        }
        """
        for inst in self.instruments:
            base_color = self.base_colors[inst]
            for effect in ['volume', 'pitch', 'echo', 'reverb', 'pan']:
                css += f"""
                .effect-{inst.lower()}-{effect} {{
                    background-color: {self.adjust_hue(base_color, self.effects[inst][effect])};
                }}
                """
        css_provider.load_from_data(css.encode())
        Gtk.StyleContext.add_provider_for_screen(
            Gdk.Screen.get_default(),
            css_provider,
            Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION
        )
        self.css_provider = css_provider

    def adjust_hue(self, hex_color, effect_value):
        from colorsys import rgb_to_hsv, hsv_to_rgb
        rgb = tuple(int(hex_color.lstrip('#')[i:i+2], 16) / 255.0 for i in (0, 2, 4))
        h, s, v = rgb_to_hsv(*rgb)
        h = (h + effect_value * 0.1) % 1.0
        r, g, b = hsv_to_rgb(h, s, v)
        return f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"

    def update_effect_colors(self):
        css = """
        .circle-talerz, .circle-stopa, .circle-werbel, .circle-tomtom {
            border-radius: 15px;
            background-color: white;
        }
        .circle-talerz:active { background-color: #FF5555; }
        .circle-stopa:active { background-color: #55FF55; }
        .circle-werbel:active { background-color: #5555FF; }
        .circle-tomtom:active { background-color: #FFAA00; }
        .instrument-talerz { background-color: #FF5555; color: white; padding: 2px; }
        .instrument-stopa { background-color: #55FF55; color: black; padding: 2px; }
        .instrument-werbel { background-color: #5555FF; color: white; padding: 2px; }
        .instrument-tomtom { background-color: #FFAA00; color: black; padding: 2px; }
        @keyframes blink-animation {
            0% { opacity: 1; }
            50% { opacity: 0.5; }
            100% { opacity: 1; }
        }
        .blink {
            animation: blink-animation 0.3s linear 1;
        }
        """
        for inst in self.instruments:
            base_color = self.base_colors[inst]
            for effect in ['volume', 'pitch', 'echo', 'reverb', 'pan']:
                css += f"""
                .effect-{inst.lower()}-{effect} {{
                    background-color: {self.adjust_hue(base_color, self.effects[inst][effect])};
                }}
                """
        self.css_provider.load_from_data(css.encode())

    def create_bpm_controls(self):
        bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(bpm_box, False, False, 0)

        bpm_label = Gtk.Label(label="BPM:")
        bpm_box.pack_start(bpm_label, False, False, 0)

        self.bpm_entry = Gtk.Entry()
        self.bpm_entry.set_text(str(self.absolute_bpm))
        self.bpm_entry.set_width_chars(4)
        bpm_box.pack_start(self.bpm_entry, False, False, 0)

        bpm_up_button = Gtk.Button()
        bpm_up_button.set_image(Gtk.Image.new_from_icon_name("go-up", Gtk.IconSize.SMALL_TOOLBAR))
        bpm_up_button.set_tooltip_text("Increase BPM")
        bpm_up_button.connect("clicked", self.bpm_step_up)
        bpm_box.pack_start(bpm_up_button, False, False, 0)

        bpm_down_button = Gtk.Button()
        bpm_down_button.set_image(Gtk.Image.new_from_icon_name("go-down", Gtk.IconSize.SMALL_TOOLBAR))
        bpm_down_button.set_tooltip_text("Decrease BPM")
        bpm_down_button.connect("clicked", self.bpm_step_down)
        bpm_box.pack_start(bpm_down_button, False, False, 0)

    def create_matched_bpm_control(self):
        bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(bpm_box, False, False, 0)

        matched_bpm_button = Gtk.Button()
        matched_bpm_button.set_image(Gtk.Image.new_from_icon_name("emblem-synchronized", Gtk.IconSize.BUTTON))
        matched_bpm_button.set_tooltip_text("Match BPM to Pattern Density")
        matched_bpm_button.connect("clicked", self.matched_bpm)
        bpm_box.pack_start(matched_bpm_button, False, False, 0)

        perfect_bpm_button = Gtk.Button()
        perfect_bpm_button.set_image(Gtk.Image.new_from_icon_name("emblem-favorite", Gtk.IconSize.BUTTON))
        perfect_bpm_button.set_tooltip_text("Set Perfect Tempo BPM")
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

        apply_button = Gtk.Button()
        apply_button.set_image(Gtk.Image.new_from_icon_name("emblem-ok", Gtk.IconSize.BUTTON))
        apply_button.set_tooltip_text("Apply Dynamic BPM")
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

        auto_fx_button = Gtk.Button()
        auto_fx_button.set_image(Gtk.Image.new_from_icon_name("system-run", Gtk.IconSize.BUTTON))
        auto_fx_button.set_tooltip_text("Apply Auto FX Style")
        auto_fx_button.connect("clicked", self.apply_auto_fx_for_selected_style)
        genre_box.pack_start(auto_fx_button, False, False, 0)

        reset_fx_button = Gtk.Button()
        reset_fx_button.set_image(Gtk.Image.new_from_icon_name("edit-clear", Gtk.IconSize.BUTTON))
        reset_fx_button.set_tooltip_text("Reset Genre FX")
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

        generate_button = Gtk.Button()
        generate_button.set_image(Gtk.Image.new_from_icon_name("emblem-downloads", Gtk.IconSize.BUTTON))
        generate_button.set_tooltip_text("Generate Custom Pattern")
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

        randomize_label = Gtk.Label(label="Randomization:")
        randomize_box.pack_start(randomize_label, False, False, 0)

        self.randomize_probability_adjustment = Gtk.Adjustment(value=10, lower=0, upper=100, step_increment=1)
        self.randomize_probability_spin = Gtk.SpinButton()
        self.randomize_probability_spin.set_adjustment(self.randomize_probability_adjustment)
        self.randomize_probability_spin.set_value(10)
        randomize_box.pack_start(self.randomize_probability_spin, False, False, 0)

        randomize_button = Gtk.Button()
        randomize_button.set_image(Gtk.Image.new_from_icon_name("view-refresh", Gtk.IconSize.BUTTON))
        randomize_button.set_tooltip_text("Randomize Instruments")
        randomize_button.connect("clicked", self.randomize_instruments)
        randomize_box.pack_start(randomize_button, False, False, 0)

        autofill_button = Gtk.Button()
        autofill_button.set_image(Gtk.Image.new_from_icon_name("edit-paste", Gtk.IconSize.BUTTON))
        autofill_button.set_tooltip_text("Autofill Pattern")
        autofill_button.connect("clicked", lambda widget: self.autofill_pattern())
        randomize_box.pack_start(autofill_button, False, False, 0)

    def create_preset_selection(self):
        preset_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(preset_box, False, False, 0)

        preset_label = Gtk.Label(label="Preset:")
        preset_box.pack_start(preset_label, False, False, 0)

        self.preset_combo = Gtk.ComboBoxText()
        self.preset_combo.append_text("None")
        self.preset_combo.append_text("Basic Techno")
        self.preset_combo.append_text("Minimal Techno")
        self.preset_combo.append_text("Hard Techno")
        self.preset_combo.set_active(0)
        preset_box.pack_start(self.preset_combo, False, False, 0)

        apply_preset_button = Gtk.Button()
        apply_preset_button.set_image(Gtk.Image.new_from_icon_name("emblem-default", Gtk.IconSize.BUTTON))
        apply_preset_button.set_tooltip_text("Apply Preset")
        apply_preset_button.connect("clicked", self.apply_preset)
        preset_box.pack_start(apply_preset_button, False, False, 0)

    def create_autolevel_button(self):
        autolevel_button = Gtk.Button()
        autolevel_button.set_image(Gtk.Image.new_from_icon_name("audio-volume-high", Gtk.IconSize.BUTTON))
        autolevel_button.set_tooltip_text("Auto Level Samples")
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
            context = label.get_style_context()
            context.add_class(f"instrument-{instrument.lower()}")
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

                reset_button = Gtk.Button()
                reset_button.set_image(Gtk.Image.new_from_icon_name("edit-undo", Gtk.IconSize.SMALL_TOOLBAR))
                reset_button.set_size_request(60, 35)
                reset_button.set_tooltip_text(f"Reset {effect} for {instrument}")
                reset_button.connect('clicked', self.reset_effect, slider, instrument, effect.lower())
                effect_grid.attach_next_to(reset_button, slider, Gtk.PositionType.RIGHT, 1, 1)

        reset_all_button = Gtk.Button()
        reset_all_button.set_image(Gtk.Image.new_from_icon_name("edit-clear-all", Gtk.IconSize.BUTTON))
        reset_all_button.set_tooltip_text("Reset All Effects")
        reset_all_button.connect("clicked", self.reset_all_effects)
        effect_box.pack_start(reset_all_button, False, False, 0)

    def create_groove_controls(self):
        groove_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        self.main_box.pack_start(groove_box, False, False, 0)

        groove_label = Gtk.Label(label="Groove:")
        groove_box.pack_start(groove_label, False, False, 0)

        self.groove_combo = Gtk.ComboBoxText()
        groove_types = ["simple", "stretch", "echoes", "bouncy", "relax"]
        for groove in groove_types:
            self.groove_combo.append_text(groove)
        self.groove_combo.set_active(0)
        groove_box.pack_start(self.groove_combo, False, False, 0)

        groove_button = Gtk.Button()
        groove_button.set_image(Gtk.Image.new_from_icon_name("system-run", Gtk.IconSize.BUTTON))
        groove_button.set_tooltip_text("Apply Groove")
        groove_button.connect("clicked", self.apply_groove)
        groove_box.pack_start(groove_button, False, False, 0)

        reset_groove_button = Gtk.Button()
        reset_groove_button.set_image(Gtk.Image.new_from_icon_name("edit-clear", Gtk.IconSize.BUTTON))
        reset_groove_button.set_tooltip_text("Reset Groove")
        reset_groove_button.connect("clicked", self.reset_groove)
        groove_box.pack_start(reset_groove_button, False, False, 0)

    def create_drummer_to_audio_button(self):
        drummer_button = Gtk.Button()
        drummer_button.set_image(Gtk.Image.new_from_icon_name("audio-x-generic", Gtk.IconSize.BUTTON))
        drummer_button.set_tooltip_text("Add Drummer to Audio")
        drummer_button.connect("clicked", self.add_drummer_to_audio)
        self.main_box.pack_start(drummer_button, False, False, 0)

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
                context.add_class(f"circle-{inst.lower()}")
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
                    context.add_class(f"circle-{instrument.lower()}")
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
        self.update_effect_colors()

    def reset_effect(self, button, slider, instrument, effect):
        slider.set_value(0)
        self.effects[instrument][effect] = 0
        self.update_effect_colors()

    def reset_all_effects(self, widget):
        for instrument in self.instruments:
            for effect in self.effects[instrument]:
                self.effects[instrument][effect] = 0
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(0)
        self.update_effect_colors()

    def reset_genre_fx(self, widget):
        for instrument in self.instruments:
            for effect in self.effects[instrument]:
                self.effects[instrument][effect] = 0
                if effect in self.effect_sliders[instrument]:
                    self.effect_sliders[instrument][effect].set_value(0)
        self.update_effect_colors()

    def apply_effects(self, sound, instrument, export=False):
        sound = self.apply_adsr_to_sound(sound, instrument)
        effects = self.effects[instrument]
        sound_array = pygame.sndarray.array(sound)
        sample_width = sound_array.dtype.itemsize
        channels = 2 if sound_array.ndim == 2 else 1

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
            reverb_segment = audio_segment.reverse().fade_in(int(reverb_amount)).reverse()
            audio_segment = audio_segment.overlay(reverb_segment, position=0)

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
        curve_type = self.sample_params[instrument]['attack_curve']

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
        curve_type = self.sample_params[instrument]['attack_curve']

        # Apply curved envelopes
        if attack_samples > 0:
            if curve_type == 'exponential':
                envelope[:attack_samples] = np.power(np.linspace(0, 1, attack_samples), 2)
            elif curve_type == 'logarithmic':
                envelope[:attack_samples] = np.log1p(np.linspace(0, 9, attack_samples)) / np.log1p(9)
            else:  # linear
                envelope[:attack_samples] = np.linspace(0, 1, attack_samples)

        if decay_samples > 0 and attack_samples < total_samples:
            decay_end = min(attack_samples + decay_samples, total_samples)
            if curve_type == 'exponential':
                envelope[attack_samples:decay_end] = np.power(np.linspace(1, adsr['sustain'], decay_end - attack_samples), 2)
            elif curve_type == 'logarithmic':
                envelope[attack_samples:decay_end] = adsr['sustain'] + (1 - adsr['sustain']) * np.log1p(np.linspace(9, 0, decay_end - attack_samples)) / np.log1p(9)
            else:
                envelope[attack_samples:decay_end] = np.linspace(1, adsr['sustain'], decay_end - attack_samples)

        if sustain_samples > 0 and attack_samples + decay_samples < total_samples:
            sustain_end = min(attack_samples + decay_samples + sustain_samples, total_samples)
            envelope[attack_samples + decay_samples:sustain_end] = adsr['sustain']

        if release_samples > 0 and total_samples - release_samples > 0:
            release_start = max(0, total_samples - release_samples)
            if curve_type == 'exponential':
                envelope[release_start:] = adsr['sustain'] * np.power(np.linspace(1, 0, total_samples - release_start), 2)
            elif curve_type == 'logarithmic':
                envelope[release_start:] = adsr['sustain'] * np.log1p(np.linspace(9, 0, total_samples - release_start)) / np.log1p(9)
            else:
                envelope[release_start:] = np.linspace(adsr['sustain'], 0, total_samples - release_start)

        if is_stereo:
            envelope = np.tile(envelope, (channels, 1)).T
        else:
            envelope = envelope.reshape(-1, 1)

        processed_array = sound_array * envelope
        return pygame.sndarray.make_sound(processed_array.astype(np.int16))

    def adjust_adsr(self, button, instrument, param, delta):
        self.current_adsr[instrument][param] = max(0.01, min(self.current_adsr[instrument][param] + delta, 1.0))
        self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def on_adsr_entry_changed(self, entry, instrument, param):
        try:
            value = float(entry.get_text())
            self.current_adsr[instrument][param] = max(0.01, min(value, 1.0))
            entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")
            self.generate_parametric_samples()
            if self.preview_active[instrument]:
                self.samples[instrument].play()
        except ValueError:
            entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")

    def reset_adsr(self, button, instrument):
        self.current_adsr[instrument] = self.nominal_adsr[instrument].copy()
        for param in ['attack', 'decay', 'sustain', 'release']:
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def randomize_adsr(self, button, instrument):
        for param in ['attack', 'decay', 'sustain', 'release']:
            self.current_adsr[instrument][param] = random.uniform(0.01, 1.0)
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def toggle_preview(self, button, instrument):
        self.preview_active[instrument] = button.get_active()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def swap_sample(self, button, instrument):
        dialog = Gtk.FileChooserDialog(
            title=f"Select sample for {instrument}",
            parent=self,
            action=Gtk.FileChooserAction.OPEN,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Open", Gtk.ResponseType.OK)
        )
        filter_wav = Gtk.FileFilter()
        filter_wav.set_name("WAV files")
        filter_wav.add_pattern("*.wav")
        dialog.add_filter(filter_wav)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            try:
                sound = pygame.mixer.Sound(file_path)
                self.samples[instrument] = sound
                if self.preview_active[instrument]:
                    sound.play()
            except Exception as e:
                print(f"Error loading sample: {e}")
        dialog.destroy()

    def navigate_up(self, button):
        parent_dir = os.path.dirname(self.current_directory)
        if os.path.exists(parent_dir):
            self.current_directory = parent_dir
            self.refresh_sample_browser(None)

    def refresh_sample_browser(self, button):
        self.sample_store.clear()
        self.current_dir_label.set_text(self.current_directory)
        try:
            for item in os.listdir(self.current_directory):
                full_path = os.path.join(self.current_directory, item)
                if os.path.isfile(full_path) and item.lower().endswith(('.wav', '.mp3')):
                    self.sample_store.append([item, full_path])
                elif os.path.isdir(full_path):
                    self.sample_store.append([f"[DIR] {item}", full_path])
        except Exception as e:
            print(f"Error refreshing sample browser: {e}")

    def on_sample_activated(self, treeview, path, column):
        model = treeview.get_model()
        iter = model.get_iter(path)
        name, full_path = model.get(iter, 0, 1)
        if os.path.isfile(full_path) and name.lower().endswith(('.wav', '.mp3')):
            try:
                sound = pygame.mixer.Sound(full_path)
                for inst in self.instruments:
                    if self.swap_buttons[inst].get_state_flags() & Gtk.StateFlags.ACTIVE:
                        self.samples[inst] = sound
                        if self.preview_active[inst]:
                            sound.play()
                        break
            except Exception as e:
                print(f"Error loading sample: {e}")
        elif os.path.isdir(full_path):
            self.current_directory = full_path
            self.refresh_sample_browser(None)

    def on_sample_selected(self, selection):
        model, iter = selection.get_selected()
        if iter:
            name, full_path = model.get(iter, 0, 1)
            if os.path.isfile(full_path) and name.lower().endswith(('.wav', '.mp3')):
                try:
                    sound = pygame.mixer.Sound(full_path)
                    sound.play()
                except Exception as e:
                    print(f"Error playing sample: {e}")

    def load_sample_bank(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Load Sample Bank",
            parent=self,
            action=Gtk.FileChooserAction.OPEN,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Open", Gtk.ResponseType.OK)
        )
        filter_json = Gtk.FileFilter()
        filter_json.set_name("JSON files")
        filter_json.add_pattern("*.json")
        dialog.add_filter(filter_json)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            try:
                with open(file_path, 'r') as f:
                    bank_data = json.load(f)
                for inst in self.instruments:
                    if inst in bank_data and 'sample_path' in bank_data[inst]:
                        sample_path = bank_data[inst]['sample_path']
                        if os.path.exists(sample_path):
                            self.samples[inst] = pygame.mixer.Sound(sample_path)
                            self.sample_params[inst] = bank_data[inst].get('params', self.sample_params[inst])
                            self.current_adsr[inst] = bank_data[inst].get('adsr', self.current_adsr[inst])
                            for param in ['attack', 'decay', 'sustain', 'release']:
                                self.adsr_entries[inst][param].set_text(f"{self.current_adsr[inst][param]:.2f}")
                            for param in ['waveform', 'frequency', 'amplitude', 'duration', 'attack_curve']:
                                if param in self.sample_param_controls[inst]:
                                    if param == 'waveform' or param == 'attack_curve':
                                        types = ['sine', 'square', 'sawtooth', 'noise'] if param == 'waveform' else ['linear', 'exponential', 'logarithmic']
                                        self.sample_param_controls[inst][param].set_active(types.index(self.sample_params[inst][param]))
                                    else:
                                        self.sample_param_controls[inst][param].set_text(str(self.sample_params[inst][param]))
                self.generate_parametric_samples()
            except Exception as e:
                print(f"Error loading sample bank: {e}")
        dialog.destroy()

    def export_sample_bank(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Export Sample Bank",
            parent=self,
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Save", Gtk.ResponseType.OK)
        )
        dialog.set_current_name("sample_bank.json")
        filter_json = Gtk.FileFilter()
        filter_json.set_name("JSON files")
        filter_json.add_pattern("*.json")
        dialog.add_filter(filter_json)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            bank_data = {}
            for inst in self.instruments:
                bank_data[inst] = {
                    'sample_path': f"{inst.lower()}_sample.wav",
                    'params': self.sample_params[inst],
                    'adsr': self.current_adsr[inst]
                }
                try:
                    sound_array = pygame.sndarray.array(self.samples[inst])
                    sf.write(sound_array, bank_data[inst]['sample_path'], 44100, 'PCM_16')
                except Exception as e:
                    print(f"Error saving sample for {inst}: {e}")
            try:
                with open(file_path, 'w') as f:
                    json.dump(bank_data, f, indent=4)
            except Exception as e:
                print(f"Error exporting sample bank: {e}")
        dialog.destroy()

    def load_samples_from_directory(self):
        if not os.path.exists(self.current_directory):
            return
        for inst in self.instruments:
            sample_path = os.path.join(self.current_directory, f"{inst.lower()}_sample.wav")
            if os.path.exists(sample_path):
                try:
                    self.samples[inst] = pygame.mixer.Sound(sample_path)
                except Exception as e:
                    print(f"Error loading sample for {inst}: {e}")

    def load_samples(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Select Samples Directory",
            parent=self,
            action=Gtk.FileChooserAction.SELECT_FOLDER,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Select", Gtk.ResponseType.OK)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            self.current_directory = dialog.get_filename()
            self.load_samples_from_directory()
            self.refresh_sample_browser(None)
        dialog.destroy()

    def save_project(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Save Project",
            parent=self,
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Save", Gtk.ResponseType.OK)
        )
        dialog.set_current_name("drum_sampler_project.json")
        filter_json = Gtk.FileFilter()
        filter_json.set_name("JSON files")
        filter_json.add_pattern("*.json")
        dialog.add_filter(filter_json)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            project_data = {
                'patterns': self.patterns,
                'bpm': self.absolute_bpm,
                'advanced_sequencer_mode': self.advanced_sequencer_mode,
                'effects': self.effects,
                'sample_params': self.sample_params,
                'current_adsr': self.current_adsr
            }
            try:
                with open(file_path, 'w') as f:
                    json.dump(project_data, f, indent=4)
            except Exception as e:
                print(f"Error saving project: {e}")
        dialog.destroy()

    def load_project(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Load Project",
            parent=self,
            action=Gtk.FileChooserAction.OPEN,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Open", Gtk.ResponseType.OK)
        )
        filter_json = Gtk.FileFilter()
        filter_json.set_name("JSON files")
        filter_json.add_pattern("*.json")
        dialog.add_filter(filter_json)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            try:
                with open(file_path, 'r') as f:
                    project_data = json.load(f)
                self.patterns = project_data.get('patterns', self.patterns)
                self.absolute_bpm = project_data.get('bpm', self.absolute_bpm)
                self.bpm_entry.set_text(str(self.absolute_bpm))
                self.advanced_sequencer_mode = project_data.get('advanced_sequencer_mode', self.advanced_sequencer_mode)
                self.sequencer_mode_switch.set_active(self.advanced_sequencer_mode)
                self.effects = project_data.get('effects', self.effects)
                self.sample_params = project_data.get('sample_params', self.sample_params)
                self.current_adsr = project_data.get('current_adsr', self.current_adsr)
                for inst in self.instruments:
                    for effect in self.effects[inst]:
                        if effect in self.effect_sliders[inst]:
                            self.effect_sliders[inst][effect].set_value(self.effects[inst][effect])
                    for param in ['attack', 'decay', 'sustain', 'release']:
                        self.adsr_entries[inst][param].set_text(f"{self.current_adsr[inst][param]:.2f}")
                    for param in ['waveform', 'frequency', 'amplitude', 'duration', 'attack_curve']:
                        if param in self.sample_param_controls[inst]:
                            if param == 'waveform' or param == 'attack_curve':
                                types = ['sine', 'square', 'sawtooth', 'noise'] if param == 'waveform' else ['linear', 'exponential', 'logarithmic']
                                self.sample_param_controls[inst][param].set_active(types.index(self.sample_params[inst][param]))
                            else:
                                self.sample_param_controls[inst][param].set_text(str(self.sample_params[inst][param]))
                self.update_buttons()
                self.generate_parametric_samples()
                self.update_effect_colors()
            except Exception as e:
                print(f"Error loading project: {e}")
        dialog.destroy()

    def export_to_midi(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Export to MIDI",
            parent=self,
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Save", Gtk.ResponseType.OK)
        )
        dialog.set_current_name("drum_pattern.mid")
        filter_midi = Gtk.FileFilter()
        filter_midi.set_name("MIDI files")
        filter_midi.add_pattern("*.mid")
        dialog.add_filter(filter_midi)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            midi = MIDIFile(1)
            midi.addTempo(0, 0, self.absolute_bpm)
            for inst in self.instruments:
                for step, active in enumerate(self.patterns[inst]):
                    if active:
                        time = step * (60 / self.absolute_bpm / 4)
                        midi.addNote(0, 0, self.midi_notes[inst], time, 0.25, 100)
            try:
                with open(file_path, 'wb') as f:
                    midi.write(f)
            except Exception as e:
                print(f"Error exporting MIDI: {e}")
        dialog.destroy()

    def export_advanced_midi(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Export Advanced MIDI",
            parent=self,
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Save", Gtk.ResponseType.OK)
        )
        dialog.set_current_name("advanced_drum_pattern.mid")
        filter_midi = Gtk.FileFilter()
        filter_midi.set_name("MIDI files")
        filter_midi.add_pattern("*.mid")
        dialog.add_filter(filter_midi)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            file_path = dialog.get_filename()
            midi = MIDIFile(1)
            midi.addTempo(0, 0, self.absolute_bpm)
            for inst in self.instruments:
                for step, step_data in enumerate(self.patterns[inst]):
                    if self.advanced_sequencer_mode and step_data['active']:
                        rhythm = self.rhythm_types[step_data['rhythm_type']]
                        notes = rhythm['notes']
                        speed = rhythm['speed']
                        swing = rhythm['swing']
                        for i in range(notes):
                            offset = i * (60 / self.absolute_bpm / 4) * speed
                            if swing and i % 2 == 1:
                                offset += swing * (60 / self.absolute_bpm / 4)
                            time = step * (60 / self.absolute_bpm / 4) + offset
                            midi.addNote(0, 0, self.midi_notes[inst], time, 0.25 * speed, 100)
                    elif not self.advanced_sequencer_mode and step_data:
                        time = step * (60 / self.absolute_bpm / 4)
                        midi.addNote(0, 0, self.midi_notes[inst], time, 0.25, 100)
            try:
                with open(file_path, 'wb') as f:
                    midi.write(f)
            except Exception as e:
                print(f"Error exporting advanced MIDI: {e}")
        dialog.destroy()

    def add_drummer_to_audio(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Select Audio File",
            parent=self,
            action=Gtk.FileChooserAction.OPEN,
            buttons=("Cancel", Gtk.ResponseType.CANCEL, "Open", Gtk.ResponseType.OK)
        )
        filter_audio = Gtk.FileFilter()
        filter_audio.set_name("Audio files")
        filter_audio.add_pattern("*.wav")
        filter_audio.add_pattern("*.mp3")
        dialog.add_filter(filter_audio)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            audio_path = dialog.get_filename()
            try:
                audio = AudioSegment.from_file(audio_path)
                pattern_length = len(self.patterns[self.instruments[0]])
                step_duration = 60 / self.absolute_bpm / 4 * 1000
                total_duration = pattern_length * step_duration
                drum_track = AudioSegment.silent(duration=total_duration)
                for inst in self.instruments:
                    sound = self.apply_effects(self.samples[inst], inst, export=True)
                    sound_array = pygame.sndarray.array(sound)
                    sound_segment = AudioSegment(
                        sound_array.tobytes(),
                        frame_rate=44100,
                        sample_width=sound_array.dtype.itemsize,
                        channels=2 if sound_array.ndim == 2 else 1
                    )
                    if self.advanced_sequencer_mode:
                        for step, step_data in enumerate(self.patterns[inst]):
                            if step_data['active']:
                                rhythm = self.rhythm_types[step_data['rhythm_type']]
                                for i in range(rhythm['notes']):
                                    offset = i * step_duration * rhythm['speed']
                                    if rhythm['swing'] and i % 2 == 1:
                                        offset += rhythm['swing'] * step_duration
                                    position = step * step_duration + offset
                                    drum_track = drum_track.overlay(sound_segment, position=position)
                    else:
                        for step, active in enumerate(self.patterns[inst]):
                            if active:
                                position = step * step_duration
                                drum_track = drum_track.overlay(sound_segment, position=position)
                audio = audio.overlay(drum_track)
                output_dialog = Gtk.FileChooserDialog(
                    title="Save Mixed Audio",
                    parent=self,
                    action=Gtk.FileChooserAction.SAVE,
                    buttons=("Cancel", Gtk.ResponseType.CANCEL, "Save", Gtk.ResponseType.OK)
                )
                output_dialog.set_current_name("mixed_audio.wav")
                filter_wav = Gtk.FileFilter()
                filter_wav.set_name("WAV files")
                filter_wav.add_pattern("*.wav")
                output_dialog.add_filter(filter_wav)
                response = output_dialog.run()
                if response == Gtk.ResponseType.OK:
                    output_path = output_dialog.get_filename()
                    audio.export(output_path, format="wav")
                output_dialog.destroy()
            except Exception as e:
                print(f"Error adding drummer to audio: {e}")
        dialog.destroy()

    def autolevel_samples(self, button):
        max_amplitude = 0
        for inst in self.instruments:
            sound_array = pygame.sndarray.array(self.samples[inst])
            max_amplitude = max(max_amplitude, np.max(np.abs(sound_array)))
        for inst in self.instruments:
            sound_array = pygame.sndarray.array(self.samples[inst])
            if max_amplitude > 0:
                sound_array = (sound_array / max_amplitude * 0.8).astype(np.int16)
            self.samples[inst] = pygame.sndarray.make_sound(sound_array)

    def apply_groove(self, button):
        self.groove_type = self.groove_combo.get_active_text()
        if self.groove_type == "stretch":
            for inst in self.instruments:
                for i in range(len(self.patterns[inst])):
                    if self.advanced_sequencer_mode:
                        if self.patterns[inst][i]['active'] and i % 2 == 1:
                            self.patterns[inst][i]['rhythm_type'] = 'double'
                    else:
                        if self.patterns[inst][i] and i % 2 == 1:
                            self.patterns[inst][i] = 0
                            if i + 1 < len(self.patterns[inst]):
                                self.patterns[inst][i + 1] = 1
        elif self.groove_type == "echoes":
            for inst in self.instruments:
                for i in range(len(self.patterns[inst])):
                    if self.advanced_sequencer_mode:
                        if self.patterns[inst][i]['active'] and random.random() < 0.3:
                            self.patterns[inst][i]['rhythm_type'] = 'echo'
                    else:
                        if self.patterns[inst][i] and random.random() < 0.3:
                            if i + 1 < len(self.patterns[inst]):
                                self.patterns[inst][i + 1] = 1
        elif self.groove_type == "bouncy":
            for inst in self.instruments:
                for i in range(len(self.patterns[inst])):
                    if self.advanced_sequencer_mode:
                        if self.patterns[inst][i]['active'] and i % 4 == 2:
                            self.patterns[inst][i]['rhythm_type'] = 'swing'
                    else:
                        if self.patterns[inst][i] and i % 4 == 2:
                            self.patterns[inst][i] = 0
                            if i + 1 < len(self.patterns[inst]):
                                self.patterns[inst][i + 1] = 1
        elif self.groove_type == "relax":
            for inst in self.instruments:
                for i in range(len(self.patterns[inst])):
                    if self.advanced_sequencer_mode:
                        if self.patterns[inst][i]['active'] and random.random() < 0.5:
                            self.patterns[inst][i]['active'] = False
                    else:
                        if self.patterns[inst][i] and random.random() < 0.5:
                            self.patterns[inst][i] = 0
        self.update_buttons()

    def reset_groove(self, button):
        self.groove_type = "simple"
        self.groove_combo.set_active(0)
        pattern_length = int(self.length_spinbutton.get_value())
        for inst in self.instruments:
            if self.advanced_sequencer_mode:
                for i in range(len(self.patterns[inst])):
                    if self.patterns[inst][i]['active']:
                        self.patterns[inst][i]['rhythm_type'] = 'single'
            else:
                self.patterns[inst] = [0] * pattern_length
        self.update_buttons()

    def apply_auto_fx_for_selected_style(self, button):
        genre = self.preset_genre_combo.get_active_text()
        fx_styles = {
            "House": {
                'Talerz': {'volume': 1.0, 'pitch': 0.5, 'echo': 0.3, 'reverb': 0.5, 'pan': 0.0},
                'Stopa': {'volume': 2.0, 'pitch': 0.0, 'echo': 0.0, 'reverb': 0.2, 'pan': 0.0},
                'Werbel': {'volume': 1.5, 'pitch': 0.2, 'echo': 0.2, 'reverb': 0.4, 'pan': 0.1},
                'TomTom': {'volume': 1.0, 'pitch': -0.5, 'echo': 0.0, 'reverb': 0.3, 'pan': -0.1}
            },
            "Techno": {
                'Talerz': {'volume': 0.8, 'pitch': 1.0, 'echo': 0.5, 'reverb': 0.7, 'pan': 0.2},
                'Stopa': {'volume': 2.5, 'pitch': -0.5, 'echo': 0.0, 'reverb': 0.3, 'pan': 0.0},
                'Werbel': {'volume': 1.8, 'pitch': 0.5, 'echo': 0.4, 'reverb': 0.6, 'pan': -0.2},
                'TomTom': {'volume': 1.2, 'pitch': -1.0, 'echo': 0.2, 'reverb': 0.5, 'pan': 0.1}
            },
            "Drum and Bass": {
                'Talerz': {'volume': 1.0, 'pitch': 1.5, 'echo': 0.6, 'reverb': 0.4, 'pan': 0.3},
                'Stopa': {'volume': 2.0, 'pitch': -0.8, 'echo': 0.1, 'reverb': 0.2, 'pan': 0.0},
                'Werbel': {'volume': 1.7, 'pitch': 0.8, 'echo': 0.5, 'reverb': 0.5, 'pan': -0.3},
                'TomTom': {'volume': 1.0, 'pitch': -0.7, 'echo': 0.3, 'reverb': 0.4, 'pan': 0.2}
            },
            "Ambient": {
                'Talerz': {'volume': 0.5, 'pitch': 0.0, 'echo': 0.8, 'reverb': 1.0, 'pan': 0.0},
                'Stopa': {'volume': 1.0, 'pitch': -1.0, 'echo': 0.5, 'reverb': 0.8, 'pan': 0.0},
                'Werbel': {'volume': 0.8, 'pitch': 0.0, 'echo': 0.7, 'reverb': 0.9, 'pan': 0.0},
                'TomTom': {'volume': 0.7, 'pitch': -0.5, 'echo': 0.6, 'reverb': 0.8, 'pan': 0.0}
            }
        }
        effects = fx_styles.get(genre, fx_styles["House"])
        for inst in self.instruments:
            for effect in self.effects[inst]:
                self.effects[inst][effect] = effects[inst][effect]
                if effect in self.effect_sliders[inst]:
                    self.effect_sliders[inst][effect].set_value(effects[inst][effect])
        self.update_effect_colors()

    def play_pattern(self, button):
        if not self.loop_playing:
            self.loop_playing = True
            self.play_thread = threading.Thread(target=self.play_loop)
            self.play_thread.start()

    def play_loop(self):
        pattern_length = len(self.patterns[self.instruments[0]])
        step_duration = 60 / self.get_next_bpm() / 4
        steps_per_bpm = self.steps_per_bpm
        current_step = 0

        while self.loop_playing:
            for inst in self.instruments:
                if self.performer_mode:
                    if random.random() < 0.1:
                        continue
                if self.advanced_sequencer_mode:
                    step_data = self.patterns[inst][current_step]
                    if step_data['active']:
                        rhythm = self.rhythm_types[step_data['rhythm_type']]
                        for i in range(rhythm['notes']):
                            offset = i * step_duration * rhythm['speed']
                            if rhythm['swing'] and i % 2 == 1:
                                offset += rhythm['swing'] * step_duration
                            GLib.idle_add(self.play_sample_with_effects, inst, offset, current_step)
                else:
                    if self.patterns[inst][current_step]:
                        GLib.idle_add(self.play_sample_with_effects, inst, 0, current_step)
            time.sleep(step_duration)
            current_step = (current_step + 1) % pattern_length
            if current_step % steps_per_bpm == 0:
                self.advance_bpm()
                step_duration = 60 / self.get_next_bpm() / 4

    def play_sample_with_effects(self, instrument, offset, current_step):
        sound = self.apply_effects(self.samples[instrument], instrument)
        sound.play()
        button = self.buttons[instrument][current_step % len(self.patterns[instrument])]
        context = button.get_style_context()
        context.add_class("blink")
        GLib.timeout_add(300, lambda: context.remove_class("blink"))
        return False

    def stop_pattern(self, button):
        self.loop_playing = False
        if self.play_thread:
            self.play_thread.join()
            self.play_thread = None

    def randomize_pattern(self, button):
        pattern_length = len(self.patterns[self.instruments[0]])
        for inst in self.instruments:
            for i in range(pattern_length):
                if self.advanced_sequencer_mode:
                    self.patterns[inst][i]['active'] = random.random() < 0.3
                    if self.patterns[inst][i]['active']:
                        self.patterns[inst][i]['rhythm_type'] = random.choice(list(self.rhythm_types.keys()))
                else:
                    self.patterns[inst][i] = 1 if random.random() < 0.3 else 0
        self.update_buttons()

    def toggle_fullscreen(self, button):
        if self.is_fullscreen:
            self.unfullscreen()
            self.is_fullscreen = False
        else:
            self.fullscreen()
            self.is_fullscreen = True

if __name__ == "__main__":
    import sys
    if platform.system() == "Emscripten":
        async def main():
            app = DrumSamplerApp()
            app.connect("destroy", Gtk.main_quit)
            app.show_all()
            await asyncio.sleep(0)
        asyncio.ensure_future(main())
    else:
        app = DrumSamplerApp()
        app.connect("destroy", Gtk.main_quit)
        app.show_all()
        Gtk.main()