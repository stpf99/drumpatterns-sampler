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
        self.virtual_drummer_mode = False  # New mode for virtual drummer
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
        self.create_virtual_drummer_mode_button()  # New button for virtual drummer mode

    def generate_parametric_samples(self):
        sample_rate = 44100
        for inst in self.instruments:
            params = self.sample_params[inst]
            duration = params['duration']
            t = np.linspace(0, duration, int(sample_rate * duration), False)

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

            signal = self.apply_adsr_to_signal(signal, inst, sample_rate)
            signal = normalize(AudioSegment(
                (signal * 32767).astype(np.int16).tobytes(),
                frame_rate=sample_rate,
                sample_width=2,
                channels=1
            ))
            signal = np.array(signal.get_array_of_samples()).reshape(-1, 1)
            signal = np.hstack((signal, signal))
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

        if attack_samples > 0:
            if curve_type == 'exponential':
                envelope[:attack_samples] = np.power(np.linspace(0, 1, attack_samples), 2)
            elif curve_type == 'logarithmic':
                envelope[:attack_samples] = np.log1p(np.linspace(0, 9, attack_samples)) / np.log1p(9)
            else:
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

            self.sample_param_controls[inst] = {}
            param_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
            param_box.pack_start(Gtk.Label(label="Sample Parameters"), False, False, 0)

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
        @keyframes occurrence-flash {
            0% { background-color: #FFFF00; }
            50% { background-color: #FFFF00; opacity: 0.7; }
            100% { background-color: white; opacity: 1; }
        }
        .blink {
            animation: blink-animation 0.3s linear 1;
        }
        .occurrence {
            animation: occurrence-flash 0.2s linear 1;
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
        @keyframes occurrence-flash {
            0% { background-color: #FFFF00; }
            50% { background-color: #FFFF00; opacity: 0.7; }
            100% { background-color: white; opacity: 1; }
        }
        .blink {
            animation: blink-animation 0.3s linear 1;
        }
        .occurrence {
            animation: occurrence-flash 0.2s linear 1;
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

    def create_virtual_drummer_mode_button(self):
        virtual_drummer_button = Gtk.Button()
        virtual_drummer_button.set_image(Gtk.Image.new_from_icon_name("system-users", Gtk.IconSize.BUTTON))
        virtual_drummer_button.set_tooltip_text("Toggle Virtual Drummer Mode")
        virtual_drummer_button.connect("clicked", self.toggle_virtual_drummer_mode)
        self.main_box.pack_start(virtual_drummer_button, False, False, 0)

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

    def toggle_virtual_drummer_mode(self, button):
        self.virtual_drummer_mode = not self.virtual_drummer_mode
        if self.virtual_drummer_mode:
            self.stop_pattern(None)
            self.play_thread = threading.Thread(target=self.virtual_drummer_loop)
            self.play_thread.start()
            button.set_label("Stop Virtual Drummer")
        else:
            self.stop_pattern(None)
            button.set_label("Start Virtual Drummer")

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

        if attack_samples > 0:
            if curve_type == 'exponential':
                envelope[:attack_samples] = np.power(np.linspace(0, 1, attack_samples), 2)
            elif curve_type == 'logarithmic':
                envelope[:attack_samples] = np.log1p(np.linspace(0, 9, attack_samples)) / np.log1p(9)
            else:
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
            envelope = np.vstack((envelope, envelope)).T
        else:
            envelope = envelope.reshape(-1, 1)

        processed_array = sound_array * envelope
        return pygame.sndarray.make_sound(processed_array.astype(np.int16))

    def load_samples_from_directory(self):
        sample_dir = self.current_directory
        if not os.path.exists(sample_dir):
            return
        for inst in self.instruments:
            sample_path = os.path.join(sample_dir, f"{inst.lower()}.wav")
            if os.path.exists(sample_path):
                try:
                    audio_segment = AudioSegment.from_file(sample_path)
                    audio_segment = audio_segment.set_channels(2)
                    audio_segment = normalize(audio_segment)
                    samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 2)
                    self.samples[inst] = pygame.sndarray.make_sound(samples.astype(np.int16))
                except Exception as e:
                    print(f"Error loading {sample_path}: {e}")

    def load_samples(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Select Sample Directory",
            action=Gtk.FileChooserAction.SELECT_FOLDER,
            buttons=("Select", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            self.current_directory = dialog.get_filename()
            self.current_dir_label.set_text(self.current_directory)
            self.load_samples_from_directory()
            self.refresh_sample_browser(None)
        dialog.destroy()

    def refresh_sample_browser(self, widget):
        self.sample_store.clear()
        for root, _, files in os.walk(self.current_directory):
            for file in files:
                if file.lower().endswith(('.wav', '.mp3', '.ogg')):
                    self.sample_store.append([file, os.path.join(root, file)])

    def on_sample_selected(self, selection):
        model, treeiter = selection.get_selected()
        if treeiter is not None:
            sample_path = model[treeiter][1]
            try:
                sound = pygame.mixer.Sound(sample_path)
                sound.play()
            except Exception as e:
                print(f"Error playing sample {sample_path}: {e}")

    def on_sample_activated(self, treeview, path, column):
        sample_path = self.sample_store[path][1]
        for inst in self.instruments:
            if self.swap_buttons[inst].get_state_flags() & Gtk.StateFlags.ACTIVE:
                try:
                    audio_segment = AudioSegment.from_file(sample_path)
                    audio_segment = audio_segment.set_channels(2)
                    audio_segment = normalize(audio_segment)
                    samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 2)
                    self.samples[inst] = pygame.sndarray.make_sound(samples.astype(np.int16))
                    self.swap_buttons[inst].set_active(False)
                except Exception as e:
                    print(f"Error loading sample {sample_path} for {inst}: {e}")

    def navigate_up(self, widget):
        parent_dir = os.path.dirname(self.current_directory)
        if parent_dir != self.current_directory:
            self.current_directory = parent_dir
            self.current_dir_label.set_text(self.current_directory)
            self.refresh_sample_browser(None)

    def swap_sample(self, button, instrument):
        button.set_active(not button.get_active())

    def play_pattern(self, widget):
        if not self.loop_playing:
            self.loop_playing = True
            self.play_thread = threading.Thread(target=self.play_loop)
            self.play_thread.start()

    def stop_pattern(self, widget):
        self.loop_playing = False
        if self.play_thread:
            self.play_thread.join()
            self.play_thread = None

    def play_loop(self):
        pattern_length = int(self.length_spinbutton.get_value())
        step_duration = 60.0 / (self.get_next_bpm() * 4)
        steps_played = 0

        while self.loop_playing:
            for step in range(pattern_length):
                if not self.loop_playing:
                    break
                current_bpm = self.get_next_bpm()
                step_duration = 60.0 / (current_bpm * 4)
                for instrument in self.instruments:
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            sound = self.apply_effects(self.samples[instrument], instrument)
                            for i in range(rhythm['notes']):
                                swing_offset = rhythm['swing'] * step_duration * i
                                sound.play()
                                time.sleep(step_duration * rhythm['speed'] + swing_offset)
                            GLib.idle_add(self.highlight_button, instrument, step)
                    else:
                        if self.patterns[instrument][step]:
                            sound = self.apply_effects(self.samples[instrument], instrument)
                            sound.play()
                            GLib.idle_add(self.highlight_button, instrument, step)
                time.sleep(step_duration)
                steps_played += 1
                if steps_played >= self.steps_per_bpm:
                    self.advance_bpm()
                    steps_played = 0

    def highlight_button(self, instrument, step):
        button = self.buttons[instrument][step]
        context = button.get_style_context()
        context.add_class("occurrence")
        GLib.timeout_add(200, self.remove_highlight, button, "occurrence")

    def remove_highlight(self, button, class_name):
        context = button.get_style_context()
        context.remove_class(class_name)
        return False

    def virtual_drummer_loop(self):
        pattern_length = int(self.length_spinbutton.get_value())
        improvisation_count = 0
        max_improvisations = 4  # Number of pattern changes before stopping

        while self.virtual_drummer_mode and improvisation_count < max_improvisations:
            # Randomize pattern
            self.randomize_pattern(None)
            # Apply groove
            self.apply_groove(None)
            # Adjust BPM dynamically
            self.perfect_tempo_bpm(None)
            # Play for a few loops
            loops = random.randint(2, 4)
            for _ in range(loops):
                if not self.virtual_drummer_mode:
                    break
                for step in range(pattern_length):
                    if not self.virtual_drummer_mode:
                        break
                    current_bpm = self.get_next_bpm()
                    step_duration = 60.0 / (current_bpm * 4)
                    for instrument in self.instruments:
                        if self.advanced_sequencer_mode:
                            step_data = self.patterns[instrument][step]
                            if step_data['active']:
                                rhythm = self.rhythm_types[step_data['rhythm_type']]
                                sound = self.apply_effects(self.samples[instrument], instrument)
                                for i in range(rhythm['notes']):
                                    swing_offset = rhythm['swing'] * step_duration * i
                                    sound.play()
                                    time.sleep(step_duration * rhythm['speed'] + swing_offset)
                                GLib.idle_add(self.highlight_button, instrument, step)
                        else:
                            if self.patterns[instrument][step]:
                                sound = self.apply_effects(self.samples[instrument], instrument)
                                sound.play()
                                GLib.idle_add(self.highlight_button, instrument, step)
                    time.sleep(step_duration)
            improvisation_count += 1
            # Randomly adjust effects
            for instrument in self.instruments:
                for effect in ['volume', 'pitch', 'echo', 'reverb', 'pan']:
                    if random.random() < 0.3:
                        self.effects[instrument][effect] = random.uniform(-2, 2)
                        if effect in self.effect_sliders[instrument]:
                            GLib.idle_add(self.effect_sliders[instrument][effect].set_value, self.effects[instrument][effect])
            self.update_effect_colors()
            # Randomly adjust BPM percentages
            percentages = [random.randint(90, 110) for _ in range(4)]
            self.dynamic_bpm_entry.set_text(','.join(map(str, percentages)))
            GLib.idle_add(self.apply_dynamic_bpm, None)
        self.virtual_drummer_mode = False
        GLib.idle_add(self.update_drummer_button_label)

    def update_drummer_button_label(self):
        for child in self.main_box.get_children():
            if isinstance(child, Gtk.Button) and child.get_tooltip_text() == "Toggle Virtual Drummer Mode":
                child.set_label("Start Virtual Drummer")
        return False

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

    def apply_groove(self, widget):
        groove_type = self.groove_combo.get_active_text()
        pattern_length = int(self.length_spinbutton.get_value())
        self.groove_type = groove_type

        for inst in self.instruments:
            if groove_type == "stretch":
                for i in range(pattern_length):
                    if i % 2 == 0 and self.patterns[inst][i]['active'] if self.advanced_sequencer_mode else self.patterns[inst][i]:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['rhythm_type'] = 'double'
                        else:
                            if i + 1 < pattern_length:
                                self.patterns[inst][i + 1] = 1
            elif groove_type == "echoes":
                for i in range(pattern_length):
                    if self.patterns[inst][i]['active'] if self.advanced_sequencer_mode else self.patterns[inst][i]:
                        self.effects[inst]['echo'] = 0.5
                        if 'echo' in self.effect_sliders[inst]:
                            self.effect_sliders[inst]['echo'].set_value(0.5)
            elif groove_type == "bouncy":
                for i in range(pattern_length):
                    if i % 4 == 0 and (self.patterns[inst][i]['active'] if self.advanced_sequencer_mode else self.patterns[inst][i]):
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['rhythm_type'] = 'swing'
                        else:
                            if i + 1 < pattern_length:
                                self.patterns[inst][i + 1] = 1
            elif groove_type == "relax":
                for i in range(pattern_length):
                    if random.random() < 0.2:
                        if self.advanced_sequencer_mode:
                            self.patterns[inst][i]['active'] = False
                        else:
                            self.patterns[inst][i] = 0
        self.update_buttons()
        self.update_effect_colors()

    def reset_groove(self, widget):
        self.groove_type = 'simple'
        for inst in self.instruments:
            for effect in ['echo']:
                self.effects[inst][effect] = 0
                if effect in self.effect_sliders[inst]:
                    self.effect_sliders[inst][effect].set_value(0)
        self.update_buttons()
        self.update_effect_colors()

    def apply_auto_fx_for_selected_style(self, widget):
        genre = self.preset_genre_combo.get_active_text()
        fx_settings = {
            'House': {'volume': 0.5, 'pitch': 0.0, 'echo': 0.3, 'reverb': 0.2, 'pan': 0.0},
            'Techno': {'volume': 0.7, 'pitch': -0.5, 'echo': 0.5, 'reverb': 0.4, 'pan': 0.0},
            'Drum and Bass': {'volume': 0.8, 'pitch': 0.5, 'echo': 0.2, 'reverb': 0.3, 'pan': 0.0},
            'Ambient': {'volume': 0.3, 'pitch': 0.0, 'echo': 0.4, 'reverb': 0.6, 'pan': 0.0}
        }
        settings = fx_settings.get(genre, {'volume': 0.0, 'pitch': 0.0, 'echo': 0.0, 'reverb': 0.0, 'pan': 0.0})
        for inst in self.instruments:
            for effect, value in settings.items():
                self.effects[inst][effect] = value
                if effect in self.effect_sliders[inst]:
                    self.effect_sliders[inst][effect].set_value(value)
        self.update_effect_colors()

    def save_project(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Save Project",
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Save", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("drum_pattern.json")
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            project_data = {
                'patterns': self.patterns,
                'effects': self.effects,
                'bpm': self.absolute_bpm,
                'dynamic_bpm': self.dynamic_bpm_entry.get_text(),
                'groove': self.groove_type,
                'pattern_length': int(self.length_spinbutton.get_value()),
                'advanced_sequencer_mode': self.advanced_sequencer_mode,
                'adsr': self.current_adsr,
                'sample_params': self.sample_params
            }
            with open(filename, 'w') as f:
                json.dump(project_data, f, indent=4)
        dialog.destroy()

    def load_project(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Load Project",
            action=Gtk.FileChooserAction.OPEN,
            buttons=("Open", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            with open(filename, 'r') as f:
                project_data = json.load(f)
            self.patterns = project_data['patterns']
            self.effects = project_data['effects']
            self.absolute_bpm = project_data['bpm']
            self.dynamic_bpm_entry.set_text(project_data['dynamic_bpm'])
            self.groove_type = project_data['groove']
            self.length_spinbutton.set_value(project_data['pattern_length'])
            self.advanced_sequencer_mode = project_data['advanced_sequencer_mode']
            self.sequencer_mode_switch.set_active(self.advanced_sequencer_mode)
            self.current_adsr = project_data.get('adsr', self.current_adsr)
            self.sample_params = project_data.get('sample_params', self.sample_params)
            self.patterns = self.advanced_patterns if self.advanced_sequencer_mode else self.simple_patterns
            for inst in self.instruments:
                for effect in self.effects[inst]:
                    if effect in self.effect_sliders[inst]:
                        self.effect_sliders[inst][effect].set_value(self.effects[inst][effect])
                for param in ['attack', 'decay', 'sustain', 'release']:
                    self.adsr_entries[inst][param].set_text(f"{self.current_adsr[inst][param]:.2f}")
                for param in ['waveform', 'frequency', 'amplitude', 'duration', 'attack_curve']:
                    if param == 'waveform' or param == 'attack_curve':
                        self.sample_param_controls[inst][param].set_active(
                            ['sine', 'square', 'sawtooth', 'noise'].index(self.sample_params[inst][param])
                            if param == 'waveform' else
                            ['linear', 'exponential', 'logarithmic'].index(self.sample_params[inst][param])
                        )
                    elif param == 'amplitude':
                        self.sample_param_controls[inst][param].set_value(self.sample_params[inst][param])
                    else:
                        self.sample_param_controls[inst][param].set_text(str(self.sample_params[inst][param]))
            self.bpm_entry.set_text(str(self.absolute_bpm))
            self.apply_dynamic_bpm(None)
            self.update_buttons()
            self.update_effect_colors()
            self.generate_parametric_samples()
        dialog.destroy()

    def export_to_midi(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export MIDI",
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Save", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("drum_pattern.mid")
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            midi = MIDIFile(1)
            track = 0
            channel = 9
            time = 0
            midi.addTempo(track, time, self.absolute_bpm)
            pattern_length = int(self.length_spinbutton.get_value())
            step_duration = 60.0 / (self.absolute_bpm * 4)

            for step in range(pattern_length):
                for instrument in self.instruments:
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            for i in range(rhythm['notes']):
                                swing_offset = rhythm['swing'] * step_duration * i
                                midi.addNote(
                                    track, channel, self.midi_notes[instrument],
                                    time + (step_duration * i * rhythm['speed']) + swing_offset,
                                    step_duration * rhythm['speed'],
                                    int(127 * (1 + self.effects[instrument]['volume'] / 5))
                                )
                    else:
                        if self.patterns[instrument][step]:
                            midi.addNote(
                                track, channel, self.midi_notes[instrument], time,
                                step_duration, int(127 * (1 + self.effects[instrument]['volume'] / 5))
                            )
                time += step_duration
            with open(filename, "wb") as output_file:
                midi.write(output_file)
        dialog.destroy()

    def export_advanced_midi(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export Advanced MIDI",
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Save", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("drum_pattern_advanced.mid")
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            midi = MIDIFile(1)
            track = 0
            channel = 9
            time = 0
            midi.addTempo(track, time, self.absolute_bpm)
            pattern_length = int(self.length_spinbutton.get_value())
            step_duration = 60.0 / (self.absolute_bpm * 4)

            for step in range(pattern_length):
                current_bpm = self.get_next_bpm()
                step_duration = 60.0 / (current_bpm * 4)
                for instrument in self.instruments:
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            for i in range(rhythm['notes']):
                                swing_offset = rhythm['swing'] * step_duration * i
                                velocity = int(127 * (1 + self.effects[instrument]['volume'] / 5))
                                if step_data['rhythm_type'] == 'accent':
                                    velocity = min(127, velocity + 20)
                                midi.addNote(
                                    track, channel, self.midi_notes[instrument],
                                    time + (step_duration * i * rhythm['speed']) + swing_offset,
                                    step_duration * rhythm['speed'], velocity
                                )
                    else:
                        if self.patterns[instrument][step]:
                            midi.addNote(
                                track, channel, self.midi_notes[instrument], time,
                                step_duration, int(127 * (1 + self.effects[instrument]['volume'] / 5))
                            )
                time += step_duration
                if step % self.steps_per_bpm == self.steps_per_bpm - 1:
                    self.advance_bpm()
            with open(filename, "wb") as output_file:
                midi.write(output_file)
        dialog.destroy()

    def add_drummer_to_audio(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export Audio",
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Save", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("drum_pattern.wav")
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            pattern_length = int(self.length_spinbutton.get_value())
            step_duration = 60.0 / (self.absolute_bpm * 4)
            total_duration = pattern_length * step_duration * 1000
            combined = AudioSegment.silent(duration=total_duration)
            sample_rate = 44100

            for step in range(pattern_length):
                for instrument in self.instruments:
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            sound = self.apply_effects(self.samples[instrument], instrument, export=True)
                            for i in range(rhythm['notes']):
                                swing_offset = rhythm['swing'] * step_duration * 1000
                                position = (step * step_duration * 1000) + (i * step_duration * rhythm['speed'] * 1000) + swing_offset
                                combined = combined.overlay(sound, position=position)
                    else:
                        if self.patterns[instrument][step]:
                            sound = self.apply_effects(self.samples[instrument], instrument, export=True)
                            position = step * step_duration * 1000
                            combined = combined.overlay(sound, position=position)
            combined = normalize(combined)
            combined.export(filename, format="wav")
        dialog.destroy()

    def autolevel_samples(self, widget):
        for instrument in self.instruments:
            sound_array = pygame.sndarray.array(self.samples[instrument])
            audio_segment = AudioSegment(
                sound_array.tobytes(),
                frame_rate=44100,
                sample_width=sound_array.dtype.itemsize,
                channels=2 if sound_array.ndim == 2 else 1
            )
            audio_segment = normalize(audio_segment)
            samples = np.array(audio_segment.get_array_of_samples())
            if sound_array.ndim == 2:
                samples = samples.reshape(-1, 2)
            else:
                samples = samples.reshape(-1, 1)
            self.samples[instrument] = pygame.sndarray.make_sound(samples.astype(np.int16))

    def toggle_fullscreen(self, widget):
        if self.is_fullscreen:
            self.unfullscreen()
            self.is_fullscreen = False
        else:
            self.fullscreen()
            self.is_fullscreen = True

    def adjust_adsr(self, button, instrument, param, delta):
        current_value = self.current_adsr[instrument][param]
        new_value = max(0.0, min(current_value + delta, 1.0))
        self.current_adsr[instrument][param] = new_value
        self.adsr_entries[instrument][param].set_text(f"{new_value:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def on_adsr_entry_changed(self, entry, instrument, param):
        try:
            value = float(entry.get_text())
            value = max(0.0, min(value, 1.0))
            self.current_adsr[instrument][param] = value
            entry.set_text(f"{value:.2f}")
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
            self.current_adsr[instrument][param] = random.uniform(0.1, 0.8)
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def toggle_preview(self, button, instrument):
        self.preview_active[instrument] = button.get_active()
        if self.preview_active[instrument]:
            self.samples[instrument].play()

    def load_sample_bank(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Load Sample Bank",
            action=Gtk.FileChooserAction.SELECT_FOLDER,
            buttons=("Select", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            self.current_directory = dialog.get_filename()
            self.current_dir_label.set_text(self.current_directory)
            self.load_samples_from_directory()
            self.refresh_sample_browser(None)
        dialog.destroy()

    def export_sample_bank(self, button):
        dialog = Gtk.FileChooserDialog(
            title="Export Sample Bank",
            action=Gtk.FileChooserAction.SELECT_FOLDER,
            buttons=("Select", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            export_dir = dialog.get_filename()
            for inst in self.instruments:
                sound_array = pygame.sndarray.array(self.samples[inst])
                audio_segment = AudioSegment(
                    sound_array.tobytes(),
                    frame_rate=44100,
                    sample_width=sound_array.dtype.itemsize,
                    channels=2 if sound_array.ndim == 2 else 1
                )
                audio_segment.export(os.path.join(export_dir, f"{inst.lower()}.wav"), format="wav")
        dialog.destroy()

if __name__ == "__main__":
    win = DrumSamplerApp()
    win.connect("destroy", Gtk.main_quit)
    win.show_all()
    Gtk.main()