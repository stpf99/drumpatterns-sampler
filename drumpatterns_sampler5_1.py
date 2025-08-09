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
import cairo
from scipy.interpolate import interp1d
import asyncio
gi.require_version('Gtk', '3.0')
from gi.repository import Gtk, GLib, Gdk
import warnings
warnings.filterwarnings("ignore", category=SyntaxWarning)
import sqlite3
import librosa
import soundfile as sf

class WaveformEditorWindow(Gtk.Window):
    def __init__(self, parent, instrument, sample_params, current_adsr, on_save_callback):
        Gtk.Window.__init__(self, title=f"Waveform Editor - {instrument}")
        self.set_default_size(800, 400)
        self.instrument = instrument
        self.sample_params = sample_params
        self.current_adsr = current_adsr
        self.on_save_callback = on_save_callback
        self.sample_rate = 44100

        self.box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10)
        self.add(self.box)

        self.drawing_area = Gtk.DrawingArea()
        self.drawing_area.set_size_request(700, 300)
        self.drawing_area.connect("draw", self.on_draw)
        self.drawing_area.connect("button-press-event", self.on_button_press)
        self.drawing_area.connect("button-release-event", self.on_button_release)
        self.drawing_area.connect("motion-notify-event", self.on_motion)
        self.drawing_area.set_events(Gdk.EventMask.BUTTON_PRESS_MASK |
                                     Gdk.EventMask.BUTTON_RELEASE_MASK |
                                     Gdk.EventMask.POINTER_MOTION_MASK)
        self.box.pack_start(self.drawing_area, True, True, 0)

        button_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        self.box.pack_start(button_box, False, False, 0)

        self.edit_button = Gtk.ToggleButton(label="Edit")
        self.edit_button.connect("toggled", self.on_tool_toggled)
        button_box.pack_start(self.edit_button, False, False, 0)

        play_button = Gtk.Button(label="Play")
        play_button.connect("clicked", self.on_play)
        button_box.pack_start(play_button, False, False, 0)

        save_button = Gtk.Button(label="Save")
        save_button.connect("clicked", self.on_save)
        button_box.pack_start(save_button, False, False, 0)

        self.waveform = self.generate_waveform()
        self.original_waveform = self.waveform.copy()
        self.control_points = []
        self.dragging_point = None
        self.current_tool = None
        self.view_start = 0
        self.view_end = len(self.waveform)
        self.update_control_points()

    def generate_waveform(self):
        params = self.sample_params[self.instrument]
        duration = params['duration']
        t = np.linspace(0, duration, int(self.sample_rate * duration), False)

        if params['waveform'] == 'sine':
            waveform = params['amplitude'] * np.sin(2 * np.pi * params['frequency'] * t)
        elif params['waveform'] == 'square':
            waveform = params['amplitude'] * np.sign(np.sin(2 * np.pi * params['frequency'] * t))
        elif params['waveform'] == 'sawtooth':
            waveform = params['amplitude'] * (2 * (t * params['frequency'] - np.floor(0.5 + t * params['frequency'])))
        elif params['waveform'] == 'noise':
            waveform = params['amplitude'] * np.random.normal(0, 1, len(t))
        else:
            waveform = np.zeros(len(t))

        waveform = self.apply_adsr_to_signal(waveform)
        waveform /= np.max(np.abs(waveform))
        return waveform

    def apply_adsr_to_signal(self, signal):
        adsr = self.current_adsr[self.instrument]
        total_samples = len(signal)
        attack_samples = int(adsr['attack'] * self.sample_rate)
        decay_samples = int(adsr['decay'] * self.sample_rate)
        release_samples = int(adsr['release'] * self.sample_rate)
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
        curve_type = self.sample_params[self.instrument]['attack_curve']

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

    def on_draw(self, widget, cr):
        cr.set_source_rgb(1, 1, 1)
        cr.paint()

        width = self.drawing_area.get_allocated_width()
        height = self.drawing_area.get_allocated_height()

        cr.set_source_rgb(0.7, 0.7, 0.7)
        cr.move_to(0, height / 2)
        cr.line_to(width, height / 2)
        cr.stroke()

        cr.set_source_rgb(0, 0, 0)
        cr.set_line_width(2)

        if len(self.waveform) > 1:
            cr.move_to(0, height / 2)
            for i in range(width):
                x = i
                index = int(self.view_start + (i / width) * (self.view_end - self.view_start))
                if index < len(self.waveform):
                    y = height / 2 - (self.waveform[index] * height / 2)
                    cr.line_to(x, y)
            cr.stroke()

        for x, y in self.control_points:
            cr.set_source_rgb(1, 0, 0)
            cr.arc(x, y, 5, 0, 2 * np.pi)
            cr.fill()

    def find_nearest_point(self, x, y):
        if not self.control_points:
            return None
        distances = [(i, (p[0] - x) ** 2 + (p[1] - y) ** 2) for i, p in enumerate(self.control_points)]
        nearest = min(distances, key=lambda d: d[1])
        return nearest[0] if nearest[1] < 100 else None

    def update_waveform(self, edited_point_index):
        if len(self.control_points) < 2:
            return

        width = self.drawing_area.get_allocated_width()
        height = self.drawing_area.get_allocated_height()

        x_points = [int(self.view_start + (p[0] / width) * (self.view_end - self.view_start)) for p in self.control_points]
        y_points = [(height / 2 - p[1]) / (height / 2) for p in self.control_points]

        influence_range = 1000
        start_index = max(0, x_points[edited_point_index] - influence_range)
        end_index = min(len(self.waveform), x_points[edited_point_index] + influence_range)

        local_x_points = [x for x in x_points if start_index <= x <= end_index]
        local_y_points = [y_points[x_points.index(x)] for x in local_x_points]

        if len(local_x_points) > 1:
            f = interp1d(local_x_points, local_y_points, kind='cubic', fill_value='extrapolate')
            local_indices = np.arange(start_index, end_index)
            new_local_waveform = f(local_indices)

            transition = np.linspace(0, 1, influence_range)
            new_local_waveform[:influence_range] = (transition * new_local_waveform[:influence_range] +
                                                    (1 - transition) * self.waveform[start_index:start_index + influence_range])
            new_local_waveform[-influence_range:] = (transition[::-1] * new_local_waveform[-influence_range:] +
                                                     (1 - transition[::-1]) * self.waveform[end_index - influence_range:end_index])

            self.waveform[start_index:end_index] = new_local_waveform

    def update_control_points(self):
        width = self.drawing_area.get_allocated_width()
        height = self.drawing_area.get_allocated_height()
        self.control_points = []
        num_points = 20
        for i in range(num_points):
            x = int(i * width / (num_points - 1))
            index = int(self.view_start + (x / width) * (self.view_end - self.view_start))
            if index < len(self.waveform):
                y = height / 2 - (self.waveform[index] * height / 2)
                self.control_points.append((x, y))

    def on_tool_toggled(self, button):
        self.current_tool = "edit" if button.get_active() else None

    def on_button_press(self, widget, event):
        if self.current_tool == "edit":
            self.dragging_point = self.find_nearest_point(event.x, event.y)

    def on_button_release(self, widget, event):
        if self.current_tool == "edit" and self.dragging_point is not None:
            self.update_waveform(self.dragging_point)
            self.dragging_point = None
        self.drawing_area.queue_draw()

    def on_motion(self, widget, event):
        if self.current_tool == "edit" and self.dragging_point is not None:
            x, y = event.x, event.y
            self.control_points[self.dragging_point] = (x, y)
            self.drawing_area.queue_draw()

    def on_play(self, widget):
        sound = self.create_pygame_sound()
        sound.play()

    def on_save(self, widget):
        sound = self.create_pygame_sound()
        self.on_save_callback(self.instrument, self.waveform, sound)
        self.destroy()

    def create_pygame_sound(self):
        audio_segment = AudioSegment(
            (self.waveform * 32767).astype(np.int16).tobytes(),
            frame_rate=self.sample_rate,
            sample_width=2,
            channels=1
        )
        audio_segment = normalize(audio_segment)
        samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 1)
        samples = np.hstack((samples, samples))
        return pygame.sndarray.make_sound(samples.astype(np.int16))

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
        self.virtual_drummer_mode = False
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
        self.waveforms = {}
        self.effects = {inst: {'volume': 0, 'pitch': 0, 'echo': 0, 'reverb': 0, 'pan': 0} for inst in self.instruments}
        self.last_button_pressed = None
        self.rhythm_types = {
            'single': {'notes': 1, 'speed': 1.0, 'swing': 0.0},
            'double': {'notes': 2, 'speed': 0.5, 'swing': 0.0},
            'burst': {'notes': 3, 'speed': 0.25, 'swing': 0.0},
            'swing': {'notes': 2, 'speed': 0.5, 'swing': 0.2},
            'accent': {'notes': 1, 'speed': 1.0, 'swing': 0.0}
        }
        self.sample_params = {
            'Talerz': {'waveform': 'noise', 'frequency': 8000, 'amplitude': 0.8, 'duration': 1.0, 'attack_curve': 'exponential'},
            'Stopa': {'waveform': 'sine', 'frequency': 100, 'amplitude': 1.0, 'duration': 0.3, 'attack_curve': 'linear'},
            'Werbel': {'waveform': 'noise', 'frequency': 4000, 'amplitude': 0.9, 'duration': 0.4, 'attack_curve': 'exponential'},
            'TomTom': {'waveform': 'sine', 'frequency': 200, 'amplitude': 0.9, 'duration': 0.5, 'attack_curve': 'linear'}
        }
        self.nominal_adsr = {
            'Talerz': {'attack': 0.01, 'decay': 0.1, 'sustain': 0.8, 'release': 0.6},
            'Stopa': {'attack': 0.01, 'decay': 0.2, 'sustain': 0.3, 'release': 0.1},
            'Werbel': {'attack': 0.02, 'decay': 0.2, 'sustain': 0.4, 'release': 0.3},
            'TomTom': {'attack': 0.03, 'decay': 0.3, 'sustain': 0.5, 'release': 0.4}
        }
        self.current_adsr = {inst: self.nominal_adsr[inst].copy() for inst in self.instruments}
        self.preview_active = {inst: False for inst in self.instruments}
        self.swap_buttons = {}
        self.wave_editor_buttons = {}

        # Load or generate samples
        self.load_samples_from_directory()
        if not self.samples:
            self.generate_parametric_samples()

        # UI setup
        self.add_css()
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
        self.create_virtual_drummer_mode_button()

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
            self.waveforms[inst] = signal[:, 0] / 32767.0

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

            wave_editor_btn = Gtk.Button()
            wave_editor_btn.set_image(Gtk.Image.new_from_icon_name("gtk-edit", Gtk.IconSize.SMALL_TOOLBAR))
            wave_editor_btn.set_size_request(int(20 * self.scale_factor), int(20 * self.scale_factor))
            wave_editor_btn.set_tooltip_text("Open Waveform Editor")
            wave_editor_btn.connect("clicked", self.open_waveform_editor, inst)
            btn_box.pack_start(wave_editor_btn, False, False, 0)
            self.wave_editor_buttons[inst] = wave_editor_btn

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

    def open_waveform_editor(self, button, instrument):
        editor = WaveformEditorWindow(
            self, instrument, self.sample_params, self.current_adsr, self.update_sample_from_waveform
        )
        editor.show_all()

    def update_sample_from_waveform(self, instrument, waveform, sound):
        self.waveforms[instrument] = waveform
        self.samples[instrument] = sound
        if self.preview_active[instrument]:
            self.samples[instrument].play()

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
        css_file_path = os.path.join(os.path.dirname(__file__), "styles.css")
        try:
            if os.path.exists(css_file_path):
                with open(css_file_path, 'r', encoding='utf-8') as f:
                    css_content = f.read()
                print("CSS file path:", css_file_path)
                print("CSS file content:", repr(css_content))
                print("CSS file content (lines):", css_content.splitlines())
                css_data = css_content.encode('utf-8')
                print("Encoded CSS length:", len(css_data))
                css_provider.load_from_path(css_file_path)
            else:
                print(f"CSS file not found: {css_file_path}")
                css = ".instrument-tomtom{color:#FFAA00;}"
                print("Using fallback CSS:", repr(css))
                css_data = css.encode('utf-8')
                css_provider.load_from_data(css_data)
            Gtk.StyleContext.add_provider_for_screen(
                Gdk.Screen.get_default(),
                css_provider,
                Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION
            )
        except GLib.GError as e:
            print(f"Error loading CSS: {e}")
            print("Attempting minimal CSS fallback...")
            try:
                css = ".instrument-tomtom{color:#FFAA00;}"
                print("Fallback CSS:", repr(css))
                css_provider.load_from_data(css.encode('utf-8'))
                Gtk.StyleContext.add_provider_for_screen(
                    Gdk.Screen.get_default(),
                    css_provider,
                    Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION
                )
            except GLib.GError as e2:
                print(f"Error loading fallback CSS: {e2}")
                raise


    def create_groove_controls(self):
        groove_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        groove_label = Gtk.Label(label="Groove:")
        groove_box.pack_start(groove_label, False, False, 0)
        self.groove_combo = Gtk.ComboBoxText()
        groove_types = ['simple', 'stretch', 'echoes', 'bouncy', 'relax']
        for gtype in groove_types:
            self.groove_combo.append_text(gtype)
        self.groove_combo.set_active(0)
        self.groove_combo.connect("changed", self.apply_groove)
        groove_box.pack_start(self.groove_combo, False, False, 0)

        reset_groove_btn = Gtk.Button()
        reset_groove_btn.set_image(Gtk.Image.new_from_icon_name("edit-undo", Gtk.IconSize.SMALL_TOOLBAR))
        reset_groove_btn.set_tooltip_text("Reset Groove")
        reset_groove_btn.connect("clicked", self.reset_groove)
        groove_box.pack_start(reset_groove_btn, False, False, 0)

        self.main_box.pack_start(groove_box, False, False, 0)

    def create_drummer_to_audio_button(self):
        export_audio_btn = Gtk.Button(label="Export to Audio")
        export_audio_btn.connect("clicked", self.add_drummer_to_audio)
        self.main_box.pack_start(export_audio_btn, False, False, 0)

    def create_bpm_controls(self):
        bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        bpm_label = Gtk.Label(label="BPM:")
        bpm_box.pack_start(bpm_label, False, False, 0)
        self.bpm_entry = Gtk.Entry()
        self.bpm_entry.set_width_chars(int(6 * self.scale_factor))
        self.bpm_entry.set_text(str(self.absolute_bpm))
        self.bpm_entry.connect("changed", self.on_bpm_changed)
        bpm_box.pack_start(self.bpm_entry, False, False, 0)
        self.main_box.pack_start(bpm_box, False, False, 0)

    def create_matched_bpm_control(self):
        matched_bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        matched_bpm_label = Gtk.Label(label="Genre BPM:")
        matched_bpm_box.pack_start(matched_bpm_label, False, False, 0)
        self.matched_bpm_combo = Gtk.ComboBoxText()
        for genre in self.genre_bpm.keys():
            self.matched_bpm_combo.append_text(genre)
        self.matched_bpm_combo.set_active(0)
        self.matched_bpm_combo.connect("changed", self.on_matched_bpm_changed)
        matched_bpm_box.pack_start(self.matched_bpm_combo, False, False, 0)
        self.main_box.pack_start(matched_bpm_box, False, False, 0)

    def create_dynamic_bpm_control(self):
        dynamic_bpm_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        dynamic_bpm_label = Gtk.Label(label="Dynamic BPM (%):")
        dynamic_bpm_box.pack_start(dynamic_bpm_label, False, False, 0)
        self.dynamic_bpm_entry = Gtk.Entry()
        self.dynamic_bpm_entry.set_width_chars(int(10 * self.scale_factor))
        self.dynamic_bpm_entry.set_text("100,100,100,100")
        self.dynamic_bpm_entry.connect("changed", self.apply_dynamic_bpm)
        dynamic_bpm_box.pack_start(self.dynamic_bpm_entry, False, False, 0)
        self.main_box.pack_start(dynamic_bpm_box, False, False, 0)

    def create_pattern_controls(self):
        pattern_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        pattern_label = Gtk.Label(label="Pattern:")
        pattern_box.pack_start(pattern_label, False, False, 0)
        self.preset_genre_combo = Gtk.ComboBoxText()
        genres = ['House', 'Techno', 'Drum and Bass', 'Ambient']
        for genre in genres:
            self.preset_genre_combo.append_text(genre)
        self.preset_genre_combo.set_active(0)
        self.preset_genre_combo.connect("changed", self.apply_auto_fx_for_selected_style)
        pattern_box.pack_start(self.preset_genre_combo, False, False, 0)
        self.main_box.pack_start(pattern_box, False, False, 0)

    def create_pattern_length_control(self):
        length_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        length_label = Gtk.Label(label="Pattern Length:")
        length_box.pack_start(length_label, False, False, 0)
        length_adjustment = Gtk.Adjustment(value=16, lower=4, upper=32, step_increment=1)
        self.length_spinbutton = Gtk.SpinButton(adjustment=length_adjustment)
        self.length_spinbutton.connect("value-changed", self.on_pattern_length_changed)
        length_box.pack_start(self.length_spinbutton, False, False, 0)
        self.main_box.pack_start(length_box, False, False, 0)

    def create_instrument_randomization_controls(self):
        randomize_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        randomize_label = Gtk.Label(label="Randomize:")
        randomize_box.pack_start(randomize_label, False, False, 0)
        for inst in self.instruments:
            btn = Gtk.Button(label=inst)
            btn.connect("clicked", self.randomize_instrument, inst)
            randomize_box.pack_start(btn, False, False, 0)
        self.main_box.pack_start(randomize_box, False, False, 0)

    def create_preset_selection(self):
        preset_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
        preset_label = Gtk.Label(label="Preset:")
        preset_box.pack_start(preset_label, False, False, 0)
        self.preset_combo = Gtk.ComboBoxText()
        self.preset_combo.append_text("Default")
        self.preset_combo.set_active(0)
        preset_box.pack_start(self.preset_combo, False, False, 0)
        self.main_box.pack_start(preset_box, False, False, 0)

    def create_autolevel_button(self):
        autolevel_btn = Gtk.Button(label="Auto Level Samples")
        autolevel_btn.connect("clicked", self.autolevel_samples)
        self.main_box.pack_start(autolevel_btn, False, False, 0)

    def create_effect_controls(self):
        effect_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=int(5 * self.scale_factor))
        effect_label = Gtk.Label(label="Effects")
        effect_box.pack_start(effect_label, False, False, 0)

        for inst in self.instruments:
            inst_effect_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=int(5 * self.scale_factor))
            inst_label = Gtk.Label(label=inst)
            inst_effect_box.pack_start(inst_label, False, False, 0)
            self.effect_sliders[inst] = {}
            for effect in ['volume', 'pitch', 'echo', 'reverb', 'pan']:
                effect_adjustment = Gtk.Adjustment(value=0, lower=-2, upper=2, step_increment=0.1)
                effect_scale = Gtk.Scale(orientation=Gtk.Orientation.HORIZONTAL, adjustment=effect_adjustment)
                effect_scale.set_digits(2)
                effect_scale.set_size_request(int(100 * self.scale_factor), -1)
                effect_scale.connect("value-changed", self.on_effect_changed, inst, effect)
                inst_effect_box.pack_start(effect_scale, True, True, 0)
                self.effect_sliders[inst][effect] = effect_scale
            effect_box.pack_start(inst_effect_box, False, False, 0)
        self.main_box.pack_start(effect_box, False, False, 0)

    def create_virtual_drummer_mode_button(self):
        drummer_btn = Gtk.Button(label="Start Virtual Drummer")
        drummer_btn.set_tooltip_text("Toggle Virtual Drummer Mode")
        drummer_btn.connect("clicked", self.toggle_virtual_drummer_mode)
        self.main_box.pack_start(drummer_btn, False, False, 0)

    def on_bpm_changed(self, entry):
        try:
            self.absolute_bpm = float(entry.get_text())
        except ValueError:
            self.absolute_bpm = self.base_bpm
            entry.set_text(str(self.absolute_bpm))

    def on_matched_bpm_changed(self, combo):
        genre = combo.get_active_text()
        self.absolute_bpm = self.genre_bpm.get(genre, self.base_bpm)
        self.bpm_entry.set_text(str(self.absolute_bpm))

    def apply_dynamic_bpm(self, widget):
        try:
            percentages = [float(x.strip()) for x in self.dynamic_bpm_entry.get_text().split(',')]
            self.dynamic_bpm_list = [self.absolute_bpm * (p / 100) for p in percentages]
            self.current_bpm_index = 0
        except ValueError:
            self.dynamic_bpm_list = [self.absolute_bpm]
            self.dynamic_bpm_entry.set_text("100")

    def on_pattern_length_changed(self, spinbutton):
        new_length = int(spinbutton.get_value())
        for inst in self.instruments:
            if self.advanced_sequencer_mode:
                self.advanced_patterns[inst] = self.advanced_patterns[inst][:new_length] + [
                    {'active': False, 'rhythm_type': 'single'} for _ in range(new_length - len(self.advanced_patterns[inst]))
                ] if new_length > len(self.advanced_patterns[inst]) else self.advanced_patterns[inst][:new_length]
            else:
                self.simple_patterns[inst] = self.simple_patterns[inst][:new_length] + [0] * (new_length - len(self.simple_patterns[inst]))
        self.patterns = self.advanced_patterns if self.advanced_sequencer_mode else self.simple_patterns
        self.update_buttons()

    def on_sequencer_mode_switch(self, switch, gparam):
        self.advanced_sequencer_mode = switch.get_active()
        self.patterns = self.advanced_patterns if self.advanced_sequencer_mode else self.simple_patterns
        self.update_buttons()

    def on_performer_mode_switch(self, switch, gparam):
        self.performer_mode = switch.get_active()

    def toggle_virtual_drummer_mode(self, button):
        self.virtual_drummer_mode = not self.virtual_drummer_mode
        button.set_label("Stop Virtual Drummer" if self.virtual_drummer_mode else "Start Virtual Drummer")
        if self.virtual_drummer_mode:
            self.play_thread = threading.Thread(target=self.virtual_drummer_loop)
            self.play_thread.start()

    def on_button_toggled(self, button, instrument, step):
        if self.advanced_sequencer_mode:
            self.patterns[instrument][step]['active'] = button.get_active()
        else:
            self.patterns[instrument][step] = 1 if button.get_active() else 0

    def on_scroll(self, button, event, instrument, step):
        if self.advanced_sequencer_mode:
            if event.direction == Gdk.ScrollDirection.UP:
                rhythm_types = list(self.rhythm_types.keys())
                current_rhythm = self.patterns[instrument][step]['rhythm_type']
                next_index = (rhythm_types.index(current_rhythm) + 1) % len(rhythm_types)
                self.patterns[instrument][step]['rhythm_type'] = rhythm_types[next_index]
            elif event.direction == Gdk.ScrollDirection.DOWN:
                rhythm_types = list(self.rhythm_types.keys())
                current_rhythm = self.patterns[instrument][step]['rhythm_type']
                prev_index = (rhythm_types.index(current_rhythm) - 1) % len(rhythm_types)
                self.patterns[instrument][step]['rhythm_type'] = rhythm_types[prev_index]

    def on_button_press(self, button, event, instrument, step):
        if self.performer_mode and event.button == 1:
            sound = self.apply_effects(self.samples[instrument], instrument)
            sound.play()
            self.last_button_pressed = (instrument, step)
            return True
        return False

    def on_effect_changed(self, scale, instrument, effect):
        self.effects[instrument][effect] = scale.get_value()
        self.update_effect_colors()

    def update_effect_colors(self):
        for inst in self.instruments:
            for effect in self.effects[inst]:
                if effect in self.effect_sliders[inst]:
                    value = self.effects[inst][effect]
                    scale = self.effect_sliders[inst][effect]
                    context = scale.get_style_context()
                    if value > 0:
                        context.add_class("positive-effect")
                        context.remove_class("negative-effect")
                    elif value < 0:
                        context.add_class("negative-effect")
                        context.remove_class("positive-effect")
                    else:
                        context.remove_class("positive-effect")
                        context.remove_class("negative-effect")

    def apply_effects(self, sound, instrument, export=False):
        audio_segment = AudioSegment(
            pygame.sndarray.array(sound).tobytes(),
            frame_rate=44100,
            sample_width=2,
            channels=2
        )
        if not export:
            audio_segment = audio_segment + self.effects[instrument]['volume']
            audio_segment = audio_segment.pan(self.effects[instrument]['pan'])
            if self.effects[instrument]['pitch'] != 0:
                audio_segment = audio_segment._spawn(audio_segment.raw_data, overrides={
                    "frame_rate": int(audio_segment.frame_rate * (2.0 ** (self.effects[instrument]['pitch'] / 12.0)))
                })
            if self.effects[instrument]['reverb'] > 0:
                reverb_segment = audio_segment.fade(to_gain=-120, start=0, duration=1000)
                reverb_gain = -20 * (1 - self.effects[instrument]['reverb'])
                reverb_segment = reverb_segment + reverb_gain
                audio_segment = audio_segment.overlay(reverb_segment, position=0)
            if self.effects[instrument]['echo'] > 0:
                echo_segment = audio_segment + self.effects[instrument]['echo']
                audio_segment = audio_segment.overlay(echo_segment, position=100)
        samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 2)
        return pygame.sndarray.make_sound(samples.astype(np.int16))

    def load_samples_from_directory(self):
        self.samples.clear()
        for root, _, files in os.walk(self.current_directory):
            for file in files:
                if file.lower().endswith(('.wav', '.mp3', '.ogg')):
                    for inst in self.instruments:
                        if inst.lower() in file.lower():
                            try:
                                audio_segment = AudioSegment.from_file(os.path.join(root, file))
                                audio_segment = audio_segment.set_channels(2)
                                audio_segment = normalize(audio_segment)
                                samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 2)
                                self.samples[inst] = pygame.sndarray.make_sound(samples.astype(np.int16))
                                self.waveforms[inst] = samples[:, 0] / 32767.0
                            except Exception as e:
                                print(f"Error loading sample {file} for {inst}: {e}")

    def refresh_sample_browser(self, button):
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
                    self.waveforms[inst] = samples[:, 0] / 32767.0
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
        max_improvisations = 4

        while self.virtual_drummer_mode and improvisation_count < max_improvisations:
            self.randomize_pattern(None)
            self.apply_groove(None)
            self.perfect_tempo_bpm(None)
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
            for instrument in self.instruments:
                for effect in ['volume', 'pitch', 'echo', 'reverb', 'pan']:
                    if random.random() < 0.3:
                        self.effects[instrument][effect] = random.uniform(-2, 2)
                        if effect in self.effect_sliders[instrument]:
                            GLib.idle_add(self.effect_sliders[instrument][effect].set_value, self.effects[instrument][effect])
            self.update_effect_colors()
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
                'sample_params': self.sample_params,
                'waveforms': {inst: waveform.tolist() for inst, waveform in self.waveforms.items()}
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
            self.waveforms = {inst: np.array(data) for inst, data in project_data.get('waveforms', {}).items()}
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
                if inst in self.waveforms:
                    audio_segment = AudioSegment(
                        (self.waveforms[inst] * 32767).astype(np.int16).tobytes(),
                        frame_rate=44100,
                        sample_width=2,
                        channels=1
                    )
                    audio_segment = normalize(audio_segment)
                    samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 1)
                    samples = np.hstack((samples, samples))
                    self.samples[inst] = pygame.sndarray.make_sound(samples.astype(np.int16))
            self.bpm_entry.set_text(str(self.absolute_bpm))
            self.apply_dynamic_bpm(None)
            self.update_buttons()
            self.update_effect_colors()
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
    
            for instrument in self.instruments:
                for step in range(pattern_length):
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            for i in range(rhythm['notes']):
                                note_time = time + (step + i * rhythm['speed'] + rhythm['swing'] * i) * step_duration
                                midi.addNote(
                                    track, channel, self.midi_notes[instrument], note_time,
                                    step_duration * rhythm['speed'], 100
                                )
                    else:
                        if self.patterns[instrument][step]:
                            midi.addNote(
                                track, channel, self.midi_notes[instrument], time + step * step_duration,
                                step_duration, 100
                            )
            with open(filename, "wb") as output_file:
                midi.writeFile(output_file)
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
    
            for instrument in self.instruments:
                for step in range(pattern_length):
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            for i in range(rhythm['notes']):
                                note_time = time + (step + i * rhythm['speed'] + rhythm['swing'] * i) * step_duration
                                velocity = 100
                                if step_data['rhythm_type'] == 'accent':
                                    velocity = 127 if i == 0 else 80
                                midi.addNote(
                                    track, channel, self.midi_notes[instrument], note_time,
                                    step_duration * rhythm['speed'], velocity
                                )
                    else:
                        if self.patterns[instrument][step]:
                            midi.addNote(
                                track, channel, self.midi_notes[instrument], time + step * step_duration,
                                step_duration, 100
                            )
            with open(filename, "wb") as output_file:
                midi.writeFile(output_file)
        dialog.destroy()
    
    def add_drummer_to_audio(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export to Audio",
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Save", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("drum_pattern.wav")
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            sample_rate = 44100
            pattern_length = int(self.length_spinbutton.get_value())
            step_duration = 60.0 / (self.absolute_bpm * 4)
            total_duration_ms = pattern_length * step_duration * 1000
            mixed_audio = AudioSegment.silent(duration=total_duration_ms)
    
            for instrument in self.instruments:
                instrument_audio = AudioSegment.silent(duration=total_duration_ms)
                for step in range(pattern_length):
                    if self.advanced_sequencer_mode:
                        step_data = self.patterns[instrument][step]
                        if step_data['active']:
                            rhythm = self.rhythm_types[step_data['rhythm_type']]
                            for i in range(rhythm['notes']):
                                position_ms = (step + i * rhythm['speed'] + rhythm['swing'] * i) * step_duration * 1000
                                audio_segment = self.apply_effects(self.samples[instrument], instrument, export=True)
                                instrument_audio = instrument_audio.overlay(audio_segment, position=position_ms)
                    else:
                        if self.patterns[instrument][step]:
                            position_ms = step * step_duration * 1000
                            audio_segment = self.apply_effects(self.samples[instrument], instrument, export=True)
                            instrument_audio = instrument_audio.overlay(audio_segment, position=position_ms)
                mixed_audio = mixed_audio.overlay(instrument_audio)
    
            mixed_audio = normalize(mixed_audio)
            mixed_audio.export(filename, format="wav")
        dialog.destroy()
    
    def load_samples(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Select Sample Directory",
            action=Gtk.FileChooserAction.SELECT_FOLDER,
            buttons=("Open", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            self.current_directory = dialog.get_filename()
            self.current_dir_label.set_text(self.current_directory)
            self.load_samples_from_directory()
            self.refresh_sample_browser(None)
        dialog.destroy()
    
    def load_sample_bank(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Load Sample Bank",
            action=Gtk.FileChooserAction.OPEN,
            buttons=("Open", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            with open(filename, 'r') as f:
                bank_data = json.load(f)
            for inst in self.instruments:
                if inst in bank_data:
                    audio_segment = AudioSegment(
                        np.array(bank_data[inst]['samples']).astype(np.int16).tobytes(),
                        frame_rate=44100,
                        sample_width=2,
                        channels=2
                    )
                    audio_segment = normalize(audio_segment)
                    samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 2)
                    self.samples[inst] = pygame.sndarray.make_sound(samples.astype(np.int16))
                    self.waveforms[inst] = samples[:, 0] / 32767.0
                    self.sample_params[inst] = bank_data[inst].get('params', self.sample_params[inst])
                    self.current_adsr[inst] = bank_data[inst].get('adsr', self.current_adsr[inst])
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
        dialog.destroy()
    
    def export_sample_bank(self, widget):
        dialog = Gtk.FileChooserDialog(
            title="Export Sample Bank",
            action=Gtk.FileChooserAction.SAVE,
            buttons=("Save", Gtk.ResponseType.OK, "Cancel", Gtk.ResponseType.CANCEL)
        )
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("sample_bank.json")
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            bank_data = {}
            for inst in self.instruments:
                samples = pygame.sndarray.array(self.samples[inst])
                bank_data[inst] = {
                    'samples': samples.tolist(),
                    'params': self.sample_params[inst],
                    'adsr': self.current_adsr[inst]
                }
            with open(filename, 'w') as f:
                json.dump(bank_data, f, indent=4)
        dialog.destroy()
    
    def autolevel_samples(self, widget):
        for inst in self.instruments:
            audio_segment = AudioSegment(
                pygame.sndarray.array(self.samples[inst]).tobytes(),
                frame_rate=44100,
                sample_width=2,
                channels=2
            )
            audio_segment = normalize(audio_segment)
            samples = np.array(audio_segment.get_array_of_samples()).reshape(-1, 2)
            self.samples[inst] = pygame.sndarray.make_sound(samples.astype(np.int16))
            self.waveforms[inst] = samples[:, 0] / 32767.0
    
    def toggle_preview(self, checkbutton, instrument):
        self.preview_active[instrument] = checkbutton.get_active()
        if self.preview_active[instrument]:
            self.samples[instrument].play()
    
    def adjust_adsr(self, button, instrument, param, delta):
        self.current_adsr[instrument][param] = max(0.0, min(1.0, self.current_adsr[instrument][param] + delta))
        self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()
    
    def on_adsr_entry_changed(self, entry, instrument, param):
        try:
            value = float(entry.get_text())
            if 0.0 <= value <= 1.0:
                self.current_adsr[instrument][param] = value
                self.generate_parametric_samples()
                if self.preview_active[instrument]:
                    self.samples[instrument].play()
            else:
                entry.set_text(f"{self.current_adsr[instrument][param]:.2f}")
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
            self.current_adsr[instrument][param] = random.uniform(0.0, 1.0)
            self.adsr_entries[instrument][param].set_text(f"{self.current_adsr[instrument][param]:.2f}")
        self.generate_parametric_samples()
        if self.preview_active[instrument]:
            self.samples[instrument].play()
    
    def randomize_instrument(self, button, instrument):
        pattern_length = int(self.length_spinbutton.get_value())
        for i in range(pattern_length):
            if self.advanced_sequencer_mode:
                self.patterns[instrument][i]['active'] = random.random() < 0.3
                if self.patterns[instrument][i]['active']:
                    self.patterns[instrument][i]['rhythm_type'] = random.choice(list(self.rhythm_types.keys()))
            else:
                self.patterns[instrument][i] = 1 if random.random() < 0.3 else 0
        self.update_buttons()
    
    def perfect_tempo_bpm(self, widget):
        pattern_length = int(self.length_spinbutton.get_value())
        total_duration = 0.0
        for step in range(pattern_length):
            current_bpm = self.get_next_bpm()
            step_duration = 60.0 / (current_bpm * 4)
            total_duration += step_duration
        if total_duration > 0:
            target_bpm = (pattern_length / total_duration) * 60
            self.absolute_bpm = target_bpm
            self.bpm_entry.set_text(str(round(target_bpm, 2)))
            self.dynamic_bpm_list = [self.absolute_bpm]
    
    def get_next_bpm(self):
        if not self.dynamic_bpm_list:
            return self.absolute_bpm
        bpm = self.dynamic_bpm_list[self.current_bpm_index]
        return bpm
    
    def advance_bpm(self):
        if self.dynamic_bpm_list:
            self.current_bpm_index = (self.current_bpm_index + 1) % len(self.dynamic_bpm_list)
    
    def toggle_fullscreen(self, widget):
        if not self.is_fullscreen:
            self.fullscreen()
            self.is_fullscreen = True
        else:
            self.unfullscreen()
            self.is_fullscreen = False
        self.scale_interface(None, self.get_allocation())
    
    def scale_interface(self, widget, allocation):
        window_width = allocation.width
        window_height = allocation.height
        reference_width = 1280
        reference_height = 720
        self.scale_factor = min(window_width / reference_width, window_height / reference_height)
        for child in self.main_box.get_children():
            if isinstance(child, Gtk.Box):
                for grandchild in child.get_children():
                    if isinstance(grandchild, (Gtk.Label, Gtk.Button, Gtk.Entry, Gtk.ComboBoxText, Gtk.CheckButton)):
                        grandchild.set_size_request(int(grandchild.get_size_request()[0] * self.scale_factor), -1)
            elif isinstance(child, (Gtk.Button, Gtk.Entry)):
                child.set_size_request(int(child.get_size_request()[0] * self.scale_factor), -1)
        for inst in self.instruments:
            for button in self.buttons[inst]:
                button.set_size_request(int(30 * self.scale_factor), int(30 * self.scale_factor))
            for param in ['attack', 'decay', 'sustain', 'release']:
                self.adsr_entries[inst][param].set_width_chars(int(4 * self.scale_factor))
            for param in ['frequency', 'duration']:
                self.sample_param_controls[inst][param].set_width_chars(int(6 * self.scale_factor))
            self.sample_param_controls[inst]['amplitude'].set_size_request(int(100 * self.scale_factor), -1)
            for effect in ['volume', 'pitch', 'echo', 'reverb', 'pan']:
                self.effect_sliders[inst][effect].set_size_request(int(100 * self.scale_factor), -1)
    
    def update_buttons(self):
        pattern_length = int(self.length_spinbutton.get_value())
        for inst in self.instruments:
            for i, button in enumerate(self.buttons[inst]):
                if i < pattern_length:
                    button.show()
                    if self.advanced_sequencer_mode:
                        button.set_active(self.patterns[inst][i]['active'])
                    else:
                        button.set_active(self.patterns[inst][i] == 1)
                else:
                    button.hide()
    
async def main():
    app = DrumSamplerApp()
    app.connect("destroy", Gtk.main_quit)
    app.show_all()
    if platform.system() == "Emscripten":
        await asyncio.sleep(0)
    else:
        Gtk.main()

if platform.system() == "Emscripten":
    asyncio.ensure_future(main())
else:
    if __name__ == "__main__":
        asyncio.run(main())
