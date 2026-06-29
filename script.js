'use strict';
/* =========================================================================
   BeatFX — a native Web Audio API sampler / sequencer DAW
   - Each channel owns an independent FX strip (Tone/Comp/Volume/Pitch):
       voice -> [BiquadFilter] -> [Compressor] -> [Gain] -> masterBus -> out
   - Layers: independent pattern sheets you switch between via tabs.
   - Variable length (16..64 steps) and a 4-octave pitch grid.
   - The waveform display reacts live to the selected channel's FX.
   ========================================================================= */
(function () {

  const $ = (id) => document.getElementById(id);
  const clamp = (lo, hi, v) => Math.max(lo, Math.min(hi, v));
  const hexA = (h, a) => {
    const n = parseInt(h.slice(1), 16);
    return `rgba(${(n >> 16) & 255},${(n >> 8) & 255},${n & 255},${a})`;
  };

  /* ----------------------------- Constants ----------------------------- */
  const HIGH_MIDI = 84, LOW_MIDI = 36;    // C6 .. C2 (4 octaves, top -> bottom)
  const ROOT_NOTE = 60;                   // Middle C — sample root pitch
  const ROWS = HIGH_MIDI - LOW_MIDI + 1;  // 49 pitch rows
  const NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
  const SLOT_COLORS = [
    '#2eb6ff', '#00e676', '#ff7a18', '#ff4d6d', '#b388ff', '#ffd166', '#22d3ee', '#a3e635',
    '#ff6ec7', '#7c4dff', '#18ffff', '#76ff03', '#ffab40', '#ff5252', '#64ffda',
    '#e879f9', '#fb923c', '#2dd4bf', '#a78bfa'
  ];
  const DEF_TONE = 100, DEF_COMP = 30, DEF_VOL = 80, DEF_PITCH = 0;

  const rowToMidi = (r) => HIGH_MIDI - r;
  const midiToRow = (m) => HIGH_MIDI - m;
  const pc = (m) => ((m % 12) + 12) % 12;
  const isBlack = (m) => NOTE_NAMES[pc(m)].includes('#');
  const noteName = (m) => NOTE_NAMES[pc(m)] + (Math.floor(m / 12) - 1);

  /* ------------------------------- State ------------------------------- */
  let bpm = 120, keyOffset = 0, steps = 16;     // global controls
  let isPlaying = false, currentStep = 0, nextNoteTime = 0, timerId = null;
  let selectedId = null;
  let isPainting = false, paintValue = true;
  let meterLevel = 0, lastNote = null;
  const notesQueue = [];
  const cells = [];                              // cells[row][step] -> DOM element
  const slots = [];                             // sample channels (own FX + mute)

  // Layers: each is an independent sheet of patterns for every channel.
  let layers = [];
  let activeLayer = 0;
  const newLayer = (name) => ({ name, patterns: {} });
  // Active layer's note Set for a channel (created lazily).
  function patt(slot) {
    const L = layers[activeLayer];
    let s = L.patterns[slot.id];
    if (!s) { s = new Set(); L.patterns[slot.id] = s; }
    return s;
  }

  /* --------------------- Sound objects & views ------------------------- */
  const BOUNCE_LOOPS = 4;          // bars baked into each sound object (a loopable phrase)
  const SO_COLORS = ['#ff9f43', '#5b6bff', '#22d3ee', '#ffd166', '#00e676', '#ff6ec7', '#b388ff', '#ff5252', '#4ade80'];
  const soundObjects = [];          // { id, name, color, buffer, duration }
  let soNum = 1, soSeq = 1;
  let view = 'studio', railExpanded = false;

  /* ----------------------- Arrangement (Create tab) ------------------- */
  const LANES = 8, PPS = 14, LANE_H = 56, CLIP_MIN = 0.5;   // rows, px-per-second, lane height
  let arrLength = 120;              // total timeline seconds
  const clips = [];                 // { id, objId, lane, start, length }
  let clipSeq = 1;
  let arrPlaying = false, arrPlayhead = 0, arrStartCtxTime = 0;
  let arrSources = [];
  const PLAY_SVG  = '<svg width="20" height="20" viewBox="0 0 24 24" fill="currentColor"><path d="M8 5v14l11-7z"/></svg>';
  const PAUSE_SVG = '<svg width="20" height="20" viewBox="0 0 24 24" fill="currentColor"><path d="M6 5h4v14H6zM14 5h4v14h-4z"/></svg>';

  /* --------------------------- Audio context --------------------------- */
  const ctx = new (window.AudioContext || window.webkitAudioContext)();
  const masterOut = ctx.createGain();
  masterOut.gain.value = 0.85;
  const analyser = ctx.createAnalyser();
  analyser.fftSize = 256;
  const meterBuf = new Uint8Array(analyser.fftSize);
  masterOut.connect(ctx.destination);
  masterOut.connect(analyser);

  const secondsPerStep = () => (60 / bpm) / 4;
  const resumeAudio = () => { if (ctx.state !== 'running') ctx.resume(); };

  function applySlotFx(slot) {
    slot.filterNode.frequency.value = 200 * Math.pow(90, slot.tone / 100);   // 200..18000 Hz
    const a = slot.compression / 100;
    slot.compNode.threshold.value = -10 - a * 40;
    slot.compNode.ratio.value = 2 + a * 16;
    slot.compNode.knee.value = 18;
    slot.compNode.attack.value = 0.003;
    slot.compNode.release.value = 0.25;
    slot.gainNode.gain.value = slot.muted ? 0 : slot.volume / 100;            // mute = silence strip
  }

  /* ===================================================================== */
  /*                       DEFAULT SAMPLE SYNTHESIS                         */
  /*  Procedurally rendered AudioBuffers so the app runs with zero assets. */
  /*  Tonal sources are tuned to Middle C so the pitch matrix lines up.    */
  /* ===================================================================== */
  const newBuf = (dur) => ctx.createBuffer(1, Math.max(1, Math.floor(ctx.sampleRate * dur)), ctx.sampleRate);
  const normalize = (d) => {
    let m = 0;
    for (let i = 0; i < d.length; i++) { const a = Math.abs(d[i]); if (a > m) m = a; }
    if (m > 0) { const g = 0.9 / m; for (let i = 0; i < d.length; i++) d[i] *= g; }
  };
  const ar = (t, dur, atk, rel) => {
    if (t < atk) return t / atk;
    if (t > dur - rel) return Math.max(0, (dur - t) / rel);
    return 1;
  };

  /* ----- Percussion ----- */
  function renderKick() {
    const b = newBuf(0.5), d = b.getChannelData(0), sr = ctx.sampleRate; let ph = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, f = 45 + 130 * Math.exp(-t * 18);
      ph += 2 * Math.PI * f / sr;
      d[i] = Math.sin(ph) * Math.exp(-t * 7);
    }
    const ck = Math.floor(sr * 0.006);
    for (let i = 0; i < ck; i++) d[i] += (1 - i / ck) * (Math.random() * 2 - 1) * 0.4;
    normalize(d); return b;
  }
  function renderSnare() {
    const b = newBuf(0.25), d = b.getChannelData(0), sr = ctx.sampleRate;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, env = Math.exp(-t * 16);
      const tone = Math.sin(2 * Math.PI * 180 * t) * Math.exp(-t * 22) * 0.4;
      d[i] = ((Math.random() * 2 - 1) * 0.8 + tone) * env;
    }
    normalize(d); return b;
  }
  function renderHat() {
    const b = newBuf(0.08), d = b.getChannelData(0), sr = ctx.sampleRate; let prev = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, n = Math.random() * 2 - 1, hp = n - prev; prev = n;
      d[i] = hp * Math.exp(-t * 55);
    }
    normalize(d); return b;
  }
  function renderClap() {
    const b = newBuf(0.3), d = b.getChannelData(0), sr = ctx.sampleRate, offs = [0, 0.012, 0.024, 0.036];
    for (let i = 0; i < d.length; i++) {
      const t = i / sr; let s = 0;
      for (const o of offs) if (t >= o) s += (Math.random() * 2 - 1) * Math.exp(-(t - o) * 45);
      s += (Math.random() * 2 - 1) * Math.exp(-t * 8) * 0.4;
      d[i] = s * 0.5;
    }
    normalize(d); return b;
  }
  function renderTom() {
    const b = newBuf(0.4), d = b.getChannelData(0), sr = ctx.sampleRate; let ph = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, f = 80 + 150 * Math.exp(-t * 6);
      ph += 2 * Math.PI * f / sr;
      d[i] = Math.sin(ph) * Math.exp(-t * 7);
    }
    normalize(d); return b;
  }
  function renderDrums() {
    const b = newBuf(0.4), d = b.getChannelData(0), sr = ctx.sampleRate; let ph = 0, prev = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr;
      const kf = 45 + 130 * Math.exp(-t * 18); ph += 2 * Math.PI * kf / sr;
      const kick = Math.sin(ph) * Math.exp(-t * 8);
      const snare = ((Math.random() * 2 - 1) * 0.8 + Math.sin(2 * Math.PI * 180 * t) * 0.4) * Math.exp(-t * 20);
      const n = Math.random() * 2 - 1, hp = n - prev; prev = n;
      const hat = hp * Math.exp(-t * 45) * 0.5;
      d[i] = kick * 0.9 + snare * 0.5 + hat * 0.4;
    }
    normalize(d); return b;
  }

  /* ----- Tonal (tuned to C4 = 261.63 Hz) ----- */
  function renderBass() {
    const b = newBuf(0.6), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63; let lp = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, saw = 2 * ((t * base) % 1) - 1;
      lp += (saw - lp) * 0.18;
      d[i] = lp * Math.exp(-t * 4);
    }
    normalize(d); return b;
  }
  function renderPluck() {
    const b = newBuf(0.35), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, tri = 2 * Math.abs(2 * ((t * base) % 1) - 1) - 1;
      d[i] = tri * Math.exp(-t * 9);
    }
    normalize(d); return b;
  }
  function renderKeys() {
    const b = newBuf(0.7), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, env = Math.exp(-t * 3);
      d[i] = (Math.sin(2 * Math.PI * base * t)
            + 0.5 * Math.sin(2 * Math.PI * base * 2 * t)
            + 0.25 * Math.sin(2 * Math.PI * base * 3 * t)) * env;
    }
    normalize(d); return b;
  }
  function renderPiano() {
    const b = newBuf(1.3), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    const parts = [[1, 1], [2, 0.6], [3, 0.4], [4, 0.26], [5, 0.16], [6, 0.1]];
    for (let i = 0; i < d.length; i++) {
      const t = i / sr; let s = 0;
      for (const [n, a] of parts) {
        const f = base * n * (1 + 0.0008 * n * n);
        s += a * Math.sin(2 * Math.PI * f * t) * Math.exp(-t * (2.2 + n * 0.7));
      }
      d[i] = s;
    }
    const hk = Math.floor(sr * 0.008);
    for (let i = 0; i < hk; i++) d[i] += (1 - i / hk) * (Math.random() * 2 - 1) * 0.3;
    normalize(d); return b;
  }
  function renderViolin() {
    const b = newBuf(1.1), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63; let ph = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, vib = 1 + 0.006 * Math.sin(2 * Math.PI * 5.5 * t);
      ph += 2 * Math.PI * base * vib / sr;
      let s = 0; for (let n = 1; n <= 10; n++) s += Math.sin(n * ph) / n;
      d[i] = s * ar(t, 1.1, 0.08, 0.2) * 0.5;
    }
    normalize(d); return b;
  }
  function renderChords() {
    const b = newBuf(1.6), d = b.getChannelData(0), sr = ctx.sampleRate;
    const freqs = [261.63, 329.63, 392.00];
    for (let i = 0; i < d.length; i++) {
      const t = i / sr; let s = 0;
      for (const f of freqs) s += Math.sin(2 * Math.PI * f * t) + 0.35 * Math.sin(2 * Math.PI * 2 * f * t);
      d[i] = s * Math.exp(-t * 1.6) * ar(t, 1.6, 0.01, 0.2);
    }
    normalize(d); return b;
  }
  function renderOrch1() {
    const b = newBuf(1.6), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    const dets = [-7, -3, 0, 3, 7].map((c) => Math.pow(2, c / 1200));
    const phs = dets.map(() => 0);
    for (let i = 0; i < d.length; i++) {
      const t = i / sr; let s = 0;
      for (let v = 0; v < dets.length; v++) {
        phs[v] += 2 * Math.PI * base * dets[v] / sr;
        let sw = 0; for (let n = 1; n <= 8; n++) sw += Math.sin(n * phs[v]) / n;
        s += sw;
      }
      s += 0.5 * Math.sin(2 * Math.PI * base * 2 * t);
      d[i] = s * ar(t, 1.6, 0.15, 0.3) * 0.25;
    }
    normalize(d); return b;
  }
  function renderOrch2() {
    const b = newBuf(1.9), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    let lp = 0, ph = 0, phs = 0, phf = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr;
      ph  += 2 * Math.PI * base / sr;
      phs += 2 * Math.PI * (base / 2) / sr;
      phf += 2 * Math.PI * (base * 1.5) / sr;
      let saw = 0; for (let n = 1; n <= 10; n++) saw += Math.sin(n * ph) / n;
      const raw = saw * 0.6 + Math.sin(phs) * 0.7 + Math.sin(phf) * 0.3;
      lp += (raw - lp) * 0.12;
      d[i] = lp * ar(t, 1.9, 0.25, 0.4) * 0.4;
    }
    normalize(d); return b;
  }
  function renderChoir() {
    const b = newBuf(1.7), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63; let ph = 0;
    const fg = (f) =>
      Math.exp(-((f - 800) ** 2) / (2 * 120 * 120)) +
      0.7 * Math.exp(-((f - 1150) ** 2) / (2 * 120 * 120)) +
      0.3 * Math.exp(-((f - 2900) ** 2) / (2 * 220 * 220));
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, vib = 1 + 0.005 * Math.sin(2 * Math.PI * 5 * t);
      ph += 2 * Math.PI * base * vib / sr;
      let s = 0;
      for (let n = 1; n <= 36; n++) { const f = n * base * vib; s += Math.sin(n * ph) * fg(f) / n; }
      d[i] = s * ar(t, 1.7, 0.18, 0.35);
    }
    normalize(d); return b;
  }

  // Bells: FM synthesis (metallic, shimmering, long decay).
  function renderBells() {
    const b = newBuf(1.6), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr;
      const mod = Math.sin(2 * Math.PI * base * 3.5 * t) * 6 * Math.exp(-t * 5);     // decaying FM index
      const car = Math.sin(2 * Math.PI * base * t + mod) * Math.exp(-t * 2.6);
      const shimmer = 0.3 * Math.sin(2 * Math.PI * base * 5.4 * t) * Math.exp(-t * 6);
      d[i] = car + shimmer;
    }
    normalize(d); return b;
  }
  // Marimba: wooden mallet — fundamental + a 4:1 bar overtone, quick decay.
  function renderMarimba() {
    const b = newBuf(0.5), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr;
      const fund = Math.sin(2 * Math.PI * base * t) * Math.exp(-t * 7);
      const partial = 0.35 * Math.sin(2 * Math.PI * base * 4 * t) * Math.exp(-t * 13);
      d[i] = fund + partial;
    }
    const mk = Math.floor(sr * 0.004);
    for (let i = 0; i < mk; i++) d[i] += (1 - i / mk) * (Math.random() * 2 - 1) * 0.2;   // mallet click
    normalize(d); return b;
  }
  // Flute: airy sine with vibrato + a touch of breath noise.
  function renderFlute() {
    const b = newBuf(1.0), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63; let ph = 0;
    for (let i = 0; i < d.length; i++) {
      const t = i / sr, vib = 1 + 0.004 * Math.sin(2 * Math.PI * 5 * t);
      ph += 2 * Math.PI * base * vib / sr;
      const tone = Math.sin(ph) + 0.12 * Math.sin(2 * ph) + 0.05 * Math.sin(3 * ph);
      const breath = (Math.random() * 2 - 1) * 0.06;
      d[i] = (tone + breath) * ar(t, 1.0, 0.07, 0.18);
    }
    normalize(d); return b;
  }

  // Organ: drawbar additive organ (the Interstellar sound) — sustained, full.
  function renderOrgan() {
    const b = newBuf(1.2), d = b.getChannelData(0), sr = ctx.sampleRate, base = 261.63;
    const bars = [[1, 1], [2, 0.7], [3, 0.5], [4, 0.35], [6, 0.2], [8, 0.13]];
    for (let i = 0; i < d.length; i++) {
      const t = i / sr; let s = 0;
      for (const [h, a] of bars) s += a * Math.sin(2 * Math.PI * base * h * t);
      d[i] = s * ar(t, 1.2, 0.02, 0.12);
    }
    normalize(d); return b;
  }

  /* --------------------------- Channel model --------------------------- */
  function addSlot(name, buffer) {
    const id = 's' + slots.length + '_' + name.toLowerCase().replace(/\W+/g, '');
    const slot = {
      id, name, buffer, el: null, muted: false,
      color: SLOT_COLORS[slots.length % SLOT_COLORS.length],
      tone: DEF_TONE, compression: DEF_COMP, volume: DEF_VOL, pitch: DEF_PITCH
    };
    slot.filterNode = ctx.createBiquadFilter();
    slot.filterNode.type = 'lowpass';
    slot.filterNode.Q.value = 0.7;
    slot.compNode = ctx.createDynamicsCompressor();
    slot.gainNode = ctx.createGain();
    slot.filterNode.connect(slot.compNode);
    slot.compNode.connect(slot.gainNode);
    slot.gainNode.connect(masterOut);
    applySlotFx(slot);
    slots.push(slot);
    return slot;
  }

  function buildDefaultSlots() {
    addSlot('Kick',        renderKick());
    addSlot('Snare',       renderSnare());
    addSlot('Hi-Hat',      renderHat());
    addSlot('Clap',        renderClap());
    addSlot('Tom',         renderTom());
    addSlot('Bass',        renderBass());
    addSlot('Pluck',       renderPluck());
    addSlot('Keys',        renderKeys());
    addSlot('Piano',       renderPiano());
    addSlot('Violin',      renderViolin());
    addSlot('Chords',      renderChords());
    addSlot('Orchestra 1', renderOrch1());
    addSlot('Orchestra 2', renderOrch2());
    addSlot('Drums',       renderDrums());
    addSlot('Choir',       renderChoir());
    addSlot('Bells',       renderBells());
    addSlot('Marimba',     renderMarimba());
    addSlot('Flute',       renderFlute());
    addSlot('Organ',       renderOrgan());
  }

  const current = () => slots.find((s) => s.id === selectedId);

  /* ===================================================================== */
  /*                              UI BUILDERS                              */
  /* ===================================================================== */
  function buildKeyOptions() {
    const sel = $('key');
    NOTE_NAMES.forEach((n, i) => {
      const o = document.createElement('option');
      o.value = i; o.textContent = n;
      sel.appendChild(o);
    });
  }

  // Rebuildable: re-runs when the step count changes.
  function buildRoll() {
    const labels = $('labels'), grid = $('grid'), head = $('stepHead');
    labels.innerHTML = ''; grid.innerHTML = ''; head.innerHTML = '';
    grid.style.gridTemplateColumns = `repeat(${steps},1fr)`;
    head.style.gridTemplateColumns = `repeat(${steps},1fr)`;
    cells.length = 0;

    for (let s = 0; s < steps; s++) {
      const h = document.createElement('div');
      h.className = 'step-h' + (s % 4 === 0 ? ' beat' : '');
      h.textContent = (steps <= 32 || s % 4 === 0) ? (s + 1) : '';
      head.appendChild(h);
    }
    for (let r = 0; r < ROWS; r++) {
      const midi = rowToMidi(r), black = isBlack(midi), octave = pc(midi) === 0;
      const lab = document.createElement('div');
      lab.className = 'note-label ' + (black ? 'black' : 'white') + (octave ? ' octave' : '');
      lab.textContent = noteName(midi);
      labels.appendChild(lab);

      cells[r] = [];
      for (let s = 0; s < steps; s++) {
        const c = document.createElement('div');
        c.className = 'cell' + (black ? ' black' : '') + (s % 4 === 3 ? ' beat' : '') + (octave ? ' octave' : '');
        c.dataset.r = r; c.dataset.s = s;
        grid.appendChild(c);
        cells[r][s] = c;
      }
    }
  }

  function paintCell(r, s, on) {
    const c = cells[r][s];
    if (!c) return;
    if (on) {
      const col = current().color;
      c.classList.add('active');
      c.style.background = col;
      c.style.boxShadow = 'inset 0 0 7px ' + hexA(col, 0.85);
    } else {
      c.classList.remove('active');
      c.style.background = '';
      c.style.boxShadow = '';
    }
  }

  function setCell(r, s, on) {
    const slot = current(), key = r + '_' + s, p = patt(slot);
    if (on) p.add(key); else p.delete(key);
    paintCell(r, s, on);
    updateSlotDot(slot);
  }

  function refreshGrid() {
    const p = patt(current());
    for (let r = 0; r < ROWS; r++)
      for (let s = 0; s < steps; s++)
        paintCell(r, s, p.has(r + '_' + s));
  }

  /* ----- Sidebar channels (with mute) ----- */
  function buildSlots() {
    const wrap = $('slots');
    wrap.innerHTML = '';
    slots.forEach((slot) => {
      const row = document.createElement('div');
      row.className = 'slot' + (slot.id === selectedId ? ' sel' : '') + (slot.muted ? ' muted' : '');
      row.dataset.id = slot.id;
      row.innerHTML =
        `<span class="dotc" style="background:${slot.color};color:${slot.color}"></span>` +
        `<span class="nm">${slot.name}</span>` +
        `<span class="hasdot"></span>` +
        `<span class="mute" title="Mute / unmute">M</span>`;
      row.addEventListener('click', () => selectSlot(slot.id));
      row.querySelector('.mute').addEventListener('click', (e) => { e.stopPropagation(); toggleMute(slot); });
      wrap.appendChild(row);
      slot.el = row;
      updateSlotDot(slot);
    });
    $('slotCount').textContent = slots.length;
  }

  function toggleMute(slot) {
    slot.muted = !slot.muted;
    slot.el.classList.toggle('muted', slot.muted);
    applySlotFx(slot);                  // instantly silences (or restores) the strip
  }

  function updateSlotDot(slot) {
    if (slot.el) slot.el.querySelector('.hasdot').style.opacity = patt(slot).size > 0 ? 1 : 0;
  }

  function selectSlot(id) {
    selectedId = id;
    slots.forEach((s) => s.el && s.el.classList.toggle('sel', s.id === id));
    const slot = current();
    $('wfName').textContent = slot.name;
    $('editName').textContent = slot.name;
    syncControls();
    refreshGrid();
    drawWave();
  }

  function syncControls() {
    const s = current();
    $('tone').value = s.tone;   $('toneVal').textContent = s.tone + '%';
    $('comp').value = s.compression; $('compVal').textContent = s.compression + '%';
    $('pitch').value = s.pitch; $('pitchVal').textContent = (s.pitch > 0 ? '+' : '') + s.pitch + ' st';
    $('vol').value = s.volume;  $('volVal').textContent = s.volume + '%';
  }

  /* ----- Layer tabs ----- */
  function buildLayerBar() {
    const bar = $('layerBar');
    bar.innerHTML = '';
    layers.forEach((L, i) => {
      const tab = document.createElement('div');
      tab.className = 'layer-tab' + (i === activeLayer ? ' active' : '');
      tab.innerHTML = `<span class="lname">${L.name}</span>` +
                      (layers.length > 1 ? `<span class="lclose" title="Delete layer">×</span>` : '');
      tab.addEventListener('click', () => switchLayer(i));
      tab.addEventListener('dblclick', () => renameLayer(i));
      const close = tab.querySelector('.lclose');
      if (close) close.addEventListener('click', (e) => { e.stopPropagation(); deleteLayer(i); });
      bar.appendChild(tab);
    });
    const add = document.createElement('button');
    add.className = 'layer-add'; add.textContent = '+'; add.title = 'Add layer';
    add.addEventListener('click', addLayer);
    bar.appendChild(add);
  }

  function switchLayer(i) {
    activeLayer = clamp(0, layers.length - 1, i);
    buildLayerBar(); refreshGrid(); slots.forEach(updateSlotDot);
  }
  function addLayer() {
    layers.push(newLayer('Layer ' + (layers.length + 1)));
    activeLayer = layers.length - 1;
    buildLayerBar(); refreshGrid(); slots.forEach(updateSlotDot);
    toast('Added ' + layers[activeLayer].name);
  }
  function deleteLayer(i) {
    if (layers.length <= 1) return;
    const nm = layers[i].name;
    layers.splice(i, 1);
    if (activeLayer >= layers.length) activeLayer = layers.length - 1;
    else if (activeLayer > i) activeLayer--;
    buildLayerBar(); refreshGrid(); slots.forEach(updateSlotDot);
    toast('Deleted ' + nm);
  }
  function renameLayer(i) {
    const nm = prompt('Rename layer:', layers[i].name);
    if (nm) { layers[i].name = nm.trim().slice(0, 18) || layers[i].name; buildLayerBar(); }
  }

  /* ----------------------------- Waveform ------------------------------ */
  /* Reacts to the selected channel's FX:
       Pitch -> horizontal time scale,  Volume -> amplitude,
       Tone  -> high-frequency detail,  Compression -> dynamic range.       */
  function drawWave() {
    if (!selectedId) return;
    const cv = $('wave'), slot = current();
    const dpr = window.devicePixelRatio || 1;
    const w = cv.clientWidth, h = cv.clientHeight;
    if (w === 0 || h === 0) return;
    cv.width = w * dpr; cv.height = h * dpr;
    const g = cv.getContext('2d');
    g.scale(dpr, dpr);
    g.clearRect(0, 0, w, h);

    g.strokeStyle = '#242424'; g.lineWidth = 1;
    g.beginPath(); g.moveTo(0, h / 2); g.lineTo(w, h / 2); g.stroke();

    const data = slot.buffer.getChannelData(0);
    const rate = Math.pow(2, slot.pitch / 12);   // PITCH
    const vol = slot.volume / 100;               // VOLUME
    const lpCoef = 0.05 + 0.95 * (slot.tone / 100); // TONE (darker => smoother)
    const cpow = 1 - 0.6 * (slot.compression / 100); // COMPRESSION (lower => fatter)

    const baseStep = Math.max(1, data.length / w);
    const span = Math.max(1, Math.floor(baseStep));
    const mn = new Float32Array(w), mx = new Float32Array(w);
    for (let x = 0; x < w; x++) {
      const startF = x * baseStep * rate;
      let lo = 0, hi = 0, any = false;
      for (let j = 0; j < span; j++) {
        const idx = Math.floor(startF + j * rate);
        if (idx < 0 || idx >= data.length) break;
        const v = data[idx];
        if (!any) { lo = hi = v; any = true; } else { if (v < lo) lo = v; if (v > hi) hi = v; }
      }
      mn[x] = any ? lo : 0; mx[x] = any ? hi : 0;
    }
    // TONE: one-pole smoothing across pixels (less high-frequency detail when dark)
    for (let x = 1; x < w; x++) {
      mn[x] = mn[x - 1] + (mn[x] - mn[x - 1]) * lpCoef;
      mx[x] = mx[x - 1] + (mx[x] - mx[x - 1]) * lpCoef;
    }
    const shape = (v) => clamp(-1, 1, Math.sign(v) * Math.pow(Math.abs(v), cpow) * vol);

    g.strokeStyle = slot.color; g.lineWidth = 1;
    g.shadowColor = slot.color; g.shadowBlur = 6;
    g.beginPath();
    for (let x = 0; x < w; x++) {
      const top = (1 - (shape(mx[x]) + 1) / 2) * h;
      const bot = (1 - (shape(mn[x]) + 1) / 2) * h;
      g.moveTo(x + 0.5, top);
      g.lineTo(x + 0.5, Math.max(top + 0.5, bot));
    }
    g.stroke();
    g.shadowBlur = 0;
  }

  /* ===================================================================== */
  /*                            AUDIO PLAYBACK                             */
  /* ===================================================================== */
  function playVoice(slot, midi, time) {
    const src = ctx.createBufferSource();
    src.buffer = slot.buffer;
    const target = midi + keyOffset + slot.pitch;
    src.playbackRate.value = Math.pow(2, (target - ROOT_NOTE) / 12);
    const g = ctx.createGain();
    g.gain.setValueAtTime(0, time);
    g.gain.linearRampToValueAtTime(1, time + 0.004);
    src.connect(g);
    g.connect(slot.filterNode);
    src.start(time);
    src.stop(time + slot.buffer.duration / src.playbackRate.value + 0.05);
  }

  function scheduleNote(step, time) {
    notesQueue.push({ step, time });
    for (const slot of slots) {
      if (slot.muted) continue;                 // muted channels stay silent
      const p = patt(slot);
      if (!p.size) continue;
      for (const key of p) {
        const u = key.indexOf('_');
        const s = +key.slice(u + 1);
        if (s === step && s < steps) playVoice(slot, rowToMidi(+key.slice(0, u)), time);
      }
    }
  }

  function scheduler() {
    while (nextNoteTime < ctx.currentTime + 0.12) {
      scheduleNote(currentStep, nextNoteTime);
      nextNoteTime += secondsPerStep();
      currentStep = (currentStep + 1) % steps;
    }
    timerId = setTimeout(scheduler, 25);
  }

  function play() {
    resumeAudio();
    if (isPlaying) return;
    isPlaying = true;
    notesQueue.length = 0; lastNote = null;
    nextNoteTime = ctx.currentTime + 0.06;
    scheduler();
    updateTransport();
  }
  function pause() { isPlaying = false; clearTimeout(timerId); updateTransport(); }
  function stop() {
    isPlaying = false; clearTimeout(timerId);
    currentStep = 0; notesQueue.length = 0; lastNote = null;
    updateTransport();
  }
  function updateTransport() { $('play').classList.toggle('on', isPlaying); }

  /* ------------------- Animation: meter + playhead --------------------- */
  function frame() {
    analyser.getByteTimeDomainData(meterBuf);
    let sum = 0;
    for (let i = 0; i < meterBuf.length; i++) { const x = (meterBuf[i] - 128) / 128; sum += x * x; }
    const target = isPlaying ? Math.min(100, Math.sqrt(sum / meterBuf.length) * 200) : 0;
    meterLevel += (target - meterLevel) * 0.25;
    $('meter').style.width = (meterLevel < 0.01 ? 0 : meterLevel) + '%';

    const gw = $('gridWrap').clientWidth, line = $('playLine');
    if (isPlaying) {
      while (notesQueue.length && notesQueue[0].time < ctx.currentTime) lastNote = notesQueue.shift();
      if (lastNote) {
        let pos = lastNote.step + (ctx.currentTime - lastNote.time) / secondsPerStep();
        pos = ((pos % steps) + steps) % steps;
        line.style.left = Math.min(pos / steps * gw, gw - 2) + 'px';
        line.style.opacity = 0.9;
      }
    } else {
      line.style.left = (currentStep / steps * gw) + 'px';
      line.style.opacity = currentStep > 0 ? 0.7 : 0.35;
    }
    updateArranger();
    requestAnimationFrame(frame);
  }

  /* ===================================================================== */
  /*                          IMPORT / DRAG & DROP                         */
  /* ===================================================================== */
  async function importFile(file) {
    try {
      const arr = await file.arrayBuffer();
      const audio = await ctx.decodeAudioData(arr);
      const name = file.name.replace(/\.[^.]+$/, '').slice(0, 18) || 'Sample';
      const slot = addSlot(name, audio);
      buildSlots();
      selectSlot(slot.id);
      toast('Imported "' + name + '"');
    } catch (err) {
      console.error(err);
      toast('Could not decode that audio file');
    }
  }

  /* ===================================================================== */
  /*                          SAVE / LOAD / EXPORT                         */
  /* ===================================================================== */
  function saveProject() {
    const d = { v: 3, bpm, key: keyOffset, steps, activeLayer, sel: selectedId, layers: [], fx: {}, mutes: {} };
    layers.forEach((L) => {
      const pat = {};
      for (const id in L.patterns) if (L.patterns[id].size) pat[id] = [...L.patterns[id]];
      d.layers.push({ name: L.name, patterns: pat });
    });
    slots.forEach((s) => {
      d.fx[s.id] = { tone: s.tone, compression: s.compression, volume: s.volume, pitch: s.pitch };
      if (s.muted) d.mutes[s.id] = true;
    });
    try { localStorage.setItem('beatfx_project', JSON.stringify(d)); toast('Project saved'); }
    catch (e) { toast('Save failed'); }
  }

  function loadProject() {
    let raw;
    try { raw = localStorage.getItem('beatfx_project'); } catch (e) { return false; }
    if (!raw) return false;
    let d; try { d = JSON.parse(raw); } catch (e) { return false; }

    setBpm(d.bpm != null ? d.bpm : 120);
    setKey(d.key != null ? d.key : 0);
    steps = [16, 32, 48, 64].includes(d.steps) ? d.steps : 16;
    $('length').value = steps;

    if (Array.isArray(d.layers) && d.layers.length) {
      layers = d.layers.map((L) => {
        const lay = newLayer(L.name || 'Layer');
        if (L.patterns) for (const id in L.patterns) lay.patterns[id] = new Set(L.patterns[id]);
        return lay;
      });
    } else {
      layers = [newLayer('Layer 1')];
    }
    activeLayer = clamp(0, layers.length - 1, d.activeLayer || 0);

    if (d.fx) for (const id in d.fx) {
      const slot = slots.find((s) => s.id === id);
      if (slot) {
        const f = d.fx[id];
        if (f.tone != null) slot.tone = f.tone;
        if (f.compression != null) slot.compression = f.compression;
        if (f.volume != null) slot.volume = f.volume;
        if (f.pitch != null) slot.pitch = f.pitch;
      }
    }
    slots.forEach((s) => { s.muted = !!(d.mutes && d.mutes[s.id]); applySlotFx(s); });

    selectedId = (d.sel && slots.find((s) => s.id === d.sel)) ? d.sel : slots[0].id;
    return true;
  }

  // Offline render of the ACTIVE layer, respecting per-channel FX + mute.
  // `tail` extra seconds let final notes ring out (0 = seamless loop for bounces).
  async function renderLayerOffline(loops, tail) {
    const sr = ctx.sampleRate, sps = secondsPerStep();
    const loopDur = steps * sps;
    const total = loopDur * loops + tail;
    const off = new OfflineAudioContext(2, Math.max(1, Math.ceil(total * sr)), sr);

    const master = off.createGain();
    master.gain.value = masterOut.gain.value;
    master.connect(off.destination);

    const inputs = new Map();
    for (const slot of slots) {
      if (slot.muted) continue;
      const f = off.createBiquadFilter();
      f.type = 'lowpass'; f.Q.value = 0.7; f.frequency.value = slot.filterNode.frequency.value;
      const c = off.createDynamicsCompressor();
      c.threshold.value = slot.compNode.threshold.value;
      c.ratio.value = slot.compNode.ratio.value;
      c.knee.value = slot.compNode.knee.value;
      c.attack.value = slot.compNode.attack.value;
      c.release.value = slot.compNode.release.value;
      const g = off.createGain(); g.gain.value = slot.volume / 100;
      f.connect(c); c.connect(g); g.connect(master);
      inputs.set(slot.id, f);
    }

    for (let loop = 0; loop < loops; loop++) {
      for (let step = 0; step < steps; step++) {
        const t = loop * loopDur + step * sps;
        for (const slot of slots) {
          if (slot.muted) continue;
          const p = patt(slot);
          if (!p.size) continue;
          for (const key of p) {
            const u = key.indexOf('_');
            const s = +key.slice(u + 1);
            if (s !== step || s >= steps) continue;
            const midi = rowToMidi(+key.slice(0, u));
            const src = off.createBufferSource();
            src.buffer = slot.buffer;
            src.playbackRate.value = Math.pow(2, (midi + keyOffset + slot.pitch - ROOT_NOTE) / 12);
            const vg = off.createGain();
            vg.gain.setValueAtTime(0, t);
            vg.gain.linearRampToValueAtTime(1, t + 0.004);
            src.connect(vg); vg.connect(inputs.get(slot.id));
            src.start(t);
            src.stop(t + slot.buffer.duration / src.playbackRate.value + 0.05);
          }
        }
      }
    }
    return off.startRendering();
  }

  async function exportWav() {
    toast('Rendering WAV…');
    const rendered = await renderLayerOffline(2, 1.8);
    download(encodeWav(rendered), 'beatfx-loop.wav');
    toast('Exported beatfx-loop.wav');
  }

  // "Bounce": freeze the current layer's beat into a reusable Sound Object.
  async function bounceToSoundObject() {
    if (!slots.some((s) => !s.muted && patt(s).size)) { toast('This layer is empty — add some beats first'); return; }
    toast('Bouncing beat…');
    const buf = await renderLayerOffline(BOUNCE_LOOPS, 0);   // no tail -> clean re-trigger loop
    const so = {
      id: 'so' + (soSeq++), name: 'Sound object ' + (soNum++),
      color: SO_COLORS[(soundObjects.length) % SO_COLORS.length],
      buffer: buf, duration: buf.duration
    };
    soundObjects.push(so);
    refreshSoundObjectsUI();
    toast('Created "' + so.name + '" (' + so.duration.toFixed(1) + 's) — open Create Tab');
  }

  function encodeWav(buffer) {
    const numCh = buffer.numberOfChannels, sr = buffer.sampleRate, len = buffer.length;
    const blockAlign = numCh * 2, dataLen = len * blockAlign;
    const ab = new ArrayBuffer(44 + dataLen), dv = new DataView(ab);
    let o = 0;
    const ws = (s) => { for (let i = 0; i < s.length; i++) dv.setUint8(o++, s.charCodeAt(i)); };
    const u32 = (v) => { dv.setUint32(o, v, true); o += 4; };
    const u16 = (v) => { dv.setUint16(o, v, true); o += 2; };
    ws('RIFF'); u32(36 + dataLen); ws('WAVE');
    ws('fmt '); u32(16); u16(1); u16(numCh); u32(sr); u32(sr * blockAlign); u16(blockAlign); u16(16);
    ws('data'); u32(dataLen);
    const chans = [];
    for (let c = 0; c < numCh; c++) chans.push(buffer.getChannelData(c));
    for (let i = 0; i < len; i++) {
      for (let c = 0; c < numCh; c++) {
        const v = clamp(-1, 1, chans[c][i]);
        dv.setInt16(o, v < 0 ? v * 0x8000 : v * 0x7fff, true); o += 2;
      }
    }
    return new Blob([ab], { type: 'audio/wav' });
  }

  function download(blob, name) {
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  /* ------------------------------- Toast ------------------------------- */
  let toastT;
  function toast(msg) {
    const t = $('toast');
    t.textContent = msg;
    t.style.opacity = 1; t.style.transform = 'translateX(-50%) translateY(0)';
    clearTimeout(toastT);
    toastT = setTimeout(() => {
      t.style.opacity = 0; t.style.transform = 'translateX(-50%) translateY(10px)';
    }, 1800);
  }

  /* ===================================================================== */
  /*                      VIEWS  (Studio  <->  Create)                     */
  /* ===================================================================== */
  function toggleRail() { railExpanded = !railExpanded; $('rail').classList.toggle('expanded', railExpanded); }

  function showView(v) {
    view = v;
    $('studioView').classList.toggle('hidden', v !== 'studio');
    $('createView').classList.toggle('hidden', v !== 'create');
    $('navStudio').classList.toggle('active', v === 'studio');
    $('navCreate').classList.toggle('active', v === 'create');
    if (v === 'create') { if (isPlaying) stop(); layoutArranger(); }
    else { arrStopTransport(); }
  }

  function refreshSoundObjectsUI() {
    $('soCount').textContent = soundObjects.length;
    buildAddMenu();
  }

  /* ----- "Add sound object" dropdown ----- */
  function buildAddMenu() {
    const menu = $('addSoMenu');
    menu.innerHTML = '';
    if (!soundObjects.length) {
      menu.innerHTML = '<div class="so-empty">No sound objects yet.<br>Go to <b>Studio</b>, make a beat, then hit <b>★ Sound Object</b>.</div>';
      return;
    }
    soundObjects.forEach((o) => {
      const row = document.createElement('div');
      row.className = 'so-row';
      row.innerHTML =
        `<span class="so-swatch" style="background:${o.color};color:${o.color}"></span>` +
        `<span class="so-name">${o.name}</span>` +
        `<span class="so-dur">${o.duration.toFixed(1)}s</span>` +
        `<span class="so-del" title="Delete sound object">🗑</span>`;
      row.querySelector('.so-name').addEventListener('click', () => { addClip(o.id); closeAddMenu(); });
      row.querySelector('.so-swatch').addEventListener('click', () => { addClip(o.id); closeAddMenu(); });
      row.querySelector('.so-del').addEventListener('click', (e) => { e.stopPropagation(); deleteSoundObject(o.id); });
      row.addEventListener('dblclick', () => renameSoundObject(o.id));
      menu.appendChild(row);
    });
  }
  const openAddMenu  = () => { buildAddMenu(); $('addSoMenu').classList.remove('hidden'); };
  const closeAddMenu = () => $('addSoMenu').classList.add('hidden');
  const toggleAddMenu = () => $('addSoMenu').classList.contains('hidden') ? openAddMenu() : closeAddMenu();

  function deleteSoundObject(id) {
    const i = soundObjects.findIndex((o) => o.id === id);
    if (i < 0) return;
    const nm = soundObjects[i].name;
    soundObjects.splice(i, 1);
    for (let c = clips.length - 1; c >= 0; c--) if (clips[c].objId === id) clips.splice(c, 1);
    refreshSoundObjectsUI(); renderClips();
    toast('Deleted ' + nm);
  }
  function renameSoundObject(id) {
    const o = soundObjects.find((x) => x.id === id);
    if (!o) return;
    const nm = prompt('Rename sound object:', o.name);
    if (nm) { o.name = nm.trim().slice(0, 22) || o.name; refreshSoundObjectsUI(); renderClips(); }
  }

  /* ===================================================================== */
  /*                       ARRANGER  (timeline)                            */
  /* ===================================================================== */
  const snapTime = (t) => Math.round(t * 4) / 4;     // 0.25s grid
  const fmtTime = (s) => { s = Math.max(0, s); return Math.floor(s / 60) + ':' + String(Math.floor(s % 60)).padStart(2, '0'); };

  function firstFreeLane(start, length) {
    for (let lane = 0; lane < LANES; lane++) {
      const clash = clips.some((c) => c.lane === lane && start < c.start + c.length && start + length > c.start);
      if (!clash) return lane;
    }
    return 0;
  }

  function addClip(objId) {
    const o = soundObjects.find((x) => x.id === objId);
    if (!o) return;
    const start = snapTime(clamp(0, Math.max(0, arrLength - o.duration), arrPlayhead));
    clips.push({ id: 'c' + (clipSeq++), objId, lane: firstFreeLane(start, o.duration), start, length: o.duration });
    renderClips();
    toast('Placed "' + o.name + '"');
  }
  function removeClip(id) { const i = clips.findIndex((c) => c.id === id); if (i >= 0) { clips.splice(i, 1); renderClips(); } }

  function layoutArranger() {
    const h = LANES * LANE_H;
    const w = Math.max(arrLength * PPS, $('arrScroll').clientWidth || 0);   // fill viewport for short songs
    $('arrContent').style.width = w + 'px';
    $('arrContent').style.height = h + 'px';
    $('arrTracks').style.height = h + 'px';
    $('arrTracks').style.backgroundImage =
      `repeating-linear-gradient(to bottom, transparent 0, transparent ${LANE_H - 1}px, #242424 ${LANE_H - 1}px, #242424 ${LANE_H}px),` +
      `repeating-linear-gradient(to right, transparent 0, transparent ${10 * PPS - 1}px, #1e1e1e ${10 * PPS - 1}px, #1e1e1e ${10 * PPS}px)`;
    $('arrPlay').style.height = h + 'px';
    $('ruler').style.width = w + 'px';
    $('arrLen').value = arrLength;
    buildRuler();
    renderClips();
    $('arrTotal').textContent = fmtTime(arrLength);
    updateArrPlayhead();
  }

  function buildRuler() {
    const t = $('rulerTicks');
    t.innerHTML = '';
    t.style.width = (arrLength * PPS) + 'px';
    for (let s = 0; s <= arrLength; s += 10) {
      const tick = document.createElement('div');
      tick.className = 'ruler-tick';
      tick.style.left = (s * PPS) + 'px';
      tick.textContent = s + 's';
      t.appendChild(tick);
    }
  }

  // Keep the bottom ruler horizontally aligned with the scrolling lanes.
  function syncRulerScroll() { $('ruler').style.transform = 'translateX(' + (-$('arrScroll').scrollLeft) + 'px)'; }
  const timeFromClientX = (clientX) => {
    const rect = $('arrRulerWrap').getBoundingClientRect();
    return clamp(0, arrLength, (clientX - rect.left + $('arrScroll').scrollLeft) / PPS);
  };

  function renderClips() {
    const wrap = $('arrClips');
    wrap.innerHTML = '';
    clips.forEach((clip) => {
      const o = soundObjects.find((x) => x.id === clip.objId);
      if (!o) return;
      const div = document.createElement('div');
      div.className = 'clip';
      div.style.left = (clip.start * PPS) + 'px';
      div.style.width = Math.max(CLIP_MIN * PPS, clip.length * PPS) + 'px';
      div.style.top = (clip.lane * LANE_H + 6) + 'px';
      div.style.height = (LANE_H - 12) + 'px';
      div.style.background = o.color;
      div.innerHTML = `<span class="clip-rmv" title="Remove">×</span><span class="clip-name">${o.name}</span><span class="clip-rsz"></span>`;
      div.querySelector('.clip-rmv').addEventListener('pointerdown', (e) => { e.stopPropagation(); removeClip(clip.id); });
      makeClipInteractive(div, clip);
      wrap.appendChild(div);
    });
  }

  function makeClipInteractive(div, clip) {
    // body drag -> move in time + lane
    div.addEventListener('pointerdown', (e) => {
      if (e.target.classList.contains('clip-rsz') || e.target.classList.contains('clip-rmv')) return;
      e.preventDefault();
      try { div.setPointerCapture(e.pointerId); } catch (err) {}
      div.classList.add('dragging');
      const sx = e.clientX, sy = e.clientY, oStart = clip.start, oLane = clip.lane;
      const move = (ev) => {
        clip.start = clamp(0, Math.max(0, arrLength - clip.length), snapTime(oStart + (ev.clientX - sx) / PPS));
        clip.lane = clamp(0, LANES - 1, oLane + Math.round((ev.clientY - sy) / LANE_H));
        div.style.left = (clip.start * PPS) + 'px';
        div.style.top = (clip.lane * LANE_H + 6) + 'px';
      };
      const up = () => { div.classList.remove('dragging'); div.removeEventListener('pointermove', move); div.removeEventListener('pointerup', up); };
      div.addEventListener('pointermove', move);
      div.addEventListener('pointerup', up);
    });
    // right edge -> resize (loops the bounced phrase to fill)
    const rsz = div.querySelector('.clip-rsz');
    rsz.addEventListener('pointerdown', (e) => {
      e.preventDefault(); e.stopPropagation();
      try { rsz.setPointerCapture(e.pointerId); } catch (err) {}
      const sx = e.clientX, oLen = clip.length;
      const move = (ev) => {
        clip.length = clamp(CLIP_MIN, arrLength - clip.start, snapTime(oLen + (ev.clientX - sx) / PPS));
        div.style.width = (clip.length * PPS) + 'px';
      };
      const up = () => { rsz.removeEventListener('pointermove', move); rsz.removeEventListener('pointerup', up); };
      rsz.addEventListener('pointermove', move);
      rsz.addEventListener('pointerup', up);
    });
  }

  function scrubTo(clientX, el) {
    const rect = el.getBoundingClientRect();
    arrPlayhead = snapTime(clamp(0, arrLength, (clientX - rect.left) / PPS));
    if (arrPlaying) scheduleArr();
    updateArrPlayhead();
  }

  /* ----- Arranger playback ----- */
  function stopArrSources() { arrSources.forEach((s) => { try { s.stop(); } catch (e) {} }); arrSources = []; }

  function scheduleArr() {
    stopArrSources();
    const now = ctx.currentTime + 0.06;
    arrStartCtxTime = now - arrPlayhead;
    for (const clip of clips) {
      const o = soundObjects.find((x) => x.id === clip.objId);
      if (!o) continue;
      const dur = o.buffer.duration, clipEnd = clip.start + clip.length;
      for (let t = clip.start; t < clipEnd - 1e-3; t += dur) {        // re-trigger the phrase to fill the clip
        const segEnd = Math.min(t + dur, clipEnd);
        if (segEnd <= arrPlayhead) continue;                          // already passed
        const playFrom = Math.max(t, arrPlayhead);
        const src = ctx.createBufferSource();
        src.buffer = o.buffer;
        const g = ctx.createGain();
        const when = arrStartCtxTime + playFrom;
        g.gain.setValueAtTime(0, when);
        g.gain.linearRampToValueAtTime(1, when + 0.004);
        src.connect(g); g.connect(masterOut);
        src.start(when, playFrom - t, (segEnd - playFrom) + 0.03);    // offset into buffer, duration
        arrSources.push(src);
      }
    }
  }

  function arrPlay() {
    resumeAudio();
    if (arrPlaying) { arrPause(); return; }
    if (arrPlayhead >= arrLength - 1e-3) arrPlayhead = 0;
    arrPlaying = true;
    scheduleArr();
    updateArrTransport();
  }
  function arrPause() { arrPlaying = false; stopArrSources(); updateArrTransport(); }
  function arrStopTransport() { arrPlaying = false; stopArrSources(); updateArrTransport(); }
  function arrRewind() { arrPlayhead = 0; if (arrPlaying) scheduleArr(); updateArrPlayhead(); }
  function arrForward() { arrPlayhead = clamp(0, arrLength, arrPlayhead + 10); if (arrPlaying) scheduleArr(); updateArrPlayhead(); }
  function updateArrTransport() { const b = $('arrPlayBtn'); b.classList.toggle('on', arrPlaying); b.innerHTML = arrPlaying ? PAUSE_SVG : PLAY_SVG; }

  function updateArrPlayhead() {
    const x = (arrPlayhead * PPS) + 'px';
    $('arrPlay').style.left = x;
    $('arrGlider').style.left = x;
    $('arrTime').textContent = fmtTime(arrPlayhead);
  }

  // Called every animation frame (no-op unless the Create tab is active & playing).
  function updateArranger() {
    if (view !== 'create' || !arrPlaying) return;
    arrPlayhead = ctx.currentTime - arrStartCtxTime;
    if (arrPlayhead >= arrLength) { arrPlayhead = arrLength; arrPause(); }
    updateArrPlayhead();
  }

  // Render the whole arrangement offline -> WAV.
  async function exportSong() {
    if (!clips.length) { toast('Add some sound objects to the timeline first'); return; }
    toast('Rendering song…');
    const sr = ctx.sampleRate;
    let end = 0; clips.forEach((c) => { end = Math.max(end, c.start + c.length); });
    const off = new OfflineAudioContext(2, Math.ceil((end + 2) * sr), sr);
    const master = off.createGain(); master.gain.value = masterOut.gain.value; master.connect(off.destination);
    for (const clip of clips) {
      const o = soundObjects.find((x) => x.id === clip.objId);
      if (!o) continue;
      const dur = o.buffer.duration, clipEnd = clip.start + clip.length;
      for (let t = clip.start; t < clipEnd - 1e-3; t += dur) {
        const segEnd = Math.min(t + dur, clipEnd);
        const src = off.createBufferSource(); src.buffer = o.buffer;
        const g = off.createGain();
        g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(1, t + 0.004);
        src.connect(g); g.connect(master);
        src.start(t); src.stop(segEnd + 0.03);
      }
    }
    const rendered = await off.startRendering();
    download(encodeWav(rendered), 'beatfx-song.wav');
    toast('Exported beatfx-song.wav');
  }

  /* ===================================================================== */
  /*                       PRE-MADE SONGS  (demos)                         */
  /* ===================================================================== */
  // ICC = Interstellar "Cornfield Chase": a fast, rolling organ arpeggio over
  // F – C – Dm – B♭ (8 sixteenths per chord, 32 steps), with swelling strings.
  const ICC_ARP = [
    [65, 0], [69, 1], [72, 2], [77, 3], [72, 4], [69, 5], [65, 6], [69, 7],          // F
    [60, 8], [64, 9], [67, 10], [72, 11], [67, 12], [64, 13], [60, 14], [64, 15],    // C
    [62, 16], [65, 17], [69, 18], [74, 19], [69, 20], [65, 21], [62, 22], [65, 23],  // Dm
    [58, 24], [62, 25], [65, 26], [70, 27], [65, 28], [62, 29], [58, 30], [62, 31]   // B♭
  ];
  // Warm string pad — root + fifth held under each chord.
  const ICC_PAD = [[53, 0], [60, 0], [48, 8], [55, 8], [50, 16], [57, 16], [46, 24], [53, 24]];
  // Soaring string melody — one long held note per chord.
  const ICC_MEL = [[69, 0], [67, 8], [65, 16], [65, 24]];
  // Faint bell sparkle doubling the melody an octave up (full section only).
  const ICC_BELL = [[81, 0], [79, 8], [77, 16], [77, 24]];
  const ICC_BASS = [[41, 0], [36, 8], [38, 16], [46, 24]];
  const ICC_KICK = [[60, 0], [60, 8], [60, 16], [60, 24]];
  const ICC_TOM  = [[60, 4], [60, 12], [60, 20], [60, 28]];

  const PREMADE = [
    {
      name: 'ICC', sub: 'Interstellar — Cornfield Chase', color: '#22d3ee', icon: '🌽',
      bpm: 110, key: 0, steps: 32, bounceBars: 2,
      layers: [
        { name: 'Arpeggio',      parts: { 'Organ': ICC_ARP } },
        { name: 'Arp + Strings', parts: { 'Organ': ICC_ARP, 'Orchestra 2': ICC_PAD, 'Orchestra 1': ICC_MEL } },
        { name: 'Full Build',    parts: { 'Organ': ICC_ARP, 'Orchestra 2': ICC_PAD, 'Orchestra 1': ICC_MEL, 'Bells': ICC_BELL, 'Bass': ICC_BASS, 'Kick': ICC_KICK, 'Tom': ICC_TOM } }
      ],
      // Seamless build: intro arpeggio -> + strings -> full (x2), laid back-to-back.
      build: [
        { obj: 0, lane: 0, loops: 1 },
        { obj: 1, lane: 1, loops: 1 },
        { obj: 2, lane: 2, loops: 2 }
      ]
    },
    {
      name: 'Lo-Fi Dream', sub: 'chilled hip-hop', color: '#b388ff', icon: '🌙',
      bpm: 75, key: 0, steps: 16,
      layers: [{ name: 'Main', parts: {
        'Kick': [[60, 0], [60, 8], [60, 11]],
        'Snare': [[60, 4], [60, 12]],
        'Hi-Hat': [[60, 0], [60, 2], [60, 4], [60, 6], [60, 8], [60, 10], [60, 12], [60, 14]],
        'Bass': [[48, 0], [46, 4], [48, 8], [51, 12]],
        'Keys': [[60, 0], [63, 0], [67, 0], [58, 8], [62, 8], [65, 8]]
      } }]
    },
    {
      name: 'Night Trap', sub: '808s & rapid hats', color: '#ff5252', icon: '🔥',
      bpm: 140, key: 0, steps: 16,
      layers: [{ name: 'Main', parts: {
        'Kick': [[60, 0], [60, 6], [60, 10]],
        'Clap': [[60, 4], [60, 12]],
        'Hi-Hat': [[60, 0], [60, 2], [60, 4], [60, 6], [60, 8], [60, 9], [60, 10], [60, 12], [60, 14], [60, 15]],
        'Bass': [[36, 0], [36, 6], [43, 10], [41, 12]]
      } }]
    },
    {
      name: 'House Groove', sub: 'four-on-the-floor', color: '#00e676', icon: '🏠',
      bpm: 124, key: 0, steps: 16,
      layers: [{ name: 'Main', parts: {
        'Kick': [[60, 0], [60, 4], [60, 8], [60, 12]],
        'Hi-Hat': [[60, 2], [60, 6], [60, 10], [60, 14]],
        'Clap': [[60, 4], [60, 12]],
        'Bass': [[48, 2], [48, 6], [48, 10], [48, 14]],
        'Pluck': [[72, 0], [67, 4], [72, 8], [70, 12]]
      } }]
    },
    {
      name: 'Cinematic Rise', sub: 'epic strings & choir', color: '#ffd166', icon: '🎬',
      bpm: 90, key: 0, steps: 16,
      layers: [{ name: 'Main', parts: {
        'Orchestra 2': [[48, 0], [55, 0], [50, 8], [53, 8]],
        'Choir': [[60, 0], [60, 8]],
        'Tom': [[60, 4], [60, 12]],
        'Bass': [[41, 0], [41, 8]]
      } }]
    }
  ];

  function buildPremadeMenu() {
    const m = $('premadeMenu'); m.innerHTML = '';
    PREMADE.forEach((song) => {
      const row = document.createElement('div'); row.className = 'pm-row';
      row.innerHTML =
        `<span class="pm-ico" style="background:${song.color}22;color:${song.color}">${song.icon}</span>` +
        `<span class="pm-name">${song.name}<div class="pm-sub">${song.sub}</div></span>`;
      row.addEventListener('click', () => { closePremadeMenu(); loadPremade(song); });
      m.appendChild(row);
    });
  }
  function openPremadeMenu(btn) {
    buildPremadeMenu();
    const m = $('premadeMenu'); m.classList.remove('hidden');
    const r = btn.getBoundingClientRect();
    m.style.left = Math.min(r.left, window.innerWidth - m.offsetWidth - 12) + 'px';
    m.style.top = (r.bottom + 8) + 'px';
  }
  const closePremadeMenu = () => $('premadeMenu').classList.add('hidden');
  const togglePremade = (btn) => $('premadeMenu').classList.contains('hidden') ? openPremadeMenu(btn) : closePremadeMenu();

  function partsToPatterns(parts) {
    const out = {};
    for (const inst in parts) {
      const slot = slots.find((s) => s.name === inst);
      if (!slot) continue;
      const set = new Set();
      parts[inst].forEach(([m, st]) => { const r = midiToRow(m); if (r >= 0 && r < ROWS && st < steps) set.add(r + '_' + st); });
      out[slot.id] = set;
    }
    return out;
  }

  async function loadPremade(song) {
    if (isPlaying) stop();
    arrStopTransport();
    toast('Loading ' + song.name + '…');
    setBpm(song.bpm); setKey(song.key || 0);
    steps = [16, 32, 48, 64].includes(song.steps) ? song.steps : 16;
    $('length').value = steps;

    slots.forEach((s) => { s.muted = false; s.tone = DEF_TONE; s.compression = DEF_COMP; s.volume = DEF_VOL; s.pitch = DEF_PITCH; applySlotFx(s); });
    layers = song.layers.map((L) => ({ name: L.name, patterns: partsToPatterns(L.parts) }));
    activeLayer = 0;
    buildRoll(); buildLayerBar(); selectSlot(slots[0].id); slots.forEach(updateSlotDot);

    soundObjects.length = 0; clips.length = 0; soNum = 1;
    if (song.build) {
      for (let i = 0; i < layers.length; i++) {
        activeLayer = i;
        const buf = await renderLayerOffline(song.bounceBars || 4, 0);
        soundObjects.push({ id: 'so' + (soSeq++), name: layers[i].name, color: SO_COLORS[i % SO_COLORS.length], buffer: buf, duration: buf.duration });
      }
      activeLayer = 0; refreshGrid(); buildLayerBar(); slots.forEach(updateSlotDot);
      // Lay sections back-to-back using the real bounced durations -> seamless build.
      let t = 0;
      song.build.forEach((a) => {
        const o = soundObjects[a.obj]; if (!o) return;
        const len = (a.loops || 1) * o.duration;
        clips.push({ id: 'c' + (clipSeq++), objId: o.id, lane: clamp(0, LANES - 1, a.lane), start: +t.toFixed(3), length: +len.toFixed(3) });
        t += len;
      });
      arrLength = Math.max(40, Math.ceil(t + 4));
    }
    refreshSoundObjectsUI(); layoutArranger();
    toast('Loaded ' + song.name + (song.build ? ' — open Create Tab ▶' : ''));
  }

  /* ===================================================================== */
  /*                         TUTORIAL  (guided tour)                       */
  /* ===================================================================== */
  const TOUR = [
    { view: 'studio', sel: null, title: 'Welcome to BeatFX 🎵', text: 'A quick self-paced tour of what everything does. Use Next / Back, or press Esc to leave any time.' },
    { view: 'studio', sel: '#rail', title: 'Navigation', text: 'Switch between the <b>Studio</b> (make beats) and the <b>Create Tab</b> (arrange beats into songs). Click ☰ to expand the labels.' },
    { view: 'studio', sel: '#premadeStudio', title: 'Pre-Made Songs', text: 'Instantly load a ready-made track — including <b>ICC</b> (Interstellar – Cornfield Chase) — with all its layers and sound objects.' },
    { view: 'studio', sel: '#key', title: 'Key, Tempo & Length', text: 'Pick the musical key, set the BPM, and choose how many steps (16–64) each pattern has.' },
    { view: 'studio', sel: '#play', title: 'Transport', text: 'Play, pause and stop your beat. Tip: the <b>Spacebar</b> also toggles play / pause.' },
    { view: 'studio', sel: '#slots', title: 'Instruments', text: '15 built-in instruments. Click one to edit it; hit its <b>M</b> to mute it so you can hear the rest. You can drop in your own audio file too.' },
    { view: 'studio', sel: '#gridWrap', title: 'Piano Roll', text: 'Click cells to place notes — up/down is pitch, left/right is time. Click-and-drag to paint a run of notes.' },
    { view: 'studio', sel: '#layerBar', title: 'Layers', text: 'Each layer is a separate pattern sheet. Build a verse on one and a chorus on another, then switch with these tabs.' },
    { view: 'studio', sel: '#tone', title: 'Per-Channel FX', text: 'Tone, Compression, Pitch and Volume are independent for every instrument — and the waveform reacts as you turn them.' },
    { view: 'studio', sel: '#bounce', title: 'Bounce → Sound Object', text: 'Freeze the current layer into a reusable <b>Sound Object</b> you can arrange into a full song.' },
    { view: 'studio', sel: '#export', title: 'Save & Export', text: '<b>Save</b> keeps the project in your browser; <b>Export WAV</b> renders the loop to an audio file.' },
    { view: 'create', sel: '#addSo', title: 'Create Tab — Add', text: "You're now in the arranger. Click here to drop your bounced sound objects onto the timeline." },
    { view: 'create', sel: '#arrTracks', title: 'Arrange', text: 'Drag clips to move them in time or between rows, drag the right edge to stretch them (the phrase loops), and remove with the ×.' },
    { view: 'create', sel: '#arrRulerWrap', title: 'Timeline & Glider', text: 'The bottom timeline shows your position. Drag the white <b>glider</b> (or click the ruler) to scrub anywhere in the song.' },
    { view: 'create', sel: '#exportSong', title: 'Export Song', text: 'Happy with the arrangement? Bounce the whole thing down to a single WAV.' },
    { view: 'create', sel: null, title: "You're all set! 🚀", text: 'Make a beat → bounce it → arrange it → export it. Have fun building tracks with BeatFX!' }
  ];
  let tourIdx = -1, tourKeyHandler = null;

  function startTour() {
    closePremadeMenu();
    tourKeyHandler = (e) => {
      if (e.key === 'Escape') tourEnd();
      else if (e.key === 'ArrowRight') { if (tourIdx < TOUR.length - 1) tourShow(tourIdx + 1); }
      else if (e.key === 'ArrowLeft') { if (tourIdx > 0) tourShow(tourIdx - 1); }
    };
    document.addEventListener('keydown', tourKeyHandler);
    tourShow(0);
  }
  function tourEnd() {
    tourIdx = -1;
    $('tourSpot').style.display = 'none';
    $('tourTip').style.display = 'none';
    if (tourKeyHandler) { document.removeEventListener('keydown', tourKeyHandler); tourKeyHandler = null; }
  }
  function tourShow(i) {
    tourIdx = i;
    const step = TOUR[i];
    if (step.view && view !== step.view) showView(step.view);
    renderTip();
    requestAnimationFrame(() => requestAnimationFrame(positionTour));
  }
  function renderTip() {
    const step = TOUR[tourIdx], tip = $('tourTip');
    tip.innerHTML =
      `<h4>${step.title}</h4><p>${step.text}</p>` +
      `<div class="tt-bar"><span class="tt-step">${tourIdx + 1} / ${TOUR.length}</span>` +
      (tourIdx > 0 ? `<button class="tt-btn" id="ttPrev">Back</button>` : '') +
      `<button class="tt-btn" id="ttSkip">Skip</button>` +
      `<button class="tt-btn primary" id="ttNext">${tourIdx === TOUR.length - 1 ? 'Finish' : 'Next'}</button></div>`;
    tip.style.display = 'block';
    const prev = $('ttPrev'); if (prev) prev.onclick = () => tourShow(tourIdx - 1);
    $('ttSkip').onclick = tourEnd;
    $('ttNext').onclick = () => (tourIdx === TOUR.length - 1 ? tourEnd() : tourShow(tourIdx + 1));
  }
  function positionTour() {
    if (tourIdx < 0) return;
    const step = TOUR[tourIdx], spot = $('tourSpot'), tip = $('tourTip');
    const el = step.sel ? document.querySelector(step.sel) : null;
    if (el && el.offsetParent !== null) {
      el.scrollIntoView({ block: 'nearest', inline: 'nearest' });
      const r = el.getBoundingClientRect(), pad = 6;
      spot.style.display = 'block';
      spot.style.left = (r.left - pad) + 'px'; spot.style.top = (r.top - pad) + 'px';
      spot.style.width = (r.width + pad * 2) + 'px'; spot.style.height = (r.height + pad * 2) + 'px';
      const tipW = 300, tipH = tip.offsetHeight || 150;
      let top = r.bottom + 12, left = clamp(12, window.innerWidth - tipW - 12, r.left);
      if (top + tipH > window.innerHeight - 12) top = Math.max(12, r.top - tipH - 12);
      tip.style.left = left + 'px'; tip.style.top = top + 'px';
    } else {
      spot.style.display = 'none';
      tip.style.left = (window.innerWidth / 2 - 150) + 'px';
      tip.style.top = (window.innerHeight / 2 - (tip.offsetHeight || 150) / 2) + 'px';
    }
  }

  function wireArranger() {
    $('railToggle').addEventListener('click', toggleRail);
    $('navStudio').addEventListener('click', () => showView('studio'));
    $('navCreate').addEventListener('click', () => showView('create'));
    $('bounce').addEventListener('click', bounceToSoundObject);

    $('addSo').addEventListener('click', (e) => { e.stopPropagation(); toggleAddMenu(); });
    document.addEventListener('click', (e) => {
      if (!$('addSo').contains(e.target) && !$('addSoMenu').contains(e.target)) closeAddMenu();
    });

    $('arrLen').addEventListener('change', () => { arrLength = clamp(20, 600, +$('arrLen').value | 0); $('arrLen').value = arrLength; layoutArranger(); });
    $('arrPlayBtn').addEventListener('click', arrPlay);
    $('arrRew').addEventListener('click', arrRewind);
    $('arrFwd').addEventListener('click', arrForward);
    $('exportSong').addEventListener('click', exportSong);

    // bottom-timeline scrubbing (ruler click + draggable glider)
    const scrub = (clientX) => { arrPlayhead = snapTime(timeFromClientX(clientX)); if (arrPlaying) scheduleArr(); updateArrPlayhead(); };
    $('arrRulerWrap').addEventListener('pointerdown', (e) => { if (!e.target.closest('#arrGlider')) scrub(e.clientX); });
    const glider = $('arrGlider');
    glider.addEventListener('pointerdown', (e) => {
      e.preventDefault(); e.stopPropagation();
      try { glider.setPointerCapture(e.pointerId); } catch (err) {}
      const move = (ev) => scrub(ev.clientX);
      const up = () => { glider.removeEventListener('pointermove', move); glider.removeEventListener('pointerup', up); };
      glider.addEventListener('pointermove', move);
      glider.addEventListener('pointerup', up);
    });
    $('arrScroll').addEventListener('scroll', syncRulerScroll);
    $('arrTracks').addEventListener('pointerdown', (e) => { if (e.target === $('arrTracks') || e.target === $('arrClips')) scrub(e.clientX); });

    // Pre-made songs + tutorial buttons (present in both views)
    $('premadeStudio').addEventListener('click', (e) => { e.stopPropagation(); togglePremade(e.currentTarget); });
    $('premadeCreate').addEventListener('click', (e) => { e.stopPropagation(); togglePremade(e.currentTarget); });
    document.addEventListener('click', (e) => {
      if (!$('premadeMenu').contains(e.target) && !e.target.closest('#premadeStudio') && !e.target.closest('#premadeCreate')) closePremadeMenu();
    });
    $('tutStudio').addEventListener('click', startTour);
    $('tutCreate').addEventListener('click', startTour);
    window.addEventListener('resize', () => { if (view === 'create') layoutArranger(); if (tourIdx >= 0) positionTour(); });
  }

  /* ===================================================================== */
  /*                  CONTROLS — globals vs per-channel                    */
  /* ===================================================================== */
  function setBpm(v) { bpm = clamp(40, 240, Math.round(v)); $('bpm').value = bpm; $('bpmNum').value = bpm; }
  function setKey(v) { keyOffset = clamp(0, 11, v | 0); $('key').value = keyOffset; }
  function setLength(v) {
    steps = clamp(16, 64, v | 0);
    $('length').value = steps;
    currentStep %= steps;
    buildRoll();
    refreshGrid();
  }

  // Panel B sliders write to the CURRENTLY SELECTED channel only, and redraw the wave.
  function onTone(v)  { const s = current(); s.tone = clamp(0, 100, v | 0); $('toneVal').textContent = s.tone + '%'; applySlotFx(s); drawWave(); }
  function onComp(v)  { const s = current(); s.compression = clamp(0, 100, v | 0); $('compVal').textContent = s.compression + '%'; applySlotFx(s); drawWave(); }
  function onPitch(v) { const s = current(); s.pitch = clamp(-12, 12, v | 0); $('pitchVal').textContent = (s.pitch > 0 ? '+' : '') + s.pitch + ' st'; drawWave(); }
  function onVol(v)   { const s = current(); s.volume = clamp(0, 100, v | 0); $('volVal').textContent = s.volume + '%'; applySlotFx(s); drawWave(); }

  /* ----------------------------- Demo seed ----------------------------- */
  function seedDemo() {
    const put = (name, pairs) => {
      const slot = slots.find((s) => s.name === name);
      if (!slot) return;
      const p = patt(slot);
      pairs.forEach(([m, st]) => { const r = midiToRow(m); if (r >= 0 && r < ROWS) p.add(r + '_' + st); });
    };
    put('Kick',   [[60, 0], [60, 4], [60, 8], [60, 12]]);
    put('Snare',  [[60, 4], [60, 12]]);
    put('Hi-Hat', [[60, 0], [60, 2], [60, 4], [60, 6], [60, 8], [60, 10], [60, 12], [60, 14]]);
    put('Bass',   [[48, 0], [48, 3], [51, 6], [55, 8], [48, 11], [58, 14]]);
    put('Pluck',  [[72, 0], [67, 4], [70, 8], [72, 12]]);
    put('Piano',  [[72, 2], [67, 6], [70, 10], [72, 14]]);
    put('Choir',  [[60, 0], [60, 8]]);
  }

  /* ===================================================================== */
  /*                               WIRING                                  */
  /* ===================================================================== */
  function wireEvents() {
    $('bpm').addEventListener('input',    () => setBpm(+$('bpm').value));
    $('bpmNum').addEventListener('input', () => setBpm(+$('bpmNum').value));
    $('key').addEventListener('change',   () => setKey(+$('key').value));
    $('length').addEventListener('change', () => setLength(+$('length').value));

    $('tone').addEventListener('input',   () => onTone(+$('tone').value));
    $('comp').addEventListener('input',   () => onComp(+$('comp').value));
    $('pitch').addEventListener('input',  () => onPitch(+$('pitch').value));
    $('vol').addEventListener('input',    () => onVol(+$('vol').value));

    $('play').addEventListener('click', play);
    $('pause').addEventListener('click', pause);
    $('stop').addEventListener('click', stop);
    $('clear').addEventListener('click', () => {
      const slot = current();
      patt(slot).clear(); refreshGrid(); updateSlotDot(slot);
      toast('Cleared ' + slot.name + ' (' + layers[activeLayer].name + ')');
    });

    $('save').addEventListener('click', saveProject);
    $('export').addEventListener('click', exportWav);

    // Grid: click + drag painting (delegated, survives rebuilds)
    const grid = $('grid');
    grid.addEventListener('mousedown', (e) => {
      const c = e.target.closest('.cell'); if (!c) return;
      e.preventDefault();
      const r = +c.dataset.r, s = +c.dataset.s;
      paintValue = !patt(current()).has(r + '_' + s);
      isPainting = true;
      setCell(r, s, paintValue);
    });
    grid.addEventListener('mouseover', (e) => {
      if (!isPainting) return;
      const c = e.target.closest('.cell'); if (!c) return;
      setCell(+c.dataset.r, +c.dataset.s, paintValue);
    });
    document.addEventListener('mouseup', () => { isPainting = false; });

    // Import + drag & drop
    const drop = $('drop'), file = $('file');
    drop.addEventListener('click', () => file.click());
    file.addEventListener('change', () => { if (file.files[0]) importFile(file.files[0]); file.value = ''; });
    ['dragenter', 'dragover'].forEach((ev) => drop.addEventListener(ev, (e) => { e.preventDefault(); drop.classList.add('drag'); }));
    ['dragleave', 'drop'].forEach((ev) => drop.addEventListener(ev, (e) => { e.preventDefault(); drop.classList.remove('drag'); }));
    drop.addEventListener('drop', (e) => { const f = e.dataTransfer.files[0]; if (f) importFile(f); });
    window.addEventListener('dragover', (e) => e.preventDefault());
    window.addEventListener('drop', (e) => e.preventDefault());

    document.addEventListener('keydown', (e) => {
      if (e.code === 'Space' && !/INPUT|SELECT|TEXTAREA/.test(e.target.tagName)) {
        e.preventDefault();
        isPlaying ? pause() : play();
      }
    });

    wireArranger();
    window.addEventListener('pointerdown', resumeAudio);
    new ResizeObserver(drawWave).observe($('wave'));
  }

  /* ------------------------------- Init -------------------------------- */
  function init() {
    buildKeyOptions();
    buildDefaultSlots();
    layers = [newLayer('Layer 1')];

    setBpm(120); setKey(0); steps = 16; $('length').value = steps;
    if (!loadProject()) seedDemo();

    buildRoll();          // uses (possibly loaded) step count
    buildLayerBar();
    buildSlots();
    selectSlot(selectedId || slots[0].id);
    wireEvents();
    refreshSoundObjectsUI();
    layoutArranger();
    updateArrTransport();
    requestAnimationFrame(frame);
  }

  init();
})();
