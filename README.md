# BeatFX 🎛️

A native **Web Audio API** Digital Audio Workstation that runs entirely in the browser — no plugins, no audio assets, no build step.

- **Studio** — a 15-instrument step-sequencer / piano-roll with per-channel FX (Tone, Compression, Pitch, Volume), pattern **Layers**, mute, and a live waveform that reacts to your settings. All instruments are synthesized procedurally with the Web Audio API.
- **Create Tab** — a song arranger: "bounce" your beats into **Sound Objects** and drag them onto a multi-row timeline to build full songs, then export to WAV.
- **Pre-Made Songs** (incl. *ICC — Interstellar / Cornfield Chase*) and an in-app **Tutorial**.

## Run locally

It's a static site — any static server works:

```bash
# Python
python -m http.server 8123

# or Node
npx serve -l 8123 .
```

Then open <http://localhost:8123>.

## Deploy to Vercel

There is **no backend** — BeatFX is 100% client-side, so it deploys as a static site.

**Option A — Vercel CLI**
```bash
npm i -g vercel
vercel          # preview deploy
vercel --prod   # production deploy
```

**Option B — Git import**
1. Push this folder to a GitHub/GitLab/Bitbucket repo.
2. In Vercel, **Add New… → Project** and import the repo.
3. Framework Preset: **Other**. Build Command: *(leave empty)*. Output Directory: `.` (root).
4. Deploy.

`vercel.json` is included and sets clean URLs plus sensible security headers. No environment variables are required.

## Files
- `index.html` — markup + Tailwind (via CDN) + styles
- `script.js` — the entire audio engine, sequencer, arranger, tutorial and pre-made songs
- `vercel.json` — static hosting config
