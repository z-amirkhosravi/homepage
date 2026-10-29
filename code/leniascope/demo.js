// Leniascope page: mounts the Leniascope web engine (web-v2.4) and wires the page's controls.
// Behaviour follows the engine's INTEGRATION.md; the engine and palettes are in assets/.
import { createLenia3D, PRESETS } from './assets/leniascope.js?v=2.4.0';
import { colormaps, defaultColormap } from './assets/colormaps.mjs?v=2.4.0';

const canvas = document.querySelector('#lenia');
const stage = document.querySelector('.demo-stage');
const fallback = document.querySelector('.demo-fallback');
const video = fallback.querySelector('video');
const note = document.querySelector('#demo-note');
const play = document.querySelector('#demo-play');
const step = document.querySelector('#demo-step');
const reset = document.querySelector('#demo-reset');
const newSeed = document.querySelector('#demo-new-seed');
const pattern = document.querySelector('#demo-pattern');
const view = document.querySelector('#demo-view');
const colormap = document.querySelector('#demo-colormap');
const recording = document.querySelector('#demo-recording');
const controls = [play, step, reset, newSeed, pattern, view, colormap];

for (const preset of PRESETS) pattern.add(new Option(preset.label, preset.name));
pattern.value = 'random';
for (const name of Object.keys(colormaps)) colormap.add(new Option(name, name));
colormap.value = defaultColormap;

let sim = null;
let inFallback = false;

function showError(message) {
  note.textContent = message;
}

function updatePlay() {
  play.textContent = sim && sim.playing ? 'Pause' : 'Play';
}

// Wraps an asynchronous engine call so a failure shows in the note instead of being lost.
function action(run) {
  return async () => {
    try {
      await run();
    } catch (error) {
      showError(error.message);
    }
    updatePlay();
  };
}

function enableControls() {
  for (const control of controls) control.disabled = false;
  updatePlay();
}

// No WebGPU, or the GPU was lost: show the recording's poster, and play the video only on request.
function showFallback() {
  if (inFallback) return;
  inFallback = true;
  canvas.hidden = true;
  fallback.hidden = false;
  for (const control of controls) control.hidden = true;
  document.querySelector('.demo-controls .gap').hidden = true;
  recording.hidden = false;
  note.textContent = 'The live simulation needs WebGPU, which this browser does not provide. The recording shows a seed developing into tubes.';
}

recording.addEventListener('click', () => {
  if (video.paused) {
    video.play().catch(() => { recording.hidden = true; });
    recording.textContent = 'Pause recording';
  } else {
    video.pause();
    recording.textContent = 'Play recording';
  }
});
video.addEventListener('error', () => { recording.hidden = true; }, true);

// Pause the recording when it is scrolled away or the tab is hidden.
const pauseRecording = () => {
  if (!video.paused) {
    video.pause();
    recording.textContent = 'Play recording';
  }
};
new IntersectionObserver(entries => { if (!entries[0].isIntersecting) pauseRecording(); }).observe(stage);
document.addEventListener('visibilitychange', () => { if (document.hidden) pauseRecording(); });

play.addEventListener('click', () => {
  if (!sim) return;
  if (sim.playing) sim.pause(); else sim.play();
  updatePlay();
});
step.addEventListener('click', action(() => sim.step()));
reset.addEventListener('click', action(() => sim.reset()));
newSeed.addEventListener('click', action(async () => {
  await sim.newSeed();
  pattern.value = 'random';
}));
pattern.addEventListener('change', action(() => sim.setPreset(pattern.value)));
view.addEventListener('change', () => {
  try { sim.setView({mode: view.value}); } catch (error) { showError(error.message); }
});
colormap.addEventListener('change', () => {
  try { sim.setColorRamp(colormaps[colormap.value]); } catch (error) { showError(error.message); }
});

try {
  sim = await createLenia3D(canvas, {
    grid: 'auto',
    preset: 'random',
    colorRamp: colormaps[defaultColormap],
    background: '#13171b',
    wheelZoom: false,
    view: {mode: 'volume', yaw: 0.65, pitch: 0.3, distance: 2.6, autoRotate: 0.08}
  });
  sim.on('ready', enableControls);
  sim.on('unsupported', showFallback);
  sim.on('error', ({message}) => showError(message));
  window.addEventListener('pagehide', () => sim.destroy());
} catch (error) {
  showFallback();
}
