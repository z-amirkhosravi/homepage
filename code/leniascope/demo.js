// Leniascope page: mounts the Leniascope web engine (web-v3.0.1) and wires the page's controls.
// 3D starts on load; 2D is created on first use, in its own canvas, and both handles are kept.
// Behaviour follows the engine's INTEGRATION.md; the engine, gallery and palettes are in assets/.
import { createLenia3D, createLenia2D, PRESETS } from './assets/leniascope.js?v=3.0.1';
import { colormaps, defaultColormap } from './assets/colormaps.mjs?v=3.0.1';

// The site's names for the 2D gallery; the unstable conjoined example is left out of the menu.
const labels2D = {
  'paraptera-gliding': 'Paraptera (glide)',
  'paraptera-jumping': 'Paraptera (jump)',
  'paraptera-walking': 'Paraptera (walk)',
};
const omitted2D = new Set(['conjoined-orbiums']);

const stage = document.querySelector('.demo-stage');
const canvases = {3: document.querySelector('#lenia'), 2: document.querySelector('#lenia-2d')};
const fallback = document.querySelector('.demo-fallback');
const video = fallback.querySelector('video');
const still2D = document.querySelector('#demo-still-2d');
const note = document.querySelector('#demo-note');
const dimension = document.querySelector('#demo-dimension');
const play = document.querySelector('#demo-play');
const step = document.querySelector('#demo-step');
const reset = document.querySelector('#demo-reset');
const newSeed = document.querySelector('#demo-new-seed');
const snapshot = document.querySelector('#demo-snapshot');
const swatch = document.querySelector('#demo-colormap');
const menu = document.querySelector('#demo-colormap-menu');
const pattern = document.querySelector('#demo-pattern');
const view = document.querySelector('#demo-view');
const recording = document.querySelector('#demo-recording');
const simControls = [play, step, reset, newSeed, snapshot, swatch, pattern, view];

const handles = new Map();   // dimension -> engine handle, kept after first use
const intents = new Map();   // dimension -> whether it was playing when the visitor switched away
const failed = new Set();    // dimensions whose simulation is unavailable
let current = 3;
let gallery = null;
let busy = false;
let disposed = false;
let inFallback = false;
let colormap = defaultColormap;

const active = () => handles.get(current);

// The note under the controls holds a suggestion; an error or the fallback message replaces it.
function showError(message) {
  note.textContent = message;
  note.hidden = false;
}

// Shows the current dimension's canvas, or its still when that simulation is unavailable, and
// enables the controls that apply.
function refresh() {
  if (inFallback) return;
  const sim = active();
  const live = !!sim?.available && !failed.has(current);
  canvases[3].hidden = current !== 3;
  canvases[2].hidden = current !== 2 || failed.has(2);
  still2D.hidden = !(current === 2 && failed.has(2));
  if (!still2D.hidden && !still2D.src) still2D.src = still2D.dataset.src;
  fallback.hidden = still2D.hidden;
  dimension.setAttribute('aria-checked', String(current === 3));
  dimension.disabled = busy;
  for (const control of simControls) control.disabled = busy || !live;
  view.hidden = current !== 3;
  const playing = !!sim?.playing && live;
  play.dataset.playing = String(playing);
  play.title = playing ? 'Pause' : 'Play';
  play.setAttribute('aria-label', play.title);
}

function fillPatterns() {
  const list = current === 3 ? PRESETS : gallery.PRESETS_2D.filter(p => !omitted2D.has(p.name));
  pattern.replaceChildren(...list.map(p => new Option(labels2D[p.name] ?? p.label, p.name)));
  pattern.value = active()?.preset ?? (current === 3 ? 'random' : 'orbium');
}

// Runs an engine call, showing a failure in the note. Calls that load a field lock the controls
// until it is ready.
function action(run, lock = false) {
  return async () => {
    if (busy || disposed) return;
    if (lock) {
      busy = true;
      refresh();
    }
    try {
      await run();
    } catch (error) {
      if (!disposed) showError(error.message);
    } finally {
      if (lock) busy = false;
      if (!disposed) refresh();
    }
  };
}

async function create(d) {
  if (d === 2) gallery ??= await import('./assets/gallery2d.js?v=3.0.1');
  if (disposed) return null;
  const options = {colorRamp: colormaps[colormap], background: '#13171b', wheelZoom: false};
  const sim = d === 3
    ? await createLenia3D(canvases[3], {
        ...options,
        grid: 'auto',
        preset: 'random',
        view: {mode: 'volume', yaw: 0.65, pitch: 0.3, distance: 2.6, autoRotate: 0.08},
      })
    : await createLenia2D(canvases[2], {...options, patterns: gallery.PATTERNS_2D, preset: 'orbium'});
  // The page was left while the engine was starting: release this late handle.
  if (disposed) {
    sim.destroy();
    return null;
  }
  handles.set(d, sim);
  sim.on('unsupported', () => fail(d));
  sim.on('error', ({message}) => { if (sim === active()) showError(message); });
  sim.on('ready', () => refresh());
  if (!sim.available) fail(d);
  return sim;
}

function fail(d) {
  failed.add(d);
  if (d === 3) showFallback(); else refresh();
}

// The visitor switches between 3D and 2D. Each keeps its field, camera and play/pause choice;
// the hidden one is paused.
async function switchDimension() {
  const previous = active();
  const next = current === 3 ? 2 : 3;
  if (previous) {
    intents.set(current, previous.playing);
    previous.pause();
  }
  current = next;
  refresh();
  try {
    const sim = handles.get(next) ?? await create(next);
    if (!sim) return;
    if (sim.available) {
      sim.setColorRamp(colormaps[colormap]);
      sim.resize();
      if (intents.has(next)) {
        if (intents.get(next)) sim.play(); else sim.pause();
      }
    }
    fillPatterns();
  } catch (error) {
    current = next === 3 ? 2 : 3;
    if (intents.get(current)) previous?.play();
    previous?.resize();
    throw error;
  }
}

// No WebGPU, or the GPU was lost: show the recording's poster, and play the video only on request.
function showFallback() {
  if (inFallback) return;
  inFallback = true;
  current = 3;
  for (const sim of handles.values()) sim.pause();
  canvases[3].hidden = canvases[2].hidden = true;
  still2D.hidden = true;
  fallback.hidden = false;
  video.hidden = false;
  for (const group of document.querySelectorAll('.demo-controls .ctl-group')) group.hidden = true;
  recording.hidden = false;
  showError('The live simulation needs WebGPU, which this browser does not provide. The recording shows a seed developing into tubes.');
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

// Colormap: a swatch of the current ramp opens a list of ramps.
function gradient(name) {
  const ramp = colormaps[name];
  const count = Math.min(17, ramp.length);
  const stops = typeof ramp[0] === 'string' ? ramp
    : Array.from({length: count}, (_, i) => ramp[Math.round(i * (ramp.length - 1) / (count - 1))])
        .map(c => `rgb(${c.slice(0, 3).map(v => Math.round(v * 255)).join(' ')})`);
  return `linear-gradient(90deg, ${stops.join(', ')})`;
}
const options = Object.keys(colormaps).map((name, i) => {
  const li = document.createElement('li');
  const ramp = document.createElement('span');
  li.id = 'demo-colormap-' + i;
  li.setAttribute('role', 'option');
  li.dataset.name = name;
  ramp.className = 'ramp';
  ramp.style.background = gradient(name);
  li.append(ramp, name);
  return li;
});
menu.append(...options);
let highlighted = 0;

function chooseColormap(name) {
  colormap = name;
  swatch.querySelector('.ramp').style.background = gradient(name);
  swatch.title = 'Colormap: ' + name;
  swatch.setAttribute('aria-label', swatch.title);
  for (const li of options) li.setAttribute('aria-selected', String(li.dataset.name === name));
  try {
    for (const sim of handles.values()) if (sim.available) sim.setColorRamp(colormaps[name]);
  } catch (error) {
    showError(error.message);
  }
}
function highlight(i) {
  highlighted = (i + options.length) % options.length;
  options.forEach((li, j) => li.classList.toggle('active', j === highlighted));
  menu.setAttribute('aria-activedescendant', options[highlighted].id);
  options[highlighted].scrollIntoView({block: 'nearest'});
}
function openMenu() {
  menu.hidden = false;
  swatch.setAttribute('aria-expanded', 'true');
  highlight(options.findIndex(li => li.dataset.name === colormap));
  menu.focus();
}
function closeMenu(returnFocus) {
  if (menu.hidden) return;
  menu.hidden = true;
  swatch.setAttribute('aria-expanded', 'false');
  if (returnFocus) swatch.focus();
}
swatch.addEventListener('click', () => { if (menu.hidden) openMenu(); else closeMenu(true); });
swatch.addEventListener('keydown', e => {
  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
    e.preventDefault();
    openMenu();
  }
});
menu.addEventListener('keydown', e => {
  const moves = {ArrowDown: highlighted + 1, ArrowUp: highlighted - 1, Home: 0, End: options.length - 1};
  if (e.key in moves) {
    e.preventDefault();
    highlight(moves[e.key]);
  } else if (e.key === 'Enter' || e.key === ' ') {
    e.preventDefault();
    chooseColormap(options[highlighted].dataset.name);
    closeMenu(true);
  } else if (e.key === 'Escape') {
    e.preventDefault();
    closeMenu(true);
  } else if (e.key === 'Tab') {
    closeMenu(false);
  }
});
menu.addEventListener('click', e => {
  const li = e.target.closest('li');
  if (!li) return;
  chooseColormap(li.dataset.name);
  closeMenu(true);
});
menu.addEventListener('pointermove', e => {
  const i = options.indexOf(e.target.closest('li'));
  if (i >= 0 && i !== highlighted) highlight(i);
});
document.addEventListener('pointerdown', e => { if (!e.target.closest('.swatch-wrap')) closeMenu(false); });
menu.addEventListener('focusout', e => { if (!menu.contains(e.relatedTarget) && e.relatedTarget !== swatch) closeMenu(false); });
chooseColormap(defaultColormap);

// The other controls act on the visible simulation.
dimension.addEventListener('click', action(switchDimension, true));
play.addEventListener('click', () => {
  const sim = active();
  if (!sim) return;
  if (sim.playing) sim.pause(); else sim.play();
  refresh();
});
step.addEventListener('click', action(() => active().step()));
reset.addEventListener('click', action(() => active().reset(), true));
newSeed.addEventListener('click', action(async () => {
  await active().newSeed();
  pattern.value = 'random';
}, true));
pattern.addEventListener('change', action(() => active().setPreset(pattern.value), true));
view.addEventListener('change', () => {
  try { active().setView({mode: view.value}); } catch (error) { showError(error.message); }
});
snapshot.addEventListener('click', action(async () => {
  const url = URL.createObjectURL(await active().snapshot());
  const link = document.createElement('a');
  link.href = url;
  link.download = `leniascope-${current}d.png`;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}));

window.addEventListener('pagehide', () => {
  disposed = true;
  for (const sim of handles.values()) sim.destroy();
});

try {
  const sim = await create(3);
  if (sim?.available) {
    fillPatterns();
    refresh();
  }
} catch (error) {
  showFallback();
}
