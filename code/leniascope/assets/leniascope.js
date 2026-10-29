// Leniascope Web v2.4.0 — generated from web/src; no runtime dependencies.

// core
// Formula and random stream ported from src/simulation.cpp. No simulation approximations here.
const WEB_VERSION = "2.4.0";
const RULES = Object.freeze({
  classic: 0,
  birthDeath: 1,
  smoothClip: 2,
});
const DEFAULT_RECIPE = Object.freeze({
  patches: 10,
  sizeMin: 0.6,
  sizeMax: 1.2,
  valueMin: 0,
  valueMax: 1,
  layout: "uniform",
  spread: 1.5,
  angle: 0,
  elevation: 0,
});
function finiteNumber(value, name, min, max) {
  if (
    typeof value !== "number" ||
    !Number.isFinite(value) ||
    value < min ||
    value > max
  )
    throw new TypeError(`${name} must be in [${min}, ${max}]`);
  return value;
}
function checkedParams(
  partial,
  n,
  base = {
    radius: Math.round((n * 26) / 128),
    mu: 0.15,
    sigma: 0.017,
    dt: 0.1,
    rule: "classic",
    smoothness: 12,
    stepsPerSecond: 30,
  },
) {
  for (const key of Object.keys(partial))
    if (!(key in base)) throw new TypeError(`Unknown parameter: ${key}`);
  const p = { ...base, ...partial };
  finiteNumber(p.radius, "radius", 1, n / 2);
  if (!Number.isInteger(p.radius))
    throw new TypeError("radius must be an integer");
  finiteNumber(p.mu, "mu", 0, 1);
  finiteNumber(p.sigma, "sigma", 1e-6, 1);
  finiteNumber(p.dt, "dt", 1e-6, 1);
  finiteNumber(p.smoothness, "smoothness", 1, 10000);
  finiteNumber(p.stepsPerSecond, "stepsPerSecond", 0, 240);
  if (!Object.hasOwn(RULES, p.rule)) throw new TypeError("Unknown growth rule");
  return p;
}
function checkedRecipe(partial = {}) {
  for (const key of Object.keys(partial))
    if (!(key in DEFAULT_RECIPE))
      throw new TypeError(`Unknown seed setting: ${key}`);
  const r = { ...DEFAULT_RECIPE, ...partial };
  finiteNumber(r.patches, "patches", 0, 4096);
  if (!Number.isInteger(r.patches))
    throw new TypeError("patches must be an integer");
  finiteNumber(r.sizeMin, "sizeMin", 0.05, 4);
  finiteNumber(r.sizeMax, "sizeMax", r.sizeMin, 4);
  finiteNumber(r.valueMin, "valueMin", 0, 1);
  finiteNumber(r.valueMax, "valueMax", r.valueMin, 1);
  finiteNumber(r.spread, "spread", 0, 16);
  finiteNumber(r.angle, "angle", -180, 180);
  finiteNumber(r.elevation, "elevation", -90, 90);
  if (
    !["uniform", "cluster", "pair"].includes(r.layout) ||
    (r.layout === "pair" && r.patches !== 2)
  )
    throw new TypeError("Invalid seed layout");
  return r;
}
function seedValue(value) {
  if (typeof value === "number" && (!Number.isSafeInteger(value) || value < 0))
    throw new TypeError(
      "seed must be a nonnegative safe integer, bigint, or integer string",
    );
  if (
    !["number", "bigint", "string"].includes(typeof value) ||
    (typeof value === "string" && !/^\d+$/.test(value))
  )
    throw new TypeError("Invalid seed");
  const s = BigInt(value);
  if (s < 0n || s > 0xffffffffffffffffn)
    throw new RangeError("seed must fit unsigned 64 bits");
  return s;
}
function splitmix64(seed) {
  let state = seedValue(seed);
  const mask = 0xffffffffffffffffn;
  return () => {
    state = (state + 0x9e3779b97f4a7c15n) & mask;
    let z = state;
    z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & mask;
    z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & mask;
    return Number((z ^ (z >> 31n)) >> 11n) / 9007199254740992;
  };
}
// Keep explicit seeds reproducible; use browser entropy only when asked for a new one.
function freshSeed(previous) {
  const words = crypto.getRandomValues(new Uint32Array(2));
  let seed = (BigInt(words[0]) << 32n) | BigInt(words[1]);
  if (previous !== undefined && seed === seedValue(previous))
    seed = (seed + 1n) & 0xffffffffffffffffn;
  return seed.toString();
}
const yieldMain = () => new Promise((resolve) => setTimeout(resolve, 0));
const wrapCell = (x, n) => ((x % n) + n) % n;
const cRound = (x) => (x < 0 ? -Math.floor(-x + 0.5) : Math.floor(x + 0.5));
async function randomField(
  n,
  radius,
  seed,
  recipe = DEFAULT_RECIPE,
  yieldWork = true,
) {
  const r = checkedRecipe(recipe),
    random = splitmix64(seed),
    a = new Float32Array(n ** 3);
  const maxSide = Math.max(1, Math.min(n, Math.trunc(radius * r.sizeMax)));
  if (r.patches * maxSide ** 3 > 16 * n ** 3)
    throw new RangeError("Too many overlapping seed writes");
  for (let patch = 0; patch < r.patches; patch++) {
    const ux = random(),
      uy = random(),
      uz = random();
    let bx = Math.trunc(ux * n),
      by = Math.trunc(uy * n),
      bz = Math.trunc(uz * n);
    const side = () =>
      Math.max(
        1,
        Math.min(
          n,
          Math.trunc(radius * (r.sizeMin + (r.sizeMax - r.sizeMin) * random())),
        ),
      );
    const w = side(),
      h = side(),
      d = side();
    if (r.layout !== "uniform") {
      let dx, dy, dz;
      if (r.layout === "pair") {
        const distance = (patch === 0 ? -0.5 : 0.5) * r.spread * radius,
          az = (r.angle * Math.PI) / 180,
          el = (r.elevation * Math.PI) / 180;
        dx = distance * Math.cos(el) * Math.cos(az);
        dy = distance * Math.cos(el) * Math.sin(az);
        dz = distance * Math.sin(el);
      } else {
        const distance = r.spread * radius * Math.cbrt(ux),
          z = 2 * uz - 1,
          horizontal = distance * Math.sqrt(Math.max(0, 1 - z * z));
        dx = horizontal * Math.cos(2 * Math.PI * uy);
        dy = horizontal * Math.sin(2 * Math.PI * uy);
        dz = distance * z;
      }
      bx = wrapCell(cRound((n - w) * 0.5 + dx), n);
      by = wrapCell(cRound((n - h) * 0.5 + dy), n);
      bz = wrapCell(cRound((n - d) * 0.5 + dz), n);
    }
    let lastYield = performance.now();
    for (let z = 0; z < d; z++) {
      for (let y = 0; y < h; y++)
        for (let x = 0; x < w; x++)
          a[(((bz + z) % n) * n + ((by + y) % n)) * n + ((bx + x) % n)] =
            r.valueMin + (r.valueMax - r.valueMin) * random();
      if (yieldWork && performance.now() - lastYield > 8) {
        await yieldMain();
        lastYield = performance.now();
      }
    }
    if (yieldWork) await yieldMain();
  }
  return a;
}
async function kernelField(n, radius, yieldWork = true) {
  const k = new Float64Array(n ** 3);
  let sum = 0;
  for (let z = -radius + 1; z <= radius; z++) {
    for (let y = -radius + 1; y <= radius; y++)
      for (let x = -radius + 1; x <= radius; x++) {
        const rho = Math.sqrt(x * x + y * y + z * z) / radius;
        if (rho >= 1) continue;
        const q = (rho - 0.5) / 0.15,
          v = Math.exp(-0.5 * q * q);
        k[(wrapCell(z, n) * n + wrapCell(y, n)) * n + wrapCell(x, n)] += v;
        sum += v;
      }
    if (yieldWork && (z & 7) === 0) await yieldMain();
  }
  const result = new Float32Array(k.length);
  for (let i = 0; i < k.length; i++) result[i] = k[i] / sum;
  return result;
}
function colorValue(c) {
  if (typeof c === "string") {
    if (!/^#(?:[\da-f]{3}|[\da-f]{4}|[\da-f]{6}|[\da-f]{8})$/i.test(c))
      throw new TypeError("Use hex colors or [r,g,b,a] in [0,1]");
    let h = c.slice(1);
    if (h.length < 5) h = [...h].map((x) => x + x).join("");
    if (h.length === 6) h += "ff";
    c = [0, 2, 4, 6].map((i) => parseInt(h.slice(i, i + 2), 16) / 255);
  }
  if (!Array.isArray(c) || ![3, 4].includes(c.length))
    throw new TypeError("Invalid color");
  return [...c.slice(0, 3), c[3] ?? 1].map((x) =>
    finiteNumber(x, "color channel", 0, 1),
  );
}
function rampTable(colors) {
  if (!Array.isArray(colors) || colors.length < 2 || colors.length > 256)
    throw new TypeError("Supply colorRamp with 2..256 colors");
  const stops = colors.map(colorValue),
    table = new Float32Array(256 * 4);
  for (let i = 0; i < 256; i++) {
    const f = (i / 255) * (stops.length - 1),
      j = Math.min(stops.length - 2, Math.floor(f)),
      t = f - j;
    for (let c = 0; c < 4; c++)
      table[4 * i + c] = stops[j][c] * (1 - t) + stops[j + 1][c] * t;
  }
  return table;
}

// gpu

function fftShader(n) {
  const m = n % 3 === 0 ? n / 3 : n,
    radix = n / m;
  if (m & (m - 1) || ![1, 3].includes(radix) || n > 96)
    throw new RangeError("FFT requires 2^k or 3*2^k, at most 96");
  return `
const N: u32 = ${n}u;
const M: u32 = ${m}u;
const RADIX: u32 = ${radix}u;
override AXIS: u32 = 0u;
override INVERSE: bool = false;
@group(0) @binding(0) var<storage, read> inputData: array<vec2f>;
@group(0) @binding(1) var<storage, read_write> outputData: array<vec2f>;
var<workgroup> lineData: array<vec2f, ${n}>;
fn cmul(a: vec2f, b: vec2f) -> vec2f { return vec2f(a.x*b.x-a.y*b.y, a.x*b.y+a.y*b.x); }
fn address(row: u32, i: u32) -> u32 {
  if (AXIS == 0u) { return row*N+i; }
  if (AXIS == 1u) { return (row/N)*N*N+i*N+row%N; }
  return i*N*N+row;
}
@compute @workgroup_size(64) fn main(@builtin(workgroup_id) group: vec3u, @builtin(local_invocation_index) tid: u32) {
  let row = group.x;
  for (var i = tid; i < N; i += 64u) {
    let residue = i/M;
    let reversed = reverseBits(i%M) >> ${32 - Math.log2(m)}u;
    lineData[i] = inputData[address(row, reversed*RADIX+residue)];
  }
  workgroupBarrier();
  let sign = select(-1.0, 1.0, INVERSE);
  for (var span = 2u; span <= M; span *= 2u) {
    let halfSpan = span/2u;
    for (var j = tid; j < N/2u; j += 64u) {
      let residue = j/(M/2u); let pair = j%(M/2u);
      let k = residue*M+(pair/halfSpan)*span+pair%halfSpan;
      let angle = sign*6.283185307179586*f32(pair%halfSpan)/f32(span);
      let a = lineData[k]; let b = cmul(lineData[k+halfSpan],vec2f(cos(angle),sin(angle)));
      lineData[k] = a+b; lineData[k+halfSpan] = a-b;
    }
    workgroupBarrier();
  }
  for (var k = tid; k < N; k += 64u) {
    var value = lineData[k%M];
    if (RADIX == 3u) {
      for (var r = 1u; r < 3u; r++) {
        let angle = sign*6.283185307179586*f32(r*k)/f32(N);
        value += cmul(lineData[r*M+k%M], vec2f(cos(angle),sin(angle)));
      }
    }
    outputData[address(row,k)] = value * select(1.0,1.0/f32(N),INVERSE);
  }
}`;
}
const packShader = `
@group(0) @binding(0) var<storage,read> field: array<f32>;
@group(0) @binding(1) var<storage,read_write> data: array<vec2f>;
@compute @workgroup_size(128) fn main(@builtin(global_invocation_id) gid: vec3u) {
  if (gid.x < arrayLength(&field)) { data[gid.x] = vec2f(field[gid.x],0); }
}`;
const multiplyShader = `
@group(0) @binding(0) var<storage,read> data: array<vec2f>;
@group(0) @binding(1) var<storage,read> kernel: array<vec2f>;
@group(0) @binding(2) var<storage,read_write> product: array<vec2f>;
@compute @workgroup_size(128) fn main(@builtin(global_invocation_id) gid: vec3u) {
 if (gid.x >= arrayLength(&data)) { return; }
 let a = data[gid.x]; let b = kernel[gid.x];
 product[gid.x] = vec2f(a.x*b.x-a.y*b.y,a.x*b.y+a.y*b.x);
}`;
function updateShader(n) {
  return `
struct Params { mu: f32, sigma: f32, dt: f32, sharp: f32, rule: u32, pad0: u32, pad1: u32, pad2: u32 }
@group(0) @binding(0) var<storage,read> potential: array<vec2f>;
@group(0) @binding(1) var<storage,read_write> field: array<f32>;
@group(0) @binding(2) var display: texture_storage_3d<rgba16float,write>;
@group(0) @binding(3) var<uniform> p: Params;
fn sp(x: f32) -> f32 { return max(x,0)+log(1+exp(-abs(x))); }
@compute @workgroup_size(128) fn main(@builtin(global_invocation_id) gid: vec3u) {
 let i=gid.x; if (i >= arrayLength(&field)) { return; }
 var a=field[i]; let q=(potential[i].x-p.mu)/p.sigma; let g=2*exp(-.5*q*q)-1;
 if (p.rule == 0u) { a=clamp(a+p.dt*g,0,1); }
 else if (p.rule == 2u) {
   let x=a+p.dt*g; let y=min(x,1-x);
   let lower=(sp(p.sharp*y)-sp(p.sharp*(y-1)))/p.sharp;
   a=select(1-lower,lower,x<=.5);
 } else {
   let b=sp(p.sharp*g)/p.sharp; let d=sp(-p.sharp*g)/p.sharp; let rate=b+d; let x=rate*p.dt;
   let decay=select(1-exp(-x),x*(1-.5*x+x*x/6),x<.001);
   a+=(b/rate-a)*decay;
 }
 field[i]=a;
 textureStore(display,vec3u(i%${n}u,(i/${n}u)%${n}u,i/${n * n}u),vec4f(a,0,0,1));
}`;
}
function displayShader(n) {
  return `
@group(0) @binding(0) var<storage,read> field: array<f32>;
@group(0) @binding(1) var display: texture_storage_3d<rgba16float,write>;
@compute @workgroup_size(128) fn main(@builtin(global_invocation_id) gid: vec3u) {
 let i=gid.x; if (i < arrayLength(&field)) { textureStore(display,vec3u(i%${n}u,(i/${n}u)%${n}u,i/${n * n}u),vec4f(field[i],0,0,1)); }
}`;
}
async function computePipeline(device, code, constants = {}) {
  const module = device.createShaderModule({ code });
  const info = await module.getCompilationInfo();
  const errors = info.messages.filter((m) => m.type === "error");
  if (errors.length)
    throw new Error(
      errors.map((m) => `${m.lineNum}:${m.linePos} ${m.message}`).join("\n"),
    );
  return device.createComputePipelineAsync({
    layout: "auto",
    compute: { module, entryPoint: "main", constants },
  });
}
function bufferBinding(buffer) {
  return { buffer };
}
function bindResources(device, pipeline, resources) {
  return device.createBindGroup({
    layout: pipeline.getBindGroupLayout(0),
    entries: resources.map((resource, binding) => ({ binding, resource })),
  });
}
class GpuEngine {
  static async create(device, n, params) {
    const e = new GpuEngine();
    e.device = device;
    e.n = n;
    e.count = n ** 3;
    e.params = params;
    e.resources = [];
    try {
      const buffer = (size, usage) => {
        const b = device.createBuffer({ size, usage });
        e.resources.push(b);
        return b;
      };
      const storage =
        GPUBufferUsage.STORAGE |
        GPUBufferUsage.COPY_DST |
        GPUBufferUsage.COPY_SRC;
      e.state = buffer(e.count * 4, storage);
      e.a = buffer(e.count * 8, storage);
      e.b = buffer(e.count * 8, storage);
      e.kernel = buffer(e.count * 8, storage);
      e.uniform = buffer(32, GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST);
      e.texture = device.createTexture({
        size: [n, n, n],
        dimension: "3d",
        format: "rgba16float",
        usage:
          GPUTextureUsage.STORAGE_BINDING | GPUTextureUsage.TEXTURE_BINDING,
      });
      e.resources.push(e.texture);
      const fftCode = fftShader(n);
      const pipelines = await Promise.all([
        computePipeline(device, packShader),
        computePipeline(device, multiplyShader),
        computePipeline(device, updateShader(n)),
        computePipeline(device, displayShader(n)),
        ...[false, true].flatMap((inverse) =>
          [0, 1, 2].map((axis) =>
            computePipeline(device, fftCode, { AXIS: axis, INVERSE: inverse }),
          ),
        ),
      ]);
      [e.pack, e.multiply, e.update, e.display, ...e.fft] = pipelines;
      e.packBind = bindResources(device, e.pack, [
        bufferBinding(e.state),
        bufferBinding(e.a),
      ]);
      e.fftBinds = e.fft.map((p, i) =>
        bindResources(device, p, [
          bufferBinding(i % 3 === 1 ? e.b : e.a),
          bufferBinding(i % 3 === 1 ? e.a : e.b),
        ]),
      );
      e.multiplyBind = bindResources(device, e.multiply, [
        bufferBinding(e.b),
        bufferBinding(e.kernel),
        bufferBinding(e.a),
      ]);
      e.updateBind = bindResources(device, e.update, [
        bufferBinding(e.b),
        bufferBinding(e.state),
        e.texture.createView(),
        bufferBinding(e.uniform),
      ]);
      e.displayBind = bindResources(device, e.display, [
        bufferBinding(e.state),
        e.texture.createView(),
      ]);
      await e.setParams(params);
      return e;
    } catch (err) {
      e.destroy();
      throw err;
    }
  }
  dispatch(pass, pipeline, bind, count) {
    pass.setPipeline(pipeline);
    pass.setBindGroup(0, bind);
    pass.dispatchWorkgroups(count);
  }
  transform(pass, inverse = false) {
    for (let axis = 0; axis < 3; axis++) {
      const i = (inverse ? 3 : 0) + axis;
      this.dispatch(pass, this.fft[i], this.fftBinds[i], this.n * this.n);
    }
  }
  async setParams(params) {
    const d = this.device,
      old = this.params;
    this.params = params;
    const data = new ArrayBuffer(32);
    new Float32Array(data).set([
      params.mu,
      params.sigma,
      params.dt,
      params.smoothness,
    ]);
    new Uint32Array(data)[4] = RULES[params.rule];
    d.queue.writeBuffer(this.uniform, 0, data);
    if (!this.kernelReady || old.radius !== params.radius) {
      const values = await kernelField(this.n, params.radius);
      const source = d.createBuffer({
        size: values.byteLength,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
      });
      try {
        d.queue.writeBuffer(source, 0, values);
        const encoder = d.createCommandEncoder(),
          pass = encoder.beginComputePass();
        this.dispatch(
          pass,
          this.pack,
          bindResources(d, this.pack, [
            bufferBinding(source),
            bufferBinding(this.a),
          ]),
          Math.ceil(this.count / 128),
        );
        this.transform(pass);
        pass.end();
        encoder.copyBufferToBuffer(this.b, 0, this.kernel, 0, this.count * 8);
        d.queue.submit([encoder.finish()]);
        await d.queue.onSubmittedWorkDone();
        this.kernelReady = true;
      } finally {
        source.destroy();
      }
    }
  }
  load(values) {
    if (
      !(values instanceof Float32Array) ||
      values.length !== this.count ||
      values.some((x) => !Number.isFinite(x) || x < 0 || x > 1)
    )
      throw new TypeError("Invalid initial field");
    this.device.queue.writeBuffer(this.state, 0, values);
    const encoder = this.device.createCommandEncoder(),
      pass = encoder.beginComputePass();
    this.dispatch(
      pass,
      this.display,
      this.displayBind,
      Math.ceil(this.count / 128),
    );
    pass.end();
    this.device.queue.submit([encoder.finish()]);
  }
  encodeStep(encoder) {
    const pass = encoder.beginComputePass(),
      groups = Math.ceil(this.count / 128);
    this.dispatch(pass, this.pack, this.packBind, groups);
    this.transform(pass);
    this.dispatch(pass, this.multiply, this.multiplyBind, groups);
    this.transform(pass, true);
    this.dispatch(pass, this.update, this.updateBind, groups);
    pass.end();
  }
  async readState() {
    const d = this.device,
      b = d.createBuffer({
        size: this.count * 4,
        usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ,
      });
    try {
      const enc = d.createCommandEncoder();
      enc.copyBufferToBuffer(this.state, 0, b, 0, this.count * 4);
      d.queue.submit([enc.finish()]);
      await b.mapAsync(GPUMapMode.READ);
      return new Float32Array(b.getMappedRange().slice(0));
    } finally {
      b.destroy();
    }
  }
  destroy() {
    for (const resource of this.resources ?? []) resource.destroy();
    this.resources = [];
  }
}

// renderer
const VIEW_DEFAULTS = Object.freeze({
  mode: "volume",
  yaw: 0.65,
  pitch: 0.3,
  distance: 2.6,
  fov: 40,
  opacity: 2,
  threshold: 0.02,
  quality: 0.8,
  clip: 1,
  offset: [0, 0, 0],
  autoRotate: 0,
});
function checkedView(partial, base = VIEW_DEFAULTS) {
  for (const key of Object.keys(partial))
    if (!(key in VIEW_DEFAULTS))
      throw new TypeError(`Unknown view setting: ${key}`);
  const v = { ...base, ...partial };
  if (!["volume", "surface"].includes(v.mode))
    throw new TypeError("Invalid view mode");
  for (const [key, min, max] of [
    ["yaw", -1e6, 1e6],
    ["pitch", -1.5, 1.5],
    ["distance", 0.9, 8],
    ["fov", 15, 90],
    ["opacity", 0, 20],
    ["threshold", 0, 0.999],
    ["quality", 0.25, 2],
    ["clip", 0.01, 1],
    ["autoRotate", -2, 2],
  ])
    finiteNumber(v[key], key, min, max);
  if (!Array.isArray(v.offset) || v.offset.length !== 3)
    throw new TypeError("offset must contain x, y, z");
  v.offset = v.offset.map((x) => finiteNumber(x, "offset", -1e6, 1e6));
  return v;
}
const renderShader = `
struct View { eye: vec4f, right: vec4f, up: vec4f, forward: vec4f, background: vec4f, settings: vec4f, offset: vec4f }
@group(0) @binding(0) var<uniform> v: View;
@group(0) @binding(1) var field: texture_3d<f32>;
@group(0) @binding(2) var linearSampler: sampler;
@group(0) @binding(3) var<storage,read> ramp: array<vec4f>;
struct VertexOut { @builtin(position) position: vec4f, @location(0) uv: vec2f }
@vertex fn vertex(@builtin(vertex_index) i: u32) -> VertexOut {
 let points=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));var o:VertexOut;o.position=vec4f(points[i],0,1);o.uv=points[i];return o;
}
fn density(p:vec3f)->f32 { return textureSampleLevel(field,linearSampler,p+vec3f(.5)+v.offset.xyz,0).x; }
fn paint(a:f32)->vec4f {let x=clamp(a,0,1)*255;let i=min(254u,u32(x));return mix(ramp[i],ramp[i+1u],x-f32(i));}
fn background()->vec4f { return vec4f(v.background.rgb*v.background.a,v.background.a); }
fn composite(color:vec4f)->vec4f { return color+(1-color.a)*background(); }
@fragment fn fragment(o:VertexOut)->@location(0) vec4f {
 let ray=normalize(v.forward.xyz+v.right.xyz*o.uv.x*v.eye.w*v.right.w+v.up.xyz*o.uv.y*v.right.w);
 let origin=v.eye.xyz;let mode=u32(v.up.w);let threshold=v.settings.y;
 let safeRay=select(vec3f(1e-6),ray,abs(ray)>vec3f(1e-6));
 let lo=(vec3f(-.5)-origin)/safeRay;let hi=(vec3f(.5,.5,v.settings.w-.5)-origin)/safeRay;
 let near=min(lo,hi);let far=max(lo,hi);let start=max(0,max(near.x,max(near.y,near.z)));let end=min(far.x,min(far.y,far.z));
 if(end<=start){return background();}
 let stepSize=1/(v.forward.w*v.settings.z*1.5);var color=vec4f(0);var previous=start;
 for(var j=0u;j<512u;j++){
  let t=start+(f32(j)+.5)*stepSize;if(t>end || color.a>.995){break;}
  let p=origin+t*ray;let a=density(p);
  if(a>=threshold){
   if(mode==1u){
    var low=previous;var high=t;
    for(var k=0;k<4;k++){let mid=(low+high)*.5;if(density(origin+mid*ray)>=threshold){high=mid;}else{low=mid;}}
    let hit=origin+high*ray;let h=1/v.forward.w;
    let normal=-vec3f(density(hit+vec3f(h,0,0))-density(hit-vec3f(h,0,0)),density(hit+vec3f(0,h,0))-density(hit-vec3f(0,h,0)),density(hit+vec3f(0,0,h))-density(hit-vec3f(0,0,h)));
    let light=.25+.75*abs(dot(normal/max(length(normal),1e-6),normalize(vec3f(.6,.8,1))));let c=paint(threshold);
    return composite(vec4f(c.rgb*light*c.a,c.a));
   }
   let c=paint(a);let alpha=(1-exp(-a*v.settings.x*20*stepSize))*c.a;
   color+=vec4f(c.rgb*alpha,alpha)*(1-color.a);
  }
  previous=t;
 }
 return composite(color);
}`;
class VolumeRenderer {
  static async create(device, canvas, texture, options, n) {
    const r = new VolumeRenderer();
    Object.assign(r, {
      device,
      canvas,
      n,
      resources: [],
      view: checkedView(options.view ?? {}),
      background: colorValue(options.background ?? [0, 0, 0, 0]),
      scale: 1,
    });
    r.maxDPR = finiteNumber(options.maxDPR ?? 2, "maxDPR", 0.25, 4);
    r.maxPixels = finiteNumber(
      options.maxPixels ?? 524288,
      "maxPixels",
      16384,
      4194304,
    );
    try {
      r.context = canvas.getContext("webgpu");
      if (!r.context) throw new Error("Canvas does not support WebGPU");
      r.format = navigator.gpu.getPreferredCanvasFormat();
      r.context.configure({
        device,
        format: r.format,
        alphaMode: "premultiplied",
        usage: GPUTextureUsage.RENDER_ATTACHMENT | GPUTextureUsage.COPY_SRC,
      });
      r.uniform = device.createBuffer({
        size: 112,
        usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
      });
      r.resources.push(r.uniform);
      r.ramp = device.createBuffer({
        size: 4096,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
      });
      r.resources.push(r.ramp);
      r.setColorRamp(options.colorRamp);
      const shader = device.createShaderModule({ code: renderShader });
      const info = await shader.getCompilationInfo();
      const errors = info.messages.filter((x) => x.type === "error");
      if (errors.length)
        throw new Error(errors.map((x) => x.message).join("\n"));
      r.pipeline = await device.createRenderPipelineAsync({
        layout: "auto",
        vertex: { module: shader, entryPoint: "vertex" },
        fragment: {
          module: shader,
          entryPoint: "fragment",
          targets: [{ format: r.format }],
        },
        primitive: { topology: "triangle-list" },
      });
      const sampler = device.createSampler({
        magFilter: "linear",
        minFilter: "linear",
        addressModeU: "repeat",
        addressModeV: "repeat",
        addressModeW: "repeat",
      });
      r.bind = bindResources(device, r.pipeline, [
        bufferBinding(r.uniform),
        texture.createView(),
        sampler,
        bufferBinding(r.ramp),
      ]);
      r.resize();
      return r;
    } catch (error) {
      r.destroy();
      throw error;
    }
  }
  resize() {
    const box = this.canvas.getBoundingClientRect(),
      w = Math.max(1, box.width),
      h = Math.max(1, box.height);
    const dpr =
      Math.min(globalThis.devicePixelRatio || 1, this.maxDPR) * this.scale;
    const factor = Math.min(
      dpr,
      Math.sqrt(this.maxPixels / (w * h)),
      this.device.limits.maxTextureDimension2D / w,
      this.device.limits.maxTextureDimension2D / h,
    );
    const width = Math.max(1, Math.round(w * factor)),
      height = Math.max(1, Math.round(h * factor));
    if (this.canvas.width !== width) this.canvas.width = width;
    if (this.canvas.height !== height) this.canvas.height = height;
    this.aspect = w / h;
    this.dpr = globalThis.devicePixelRatio || 1;
  }
  setView(partial) {
    this.view = checkedView(partial, this.view);
  }
  setColorRamp(colors) {
    this.device.queue.writeBuffer(this.ramp, 0, rampTable(colors));
  }
  encode(encoder, target = null) {
    if (this.dpr !== (globalThis.devicePixelRatio || 1)) this.resize();
    const v = this.view,
      cy = Math.cos(v.yaw),
      sy = Math.sin(v.yaw),
      cp = Math.cos(v.pitch),
      sp = Math.sin(v.pitch);
    const data = new Float32Array([
      sy * cp * v.distance,
      sp * v.distance,
      cy * cp * v.distance,
      this.aspect,
      cy,
      0,
      -sy,
      Math.tan((v.fov * Math.PI) / 360),
      -sy * sp,
      cp,
      -cy * sp,
      { volume: 0, surface: 1 }[v.mode],
      -sy * cp,
      -sp,
      -cy * cp,
      this.n,
      ...this.background,
      v.opacity,
      v.threshold,
      v.quality,
      v.clip,
      ...v.offset,
      0,
    ]);
    this.device.queue.writeBuffer(this.uniform, 0, data);
    const texture = target ?? this.context.getCurrentTexture();
    const pass = encoder.beginRenderPass({
      colorAttachments: [
        {
          view: texture.createView(),
          loadOp: "clear",
          clearValue: { r: 0, g: 0, b: 0, a: 0 },
          storeOp: "store",
        },
      ],
    });
    pass.setPipeline(this.pipeline);
    pass.setBindGroup(0, this.bind);
    pass.draw(3);
    pass.end();
    return texture;
  }
  async snapshot() {
    const width = this.canvas.width,
      height = this.canvas.height,
      stride = Math.ceil((width * 4) / 256) * 256;
    const buffer = this.device.createBuffer({
      size: stride * height,
      usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ,
    });
    try {
      const enc = this.device.createCommandEncoder(),
        texture = this.encode(enc);
      enc.copyTextureToBuffer({ texture }, { buffer, bytesPerRow: stride }, [
        width,
        height,
      ]);
      this.device.queue.submit([enc.finish()]);
      await buffer.mapAsync(GPUMapMode.READ);
      const raw = new Uint8Array(buffer.getMappedRange()),
        rgba = new Uint8ClampedArray(width * height * 4),
        bgra = this.format.startsWith("bgra");
      for (let y = 0; y < height; y++)
        for (let x = 0; x < width; x++) {
          const src = y * stride + 4 * x,
            dst = (y * width + x) * 4,
            alpha = raw[src + 3];
          rgba[dst + 3] = alpha;
          for (let c = 0; c < 3; c++)
            rgba[dst + c] = alpha
              ? Math.min(
                  255,
                  Math.round((raw[src + (bgra ? 2 - c : c)] * 255) / alpha),
                )
              : 0;
        }
      const out =
        typeof OffscreenCanvas === "function"
          ? new OffscreenCanvas(width, height)
          : document.createElement("canvas");
      out.width = width;
      out.height = height;
      out
        .getContext("2d")
        .putImageData(new ImageData(rgba, width, height), 0, 0);
      if (out.convertToBlob) return out.convertToBlob({ type: "image/png" });
      return new Promise((resolve, reject) =>
        out.toBlob(
          (b) => (b ? resolve(b) : reject(new Error("PNG encoding failed"))),
          "image/png",
        ),
      );
    } finally {
      buffer.destroy();
    }
  }
  destroy() {
    for (const r of this.resources ?? []) r.destroy();
    this.resources = [];
    this.context?.unconfigure();
  }
}

// presets

const PRESETS = Object.freeze([
  Object.freeze({ name: "random", label: "Random", rule: "classic" }),
  Object.freeze({
    name: "classic-tubes",
    label: "Tubes",
    rule: "classic",
  }),
  Object.freeze({
    name: "spheres",
    label: "Spheres",
    rule: "classic",
  }),
]);

function checkedRandomRecipe(partial, n) {
  return checkedRecipe({
    patches: n === 64 ? 5 : 4,
    sizeMax: n === 48 ? 1.25 : 1.2,
    ...partial,
  });
}

async function presetField(name, n, seed, recipe, overrides = {}) {
  if (!PRESETS.some((p) => p.name === name))
    throw new TypeError(`Unknown preset: ${name}`);
  const params = checkedParams({ mu: 0.14, ...overrides }, n);
  // Desktop-style uniform boxes, with a lighter count calibrated at each demo
  // resolution (see data/random-calibration.json). Sample once, without filtering
  // or evolving candidates. Explicit recipe fields override these web defaults.
  if (name === "random") recipe = checkedRandomRecipe(recipe, n);
  else {
    seed = 7;
    recipe = checkedRecipe(
      name === "classic-tubes"
        ? {
            patches: 1,
            layout: "cluster",
            spread: 0,
            sizeMin: 1.7,
            sizeMax: 1.7,
          }
        : {
            patches: 2,
            layout: "pair",
            spread: 2.4,
            angle: 45,
            elevation: 20,
            sizeMin: 0.7,
            sizeMax: 0.7,
            valueMin: 0.8,
            valueMax: 1,
          },
    );
  }
  return {
    params,
    field: await randomField(n, params.radius, seed, recipe),
    seed: seedValue(seed).toString(),
    recipe,
  };
}

// interaction
function attachInteraction(canvas, sim, wheelZoom) {
  const points = new Map(),
    listeners = [],
    oldTouch = canvas.style.touchAction;
  canvas.style.touchAction = "none";
  const on = (name, fn, options) => {
    canvas.addEventListener(name, fn, options);
    listeners.push(() => canvas.removeEventListener(name, fn, options));
  };
  const gap = () => {
    const [a, b] = points.values();
    return Math.hypot(a.x - b.x, a.y - b.y);
  };
  on("pointerdown", (e) => {
    if (e.pointerType === "mouse" && e.button !== 0) return;
    points.set(e.pointerId, { x: e.clientX, y: e.clientY });
    canvas.setPointerCapture(e.pointerId);
  });
  on("pointermove", (e) => {
    if (!points.has(e.pointerId)) return;
    const old = points.get(e.pointerId),
      before = points.size === 2 ? gap() : 0;
    points.set(e.pointerId, { x: e.clientX, y: e.clientY });
    const v = sim.view;
    if (points.size === 1)
      sim.setView({
        yaw: v.yaw - (e.clientX - old.x) * 0.008,
        pitch: Math.max(
          -1.5,
          Math.min(1.5, v.pitch + (e.clientY - old.y) * 0.008),
        ),
      });
    else if (points.size === 2 && before > 0)
      sim.setView({
        distance: Math.max(
          0.9,
          Math.min(8, (v.distance * before) / Math.max(1, gap())),
        ),
      });
  });
  const up = (e) => points.delete(e.pointerId);
  for (const name of ["pointerup", "pointercancel", "lostpointercapture"])
    on(name, up);
  if (wheelZoom)
    on(
      "wheel",
      (e) => {
        e.preventDefault();
        const delta =
          e.deltaY *
          (e.deltaMode === 1
            ? 16
            : e.deltaMode === 2
              ? canvas.clientHeight
              : 1);
        sim.setView({
          distance: Math.max(
            0.9,
            Math.min(
              8,
              sim.view.distance *
                Math.exp(Math.max(-1, Math.min(1, delta * 0.001))),
            ),
          ),
        });
      },
      { passive: false },
    );
  return () => {
    for (const id of points.keys())
      if (canvas.hasPointerCapture(id)) canvas.releasePointerCapture(id);
    for (const off of listeners) off();
    canvas.style.touchAction = oldTouch;
  };
}

// index

class LeniaHandle {
  constructor(canvas, options) {
    Object.assign(this, {
      canvas,
      options,
      available: false,
      backend: null,
      grid: null,
      steps: 0,
      time: 0,
      info: { version: WEB_VERSION },
      _events: new Map(),
      _sticky: new Map(),
      _queue: Promise.resolve(),
      _pending: 0,
      _frameTask: Promise.resolve(),
      _cleanups: [],
      _visible: true,
      _destroyed: false,
      _playing: false,
      _dirty: true,
      _raf: 0,
      _last: 0,
      _accum: 0,
      _statsStart: performance.now(),
      _frames: 0,
      _stepCount: 0,
    });
  }
  on(name, fn) {
    if (
      !["ready", "unsupported", "stats", "error"].includes(name) ||
      typeof fn !== "function"
    )
      throw new TypeError("Invalid event listener");
    if (this._destroyed) return () => {};
    if (!this._events.has(name)) this._events.set(name, new Set());
    const listeners = this._events.get(name);
    listeners.add(fn);
    if (this._sticky.has(name)) {
      const payload = this._sticky.get(name);
      queueMicrotask(() => {
        if (
          !this._destroyed &&
          listeners.has(fn) &&
          this._sticky.get(name) === payload
        )
          this._call(fn, payload);
      });
    }
    return () => listeners.delete(fn);
  }
  _call(fn, payload) {
    try {
      fn(payload);
    } catch (e) {
      console.error("Leniascope listener:", e);
    }
  }
  _emit(name, payload, sticky = false) {
    if (sticky) this._sticky.set(name, payload);
    for (const fn of this._events.get(name) ?? []) this._call(fn, payload);
  }
  get params() {
    return { ...this._engine?.params };
  }
  get view() {
    const v = this._renderer?.view;
    return v ? { ...v, offset: [...v.offset] } : {};
  }
  get playing() {
    return this._playing;
  }
  get seed() {
    return this._seed;
  }
  get preset() {
    return this._preset;
  }
  get seedRecipe() {
    return { ...this._recipe };
  }
  _fail(error) {
    if (this._destroyed || this._failed) return;
    this._failed = true;
    this.available = false;
    this.pause();
    this._sticky.delete("ready");
    this._emit("error", { message: error.message ?? String(error) });
    this._emit("unsupported", { reason: error.message ?? String(error) }, true);
  }
  _alive() {
    if (this._destroyed)
      throw new DOMException("Leniascope was destroyed", "AbortError");
    if (!this.available)
      throw new Error(
        this._sticky.get("unsupported")?.reason ?? "Leniascope is unavailable",
      );
  }
  _run(fn) {
    if (this._destroyed)
      return Promise.reject(
        new DOMException("Leniascope was destroyed", "AbortError"),
      );
    this._pending++;
    cancelAnimationFrame(this._raf);
    this._raf = 0;
    const operation = this._queue.then(async () => {
      await this._frameTask;
      this._alive();
      return fn();
    });
    this._queue = operation.catch(() => {});
    return operation.finally(() => {
      this._pending--;
      this._schedule();
    });
  }
  play() {
    if (
      this._playing ||
      this._destroyed ||
      !this.available ||
      this.options.recording
    )
      return;
    this._playing = true;
    this._last = 0;
    this._nextFrameAt = 0;
    this._statsStart = performance.now();
    this._frames = 0;
    this._stepCount = 0;
    this._schedule();
  }
  pause() {
    const wasPlaying = this._playing;
    this._playing = false;
    this._accum = 0;
    this._last = 0;
    cancelAnimationFrame(this._raf);
    this._raf = 0;
    if (wasPlaying)
      this._emit("stats", { stepsPerSecond: 0, framesPerSecond: 0 });
    if (this._dirty) this._schedule();
  }
  async step(count = 1) {
    finiteNumber(count, "step count", 1, 1024);
    if (!Number.isInteger(count))
      throw new TypeError("step count must be an integer");
    this.pause();
    return this._run(async () => {
      for (let done = 0; done < count; ) {
        this._alive();
        const batch = Math.min(4, count - done),
          enc = this._device.createCommandEncoder();
        for (let i = 0; i < batch; i++) this._engine.encodeStep(enc);
        this._device.queue.submit([enc.finish()]);
        await this._device.queue.onSubmittedWorkDone();
        this._alive();
        this.steps += batch;
        this.time += batch * this.params.dt;
        this._stepCount += batch;
        done += batch;
        await yieldMain();
      }
      await this._draw();
    });
  }
  reset(seed) {
    if (seed !== undefined) seedValue(seed);
    return this._run(async () => {
      if (seed !== undefined) {
        if (this._preset !== "random")
          throw new TypeError("A seed is only used by the random preset");
        await this._replaceRandomSeed(seed);
        return;
      }
      this._engine.load(this._initial);
      this.steps = 0;
      this.time = 0;
      this._accum = 0;
      await this._draw();
    });
  }
  async _replaceRandomSeed(seed) {
    const data = await presetField(
      "random",
      this.grid[0],
      seed,
      this.options.seedRecipe,
      this.params,
    );
    this._alive();
    this._initial = data.field;
    this._seed = data.seed;
    this._recipe = data.recipe;
    this._preset = "random";
    this.options.seed = data.seed;
    this._engine.load(data.field);
    this.steps = 0;
    this.time = 0;
    this._accum = 0;
    await this._draw();
    return data.seed;
  }
  newSeed() {
    return this._run(() => this._replaceRandomSeed(freshSeed(this._seed)));
  }
  setPreset(name) {
    if (!PRESETS.some((p) => p.name === name))
      return Promise.reject(new TypeError(`Unknown preset: ${name}`));
    return this._run(async () => {
      const data = await presetField(
        name,
        this.grid[0],
        name === "random" && !this.options.recording
          ? freshSeed(this._seed)
          : this.options.seed,
        this.options.seedRecipe,
      );
      this._alive();
      await this._engine.setParams(data.params);
      this._alive();
      this._initial = data.field;
      this._seed = data.seed;
      this._recipe = data.recipe;
      this._preset = name;
      this._engine.load(data.field);
      this.steps = 0;
      this.time = 0;
      this._accum = 0;
      await this._draw();
    });
  }
  setParams(partial) {
    const copy = { ...partial };
    return this._run(async () => {
      const params = checkedParams(copy, this.grid[0], this.params);
      await this._engine.setParams(params);
      this._alive();
      this._dirty = true;
    });
  }
  setView(partial) {
    if (!this.available || this._destroyed) return;
    this._renderer.setView(partial);
    this._dirty = true;
    this._schedule();
  }
  setColorRamp(colors) {
    if (!this.available || this._destroyed) return;
    this._renderer.setColorRamp(colors);
    this._dirty = true;
    this._schedule();
  }
  resize() {
    if (!this.available || this._destroyed) return;
    this._renderer.resize();
    this._dirty = true;
    this._schedule();
  }
  snapshot() {
    return this._run(() => this._renderer.snapshot());
  }
  _schedule() {
    if (
      this._destroyed ||
      !this.available ||
      this._raf ||
      this._inFrame ||
      this._pending ||
      !this._visible ||
      document.hidden ||
      (!this._dirty && !this._playing)
    )
      return;
    this._raf = requestAnimationFrame((t) => {
      this._raf = 0;
      if (!this._dirty && t < (this._nextFrameAt ?? 0)) {
        this._schedule();
        return;
      }
      const interval = 1000 / (this.options.maxFPS ?? 60);
      this._nextFrameAt =
        Math.max(t - interval, this._nextFrameAt ?? t) + interval;
      this._inFrame = true;
      this._frameTask = this._frame(t)
        .catch((e) => this._fail(e))
        .finally(() => {
          this._inFrame = false;
          this._schedule();
        });
    });
  }
  async _draw() {
    this._alive();
    const enc = this._device.createCommandEncoder();
    this._renderer.encode(enc);
    this._device.queue.submit([enc.finish()]);
    this._dirty = false;
    await this._device.queue.onSubmittedWorkDone();
  }
  async _frame(now) {
    const elapsed = this._last ? Math.min(0.1, (now - this._last) / 1000) : 0;
    this._last = now;
    const enc = this._device.createCommandEncoder();
    let didStep = false;
    if (this._playing) {
      this._accum = Math.min(
        2,
        this._accum + elapsed * this.params.stepsPerSecond,
      );
      if (this._accum >= 1) {
        this._engine.encodeStep(enc);
        this._accum -= 1;
        didStep = true;
      }
      if (this.view.autoRotate && !this.options.recording)
        this._renderer.setView({
          yaw: this.view.yaw + elapsed * this.view.autoRotate,
        });
    }
    this._renderer.encode(enc);
    this._dirty = false;
    const start = performance.now();
    this._device.queue.submit([enc.finish()]);
    await this._device.queue.onSubmittedWorkDone();
    if (this._destroyed || !this.available) return;
    if (didStep) {
      this.steps++;
      this.time += this.params.dt;
      this._stepCount++;
    }
    this._frames++;
    // Only drawing resolution adapts after initialization; the state grid never changes silently.
    const ms = performance.now() - start;
    this._gpuEMA = (this._gpuEMA ?? ms) * 0.9 + ms * 0.1;
    if (
      !this.options.recording &&
      this._frames % 30 === 0 &&
      this._gpuEMA > 24 &&
      this._renderer.scale > 0.4
    ) {
      this._renderer.scale = Math.max(0.4, this._renderer.scale * 0.85);
      this._renderer.resize();
    }
    if (now - this._statsStart >= 1000) {
      const seconds = (now - this._statsStart) / 1000;
      this._emit("stats", {
        stepsPerSecond: this._stepCount / seconds,
        framesPerSecond: this._frames / seconds,
      });
      this._stepCount = 0;
      this._frames = 0;
      this._statsStart = now;
    }
  }
  _watch() {
    const changed = () => {
      this._last = 0;
      this._accum = 0;
      this._statsStart = performance.now();
      this._frames = 0;
      this._stepCount = 0;
      cancelAnimationFrame(this._raf);
      this._raf = 0;
      if (document.hidden || !this._visible)
        this._emit("stats", { stepsPerSecond: 0, framesPerSecond: 0 });
      this._schedule();
    };
    document.addEventListener("visibilitychange", changed);
    this._cleanups.push(() =>
      document.removeEventListener("visibilitychange", changed),
    );
    if (globalThis.IntersectionObserver) {
      const o = new IntersectionObserver((entries) => {
        this._visible = entries[0].isIntersecting;
        changed();
      });
      o.observe(this.canvas);
      this._cleanups.push(() => o.disconnect());
    }
    if (globalThis.ResizeObserver) {
      const o = new ResizeObserver(() => this.resize());
      o.observe(this.canvas);
      this._cleanups.push(() => o.disconnect());
    }
    const resized = () => this.resize();
    window.addEventListener("resize", resized);
    this._cleanups.push(() => window.removeEventListener("resize", resized));
    const reduced = matchMedia("(prefers-reduced-motion: reduce)"),
      motion = () => {
        if (reduced.matches) this.pause();
      };
    reduced.addEventListener("change", motion);
    this._cleanups.push(() => reduced.removeEventListener("change", motion));
    if (this.options.interactive !== false)
      this._cleanups.push(
        attachInteraction(this.canvas, this, this.options.wheelZoom === true),
      );
    if (
      this.options.autoplay !== false &&
      !this.options.recording &&
      !reduced.matches
    )
      this.play();
    else this.pause();
  }
  destroy() {
    if (this._destroyed) return;
    this._destroyed = true;
    this._playing = false;
    this.available = false;
    cancelAnimationFrame(this._raf);
    for (const cleanup of this._cleanups) cleanup();
    this._cleanups = [];
    this._renderer?.destroy();
    this._engine?.destroy();
    this._device?.destroy();
    this._initial = null;
    this._events.clear();
    this._sticky.clear();
  }
}

async function createLenia3D(canvas, options = {}) {
  if (
    !canvas ||
    typeof canvas.getContext !== "function" ||
    typeof canvas.getBoundingClientRect !== "function"
  )
    throw new TypeError("Pass an HTML canvas");
  const opts = { grid: "auto", preset: "random", ...options };
  opts.seed ??= opts.recording ? 1 : freshSeed();
  if (!["auto", 48, 64, 96].includes(opts.grid))
    throw new TypeError("grid must be auto, 48, 64, or 96");
  if (opts.recording && opts.grid === "auto")
    throw new TypeError("Recording requires an explicit grid");
  if (!PRESETS.some((p) => p.name === opts.preset))
    throw new TypeError("Unknown preset");
  seedValue(opts.seed);
  if (opts.seedRecipe !== undefined) {
    checkedRandomRecipe(opts.seedRecipe, opts.grid === "auto" ? 48 : opts.grid);
    // Preserve partial overrides: the default patch count depends on the grid
    // selected below, including when the timing probe changes that grid.
    opts.seedRecipe = { ...opts.seedRecipe };
  }
  checkedParams(opts.params ?? {}, opts.grid === "auto" ? 48 : opts.grid);
  checkedView(opts.view ?? {});
  rampTable(opts.colorRamp);
  colorValue(opts.background ?? [0, 0, 0, 0]);
  finiteNumber(opts.maxDPR ?? 2, "maxDPR", 0.25, 4);
  finiteNumber(opts.maxFPS ?? 60, "maxFPS", 15, 240);
  finiteNumber(opts.maxPixels ?? 524288, "maxPixels", 16384, 4194304);
  const sim = new LeniaHandle(canvas, opts);
  try {
    if (!navigator.gpu)
      throw new Error(
        "WebGPU requires a supported browser and HTTPS (or localhost).",
      );
    const adapter = await navigator.gpu.requestAdapter({
      powerPreference: opts.powerPreference ?? "low-power",
    });
    if (!adapter) throw new Error("No WebGPU adapter is available.");
    const device = await adapter.requestDevice();
    sim._device = device;
    device.addEventListener("uncapturederror", (e) => {
      e.preventDefault();
      sim._fail(e.error);
    });
    device.lost.then((info) => {
      if (!sim._destroyed && !sim._deviceEnded)
        sim._fail(
          new Error(`WebGPU device lost: ${info.message || info.reason}`),
        );
    });
    const supports = (n) =>
      device.limits.maxTextureDimension3D >= n &&
      device.limits.maxStorageBufferBindingSize >= n ** 3 * 8 &&
      device.limits.maxBufferSize >= n ** 3 * 8 &&
      device.limits.maxComputeWorkgroupsPerDimension >= n * n &&
      device.limits.maxComputeInvocationsPerWorkgroup >= 128;
    const initialize = async (n) => {
      if (!supports(n))
        throw new Error(`GPU limits cannot support a ${n}³ field.`);
      sim._renderer?.destroy();
      sim._engine?.destroy();
      sim._renderer = null;
      sim._engine = null;
      const data = await presetField(
        opts.preset,
        n,
        opts.seed,
        opts.seedRecipe,
        opts.params,
      );
      sim._engine = await GpuEngine.create(device, n, data.params);
      sim._engine.load(data.field);
      sim._initial = data.field;
      sim._seed = data.seed;
      sim._recipe = data.recipe;
      sim.grid = Object.freeze([n, n, n]);
      sim._renderer = await VolumeRenderer.create(
        device,
        canvas,
        sim._engine.texture,
        opts,
        n,
      );
    };
    await initialize(
      opts.grid === "auto" ? (supports(64) ? 64 : 48) : opts.grid,
    );
    const probe = async () => {
      const timings = [];
      // Probe offscreen so reduced-motion visitors never see warm-up evolution.
      const target = device.createTexture({
        size: [canvas.width, canvas.height],
        format: sim._renderer.format,
        usage: GPUTextureUsage.RENDER_ATTACHMENT,
      });
      try {
        for (let i = 0; i < 4; i++) {
          const enc = device.createCommandEncoder();
          sim._engine.encodeStep(enc);
          sim._renderer.encode(enc, target);
          const start = performance.now();
          device.queue.submit([enc.finish()]);
          await device.queue.onSubmittedWorkDone();
          if (i) timings.push(performance.now() - start);
          await yieldMain();
        }
      } finally {
        target.destroy();
      }
      return timings.reduce((a, b) => a + b) / timings.length;
    };
    let probeMs = await probe();
    const probes = [{ grid: sim.grid[0], milliseconds: probeMs }];
    if (opts.grid === "auto") {
      if (probeMs > 20 && sim.grid[0] > 48) {
        await initialize(48);
        probeMs = await probe();
        probes.push({ grid: 48, milliseconds: probeMs });
      } else if (probeMs < 8 && supports(96)) {
        await initialize(96);
        probeMs = await probe();
        probes.push({ grid: 96, milliseconds: probeMs });
        if (probeMs > 20) {
          await initialize(64);
        }
      }
    }
    sim._engine.load(sim._initial);
    await device.queue.onSubmittedWorkDone();
    if (sim._failed) throw new Error(sim._sticky.get("unsupported").reason);
    sim._preset = opts.preset;
    sim.backend = "webgpu";
    sim.available = true;
    sim.info = Object.freeze({
      version: WEB_VERSION,
      adapter: adapter.info?.description || adapter.info?.vendor || "WebGPU",
      probes: Object.freeze(probes),
    });
    await sim._draw();
    sim._emit("ready", { backend: "webgpu", grid: sim.grid }, true);
    sim._watch();
    return sim;
  } catch (error) {
    sim._renderer?.destroy();
    sim._engine?.destroy();
    sim._deviceEnded = true;
    sim._device?.destroy();
    sim.available = false;
    sim.backend = null;
    sim._sticky.delete("ready");
    sim._emit("unsupported", { reason: error.message ?? String(error) }, true);
    return sim;
  }
}

export {createLenia3D, PRESETS, WEB_VERSION};
