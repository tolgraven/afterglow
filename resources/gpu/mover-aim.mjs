// A dedicated WebGL2 context solves one calibrated pan/tilt pair per fixture.
function compile(gl, program, type, source) {
  const shader = gl.createShader(type);
  if (!shader) throw new Error('Unable to allocate moving-head shader');
  try {
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(shader));
    gl.attachShader(program, shader);
  } finally {
    gl.deleteShader(shader);
  }
}

function coefficients(spec, low, high) {
  if (Array.isArray(spec)) {
    if (spec.length !== 2 || !spec.every(Number.isFinite) || spec[0] < 0 || spec[0] > 255 || spec[1] === 0)
      throw new RangeError('Invalid center and half-circle calibration');
    return [spec[0] / 255, spec[1] / (180 * 255)];
  }
  if (spec != null) [low, high] = [spec['min-deg'], spec['max-deg']];
  if (!Number.isFinite(low) || !Number.isFinite(high) || low >= high || !Number.isFinite(high - low)) throw new RangeError('Invalid axis limits');
  return [-low / (high - low), 1 / (high - low)];
}

function triple(v) {
  return (Array.isArray(v) || ArrayBuffer.isView(v)) && v.length === 3 && v.every(Number.isFinite);
}

function mountData(fixtures) {
  if (!Array.isArray(fixtures) || !fixtures.length) throw new RangeError('Supply a nonempty fixture list');
  const rig = new Float32Array(fixtures.length * 13);
  fixtures.forEach((f, i) => {
    const position = f.position ?? [0, 0, 0], rotation = f['rotation-deg'] ?? [0, 0, 0];
    if (!triple(position) || !triple(rotation)) throw new RangeError('Invalid fixture position or rotation');
    const angles = Array.from(rotation, deg => -deg * Math.PI / 180);
    rig.set([...position, ...angles.map(Math.cos), ...angles.map(Math.sin),
      ...coefficients(f.calibration?.pan, -180, 180), ...coefficients(f.calibration?.tilt, -90, 90)], i * 13);
  });
  if (!rig.every(Number.isFinite)) throw new RangeError('Mount values must fit float32');
  return rig;
}

async function waitForReadback(gl) {
  const fence = gl.fenceSync(gl.SYNC_GPU_COMMANDS_COMPLETE, 0);
  if (!fence) throw new Error('Unable to fence submitted work');
  gl.flush();
  const deadline = performance.now() + 5000;
  try {
    while (performance.now() < deadline) {
      await new Promise(resolve => setTimeout(resolve, 0));
      const status = gl.clientWaitSync(fence, 0, 0);
      if (status === gl.WAIT_FAILED || gl.isContextLost()) throw new Error('Moving-head readback failed');
      if (status === gl.ALREADY_SIGNALED || status === gl.CONDITION_SATISFIED) return;
    }
    throw new Error('Moving-head readback timed out');
  } finally { gl.deleteSync(fence); }
}

/** The canvas must be dedicated to this solver. History belongs to the publisher. */
export function createMovingHeadSolver(fixtures, vertexSource, canvas = globalThis.OffscreenCanvas ? new OffscreenCanvas(1, 1) : document.createElement('canvas')) {
  const mounts = mountData(fixtures);
  const count = fixtures.length;
  const gl = canvas.getContext('webgl2', { powerPreference: 'high-performance' });
  if (!gl) throw new Error('Moving-head solving requires WebGL2');
  const buffers = [];
  const program = gl.createProgram(), vao = gl.createVertexArray();
  let busy = false, disposed = false;
  const dispose = () => {
    if (disposed) return;
    disposed = true;
    for (const buffer of buffers) gl.deleteBuffer(buffer);
    gl.deleteVertexArray(vao);
    gl.deleteProgram(program);
  };
  function allocate(target, data, usage) {
    const buffer = gl.createBuffer();
    if (!buffer) throw new Error('Unable to allocate moving-head buffer');
    buffers.push(buffer);
    gl.bindBuffer(target, buffer);
    gl.bufferData(target, data, usage);
    return buffer;
  }

  try {
    if (!program || !vao) throw new Error('Unable to allocate moving-head shader program');
    compile(gl, program, gl.VERTEX_SHADER, vertexSource);
    compile(gl, program, gl.FRAGMENT_SHADER, '#version 300 es\nprecision highp float;\nout vec4 color; void main(){color=vec4(0.0);}');
    gl.transformFeedbackVaryings(program, ['axes'], gl.INTERLEAVED_ATTRIBS);
    gl.linkProgram(program);
    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
    gl.useProgram(program);
    gl.bindVertexArray(vao);
    allocate(gl.ARRAY_BUFFER, mounts, gl.STATIC_DRAW);
    for (const [slot, width, offset] of [[1,3,0], [2,3,3], [3,3,6], [4,4,9]]) {
      gl.enableVertexAttribArray(slot);
      gl.vertexAttribPointer(slot, width, gl.FLOAT, false, 52, offset * 4);
    }
    // Per head: three world coordinates, the last accepted pan, and input kind.
    const targets = new Float32Array(count * 5);
    const input = allocate(gl.ARRAY_BUFFER, targets.byteLength, gl.STREAM_DRAW);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 4, gl.FLOAT, false, 20, 0);
    gl.enableVertexAttribArray(5);
    gl.vertexAttribPointer(5, 1, gl.FLOAT, false, 20, 16);
    const output = allocate(gl.TRANSFORM_FEEDBACK_BUFFER, count * 16, gl.STREAM_COPY);
    const staging = allocate(gl.COPY_WRITE_BUFFER, count * 16, gl.STREAM_READ);
    gl.enable(gl.RASTERIZER_DISCARD);
    if (gl.getError() !== gl.NO_ERROR) throw new Error('Unable to configure moving-head buffers');
    const info = gl.getExtension('WEBGL_debug_renderer_info');
    const renderer = gl.getParameter(info ? info.UNMASKED_RENDERER_WEBGL : gl.RENDERER);

    async function solve(inputs, previousAxes) {
      if (disposed || gl.isContextLost()) throw new Error('Moving-head solver is unavailable');
      if (busy) throw new Error('A moving-head frame is already in flight');
      if (inputs?.length !== count || (previousAxes != null && previousAxes.length !== count * 4))
        throw new RangeError('Movement inputs and previous axes must describe this rig in patch order');
      const started = performance.now();
      for (let i = 0; i < count; i++) {
        const prior = previousAxes == null ? -1 : previousAxes[i * 4];
        const input = inputs[i];
        const direction = input?.aim == null && input?.direction != null;
        const coordinates = direction ? input.direction : (input?.aim ?? input);
        if (!triple(coordinates) || (previousAxes != null && !(prior >= 0 && prior <= 1)))
          throw new RangeError('Invalid world target, direction or prior normalized pan');
        const offset = i * 5;
        targets.set(coordinates, offset);
        targets[offset + 3] = prior;
        targets[offset + 4] = direction ? 1 : 0;
      }
      if (!targets.every(Number.isFinite)) throw new RangeError('Targets must fit float32');
      busy = true;
      try {
        gl.bindBuffer(gl.ARRAY_BUFFER, input);
        gl.bufferSubData(gl.ARRAY_BUFFER, 0, targets);
        const uploaded = performance.now();
        gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, output);
        gl.beginTransformFeedback(gl.POINTS);
        gl.drawArrays(gl.POINTS, 0, count);
        gl.endTransformFeedback();
        gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, null);
        gl.bindBuffer(gl.COPY_READ_BUFFER, output);
        gl.bindBuffer(gl.COPY_WRITE_BUFFER, staging);
        gl.copyBufferSubData(gl.COPY_READ_BUFFER, gl.COPY_WRITE_BUFFER, 0, 0, count * 4 * Float32Array.BYTES_PER_ELEMENT);
        const pending = waitForReadback(gl), submitted = performance.now();
        await pending;
        if (disposed) throw new Error('Moving-head solver disposed during frame');
        const ready = performance.now(), axes = new Float32Array(count * 4);
        gl.bindBuffer(gl.COPY_READ_BUFFER, staging);
        gl.getBufferSubData(gl.COPY_READ_BUFFER, 0, axes);
        gl.bindBuffer(gl.COPY_READ_BUFFER, null);
        if (gl.getError() !== gl.NO_ERROR || !axes.every(Number.isFinite))
          throw new Error('Invalid moving-head readback');
        for (let i = 3; i < axes.length; i += 4)
          if (axes[i] !== 1) throw new RangeError('Aim or direction has zero length in fixture coordinates');
        const copied = performance.now();
        return { axes, timing: { uploadMs: uploaded-started, submitMs: submitted-uploaded,
          fenceWaitMs: ready-submitted, readbackMs: copied-ready, totalMs: copied-started } };
      } finally { busy = false; }
    }
    return { solve, dispose, renderer, webgl: gl.getParameter(gl.VERSION) };
  } catch (error) { dispose(); throw error; }
}
