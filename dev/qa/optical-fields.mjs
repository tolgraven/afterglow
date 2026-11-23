// WebGL2 fixtures for the data emitted by afterglow.qa.effect-blocks.
// The vertex stage supplies either metre coordinates or the surface's own UVs.
const sampleVertex = `#version 300 es
layout(location=0) in vec3 position;
uniform float count;
out vec3 v_position;
out vec2 v_uv;
void main() {
  v_position=position;
  v_uv=position.xy;
  gl_Position=vec4((float(gl_VertexID)+0.5)*2.0/count-1.0,0.0,0.0,1.0);
  gl_PointSize=1.0;
}`;
const discardFragment = '#version 300 es\nprecision highp float;out vec4 c;void main(){c=vec4(0.0);}';

function link(gl, vertex, fragment, varyings = []) {
  const program = gl.createProgram();
  for (const [type, source] of [[gl.VERTEX_SHADER, vertex], [gl.FRAGMENT_SHADER, fragment]]) {
    const shader = gl.createShader(type);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw Error(gl.getShaderInfoLog(shader));
    gl.attachShader(program, shader);
    gl.deleteShader(shader);
  }
  if (varyings.length) gl.transformFeedbackVaryings(program, varyings, gl.INTERLEAVED_ATTRIBS);
  gl.linkProgram(program);
  if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw Error(gl.getProgramInfoLog(program));
  return program;
}

function vertices(gl, positions) {
  const buffer = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
  gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(positions.flat()), gl.STATIC_DRAW);
  gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
  gl.enableVertexAttribArray(0);
  return buffer;
}

function bind(gl, program, shader, {beat, density}) {
  gl.useProgram(program);
  if (shader.inputs['elapsed-beats']) gl.uniform1f(gl.getUniformLocation(program, shader.inputs['elapsed-beats']), beat);
  if (shader.uniforms.density) gl.uniform1f(gl.getUniformLocation(program, shader.uniforms.density.name), density);
}

function checked(gl, stage = 'readback') {
  const error = gl.getError();
  if (error !== gl.NO_ERROR) throw Error(stage + ' WebGL error ' + error);
}

function readFragments(gl, fixture, count) {
  if (!gl.getExtension('EXT_color_buffer_float')) throw Error('Float color attachments unavailable');
  const texture = gl.createTexture(), target = gl.createFramebuffer();
  gl.bindTexture(gl.TEXTURE_2D, texture);
  gl.texStorage2D(gl.TEXTURE_2D, 1, gl.RGBA32F, count, 1);
  gl.bindFramebuffer(gl.FRAMEBUFFER, target);
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, texture, 0);
  if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) throw Error('Incomplete float target');
  gl.viewport(0, 0, count, 1);
  let maxError = 0;
  for (const [field, shader] of Object.entries(fixture.fragments)) {
    const program = link(gl, sampleVertex, shader.source);
    for (const sample of fixture.samples) {
      bind(gl, program, shader, sample);
      gl.uniform1f(gl.getUniformLocation(program, 'count'), count);
      gl.drawArrays(gl.POINTS, 0, count);
      const values = new Float32Array(4 * count);
      gl.readPixels(0, 0, count, 1, gl.RGBA, gl.FLOAT, values);
      sample.values.forEach((row, i) => {
        const expected = [row[field]].flat();
        expected.forEach((value, component) => {
          maxError = Math.max(maxError, Math.abs(values[4 * i + component] - value));
        });
      });
    }
    gl.deleteProgram(program);
  }
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  gl.deleteFramebuffer(target);
  gl.deleteTexture(texture);
  checked(gl);
  return maxError;
}

function fieldProgram(gl, shader) {
  return link(gl, shader.source, discardFragment, shader.outputs.map(field => field.varying));
}

function evaluateField(gl, program, shader, sample, count, output) {
  bind(gl, program, shader, sample);
  gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, output);
  gl.enable(gl.RASTERIZER_DISCARD);
  gl.beginTransformFeedback(gl.POINTS);
  gl.drawArrays(gl.POINTS, 0, count);
  gl.endTransformFeedback();
  gl.disable(gl.RASTERIZER_DISCARD);
  gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, null);
}

function fieldBuffer(gl, count, stride) {
  const output = gl.createBuffer();
  gl.bindBuffer(gl.TRANSFORM_FEEDBACK_BUFFER, output);
  gl.bufferData(gl.TRANSFORM_FEEDBACK_BUFFER, count * stride * 4, gl.DYNAMIC_COPY);
  gl.bindBuffer(gl.TRANSFORM_FEEDBACK_BUFFER, null);
  return output;
}

function readFields(gl, fixture, count) {
  const shader = fixture.batch, program = fieldProgram(gl, shader);
  const output = fieldBuffer(gl, count, shader.stride);
  let maxError = 0;
  for (const sample of fixture.samples) {
    evaluateField(gl, program, shader, sample, count, output);
    const gpu = new Float32Array(shader.stride * count);
    gl.bindBuffer(gl.TRANSFORM_FEEDBACK_BUFFER, output);
    gl.getBufferSubData(gl.TRANSFORM_FEEDBACK_BUFFER, 0, gpu);
    for (const [i, row] of sample.values.entries()) {
      for (const field of shader.outputs) {
        [row[field.attribute]].flat().forEach((value, channel) => {
          maxError = Math.max(maxError, Math.abs(value - gpu[i * shader.stride + field.offset + channel]));
        });
      }
    }
  }
  gl.deleteBuffer(output);
  gl.deleteProgram(program);
  checked(gl);
  return maxError;
}

export function verify(canvas, proof) {
  const gl = canvas.getContext('webgl2');
  if (!gl) throw Error('WebGL2 unavailable');
  const count = proof.positions.length;
  const input = vertices(gl, proof.positions);
  const results = {};
  for (const name of ['uv', 'world']) {
    results[name] = {fragments: readFragments(gl, proof[name], count), batch: readFields(gl, proof[name], count)};
  }
  const debug = gl.getExtension('WEBGL_debug_renderer_info');
  results.renderer = gl.getParameter(debug ? debug.UNMASKED_RENDERER_WEBGL : gl.RENDERER);
  gl.deleteBuffer(input);
  return results;
}

// The film harness consumes the emitted transform-feedback buffer directly as
// vertex attributes for a curved LED surface. Only the camera and diodes below
// are visualization code. Color, dimmer and focus all come from the authored IR.
const diodeVertex = `#version 300 es
precision highp float;
layout(location=0) in vec3 position;
layout(location=1) in vec3 color;
layout(location=2) in float dimmer;
layout(location=3) in float focus;
uniform vec2 viewport;
uniform float orbit;
out vec3 emitted;
out float spot;
void main() {
  float c=cos(orbit),s=sin(orbit);
  vec3 p=vec3(c*position.x+s*position.z,position.y,-s*position.x+c*position.z);
  float depth=5.35-p.z*0.75;
  gl_Position=vec4(p.x*2.7*viewport.y/viewport.x,2.75*(p.y+0.13*p.z),depth-0.7,depth);
  gl_PointSize=clamp(viewport.y*(0.094-0.029*focus)/depth,2.0,28.0);
  emitted=color*dimmer; spot=focus;
}`;
const diodeFragment = `#version 300 es
precision highp float;
in vec3 emitted;
in float spot;
out vec4 pixel;
void main() {
  vec2 p=gl_PointCoord*2.0-1.0;
  float radius=length(p);
  if(radius>1.0) discard;
  float core=exp(-radius*radius*mix(3.1,8.0,spot));
  float halo=(1.0-smoothstep(0.16,1.0,radius))*0.40;
  vec3 linear=emitted*(core*7.3+halo);
  pixel=vec4(pow(1.0-exp(-linear),vec3(1.0/2.2)),1.0);
}`;

function curtain(columns, rows) {
  const world = [], uv = [];
  for (let row = 0; row < rows; row++) {
    for (let column = 0; column < columns; column++) {
      const u = column / (columns - 1), v = row / (rows - 1);
      const z = 0.73 * Math.sin(u * 5.8 + v * 2.1) + 0.23 * Math.cos(v * 4.6 - u * 4);
      world.push([(u - 0.5) * 3.7, (v - 0.5) * 2.35 + 0.26 * Math.sin(6 * u), z]);
      uv.push([u, v, 0]);
    }
  }
  return {world, uv};
}

export function demonstrate(canvas, proof) {
  const gl = canvas.getContext('webgl2', {alpha: false, antialias: true, preserveDrawingBuffer: true});
  const shape = curtain(84, 48), count = shape.world.length;
  const display = link(gl, diodeVertex, diodeFragment);
  const geometry = vertices(gl, shape.world), texcoords = vertices(gl, shape.uv);
  const displays = ['world', 'uv'].map((mode, panel) => {
    const shader = proof[mode].batch;
    const compute = fieldProgram(gl, shader);
    const data = fieldBuffer(gl, count, shader.stride);
    const read = gl.createVertexArray(), draw = gl.createVertexArray();
    gl.bindVertexArray(read);
    gl.bindBuffer(gl.ARRAY_BUFFER, mode === 'world' ? geometry : texcoords);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
    gl.enableVertexAttribArray(0);
    gl.bindVertexArray(draw);
    gl.bindBuffer(gl.ARRAY_BUFFER, geometry);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
    gl.enableVertexAttribArray(0);
    gl.bindBuffer(gl.ARRAY_BUFFER, data);
    const slot = {color: 1, dimmer: 2, focus: 3};
    for (const field of shader.outputs) {
      gl.vertexAttribPointer(slot[field.attribute], field.components, gl.FLOAT, false, 4 * shader.stride, 4 * field.offset);
      gl.enableVertexAttribArray(slot[field.attribute]);
    }
    gl.bindVertexArray(null);
    gl.bindBuffer(gl.ARRAY_BUFFER, null);
    return {shader, compute, data, read, draw, panel};
  });
  function render(beat) {
    gl.clearColor(0.023, 0.035, 0.045, 1);
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.enable(gl.DEPTH_TEST);
    const w = canvas.width / 2, h = canvas.height;
    for (const {shader, compute, data, read, draw, panel} of displays) {
      gl.bindVertexArray(read);
      evaluateField(gl, compute, shader, {beat, density: 0.32}, count, data);
      checked(gl, 'field computation');
      gl.bindVertexArray(draw);
      gl.viewport(w * panel, 0, w, h);
      gl.useProgram(display);
      gl.uniform2f(gl.getUniformLocation(display, 'viewport'), w, h);
      gl.uniform1f(gl.getUniformLocation(display, 'orbit'), -0.21 + 0.13 * Math.sin(beat * 0.18));
      gl.drawArrays(gl.POINTS, 0, count);
      checked(gl, 'LED surface');
    }
    gl.bindVertexArray(null);
    checked(gl);
  }
  function dispose() {
    for (const {compute, data, read, draw} of displays) {
      gl.deleteVertexArray(read); gl.deleteVertexArray(draw);
      gl.deleteBuffer(data); gl.deleteProgram(compute);
    }
    gl.deleteBuffer(geometry); gl.deleteBuffer(texcoords); gl.deleteProgram(display);
  }
  return {render, dispose};
}
