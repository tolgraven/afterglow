const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const {promisify} = require('node:util');
const {execFile} = require('node:child_process');
const {launch} = require('../../dev/qa/browser.cjs');

const root = path.resolve(__dirname, '../..');
const run = promisify(execFile);

test('generated water, gel and fog agree on surface fragments, fixture batches and the CPU', async t => {
  const tmp = await fs.mkdtemp(path.join(os.tmpdir(), 'afterglow-optical-'));
  t.after(() => fs.rm(tmp, {recursive: true, force: true}));
  const emitted = process.env.AFTERGLOW_SHADER_FIXTURE || path.join(tmp, 'shaders.json');
  if (!process.env.AFTERGLOW_SHADER_FIXTURE) {
    await run('lein', ['run', '-m', 'afterglow.qa.effect-blocks', emitted], {cwd: root});
  }
  const proof = JSON.parse(await fs.readFile(emitted, 'utf8'));
  const source = await fs.readFile(path.join(root, 'dev/qa/optical-fields.mjs'), 'utf8');
  const browser = await launch();
  t.after(() => browser.close());
  const page = await browser.newPage();
  const result = await page.evaluate(async ({source, proof}) => {
    const url = URL.createObjectURL(new Blob([source], {type:'text/javascript'}));
    try {
      const {verify} = await import(url);
      return verify(document.createElement('canvas'), proof);
    } finally { URL.revokeObjectURL(url); }
  }, {source, proof});
  // highp sin/exp may use different approximations than JVM float64.
  // This normalized-light tolerance is smaller than 1/32 of one 8-bit DMX step.
  const tolerance = 1 / 8192;
  for (const mapping of ['uv', 'world']) {
    assert.ok(result[mapping].fragments <= tolerance, JSON.stringify(result));
    assert.ok(result[mapping].batch <= tolerance, JSON.stringify(result));
  }
  // The first two fixtures share XY and have different depths.
  assert.deepEqual(proof.uv.samples[0].values[0], proof.uv.samples[0].values[1]);
  assert.notEqual(proof.world.samples[0].values[0].dimmer, proof.world.samples[0].values[1].dimmer);
  // A second pair occupies the same XYZ with two deliberately different UVs.
  assert.deepEqual(proof.world.samples[0].values[0], proof.world.samples[0].values[4]);
  assert.notEqual(proof.uv.samples[0].values[0].dimmer, proof.uv.samples[0].values[4].dimmer);
  const runnerSource = await fs.readFile(path.join(root, 'resources/gpu/compute.js'), 'utf8');
  const values = await page.evaluate(async ({runnerSource, proof}) => {
    const url = URL.createObjectURL(new Blob([runnerSource], {type: 'text/javascript'}));
    const {createComputeRunner} = await import(url);
    URL.revokeObjectURL(url);
    const runner = createComputeRunner(document.createElement('canvas'));
    const positions = new Float32Array(proof.positions.flat());
    const sample = proof.uv.samples[1];
    const input = {positions, elapsedBeats: sample.beat, params: {density: sample.density}};
    try {
      runner.compile(proof.uv.fragments.color);
      const mixed = await runner.run({...input, surfaceUVs: proof['surface-uvs']});
      const fallback = await runner.run(input);
      const uncharted = await runner.run({...input, surfaceUVs: proof.positions.map(() => null)});
      runner.compile(proof.world.fragments.color);
      const ordinary = await runner.run(input);
      return [mixed, fallback, ordinary, uncharted].map(frame => Array.from(frame.values));
    } finally { runner.dispose(); }
  }, {runnerSource, proof});
  for (let i = 0; i < proof.positions.length; i++) {
    for (let c = 0; c < 3; c++) {
      assert.ok(Math.abs(values[0][4*i+c] - proof.uv.samples[1].values[i].color[c]) <= tolerance);
      assert.ok(Math.abs(values[2][4*i+c] - proof.world.samples[1].values[i].color[c]) <= tolerance);
    }
  }
  assert.deepEqual(values[1], values[3]);
  assert.deepEqual(values[1].slice(0, 3), values[1].slice(16, 19));
  t.diagnostic(JSON.stringify(result));
});
