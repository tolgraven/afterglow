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
  t.diagnostic(JSON.stringify(result));
});
