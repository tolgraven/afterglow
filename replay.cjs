const assert = require('node:assert/strict');
const {createHash} = require('node:crypto');
const {readFileSync, writeFileSync} = require('node:fs');
const {join} = require('node:path');
const {chromium} = require('playwright-core');

const software = process.argv.includes('--software');
const fixturePath = join(__dirname, 'fixture.json');
const guestPath = join(__dirname, 'audience-compute.js');
const hash = bytes => createHash('sha256').update(bytes).digest('hex');

function fields(message) {
  const [tag, ...entries] = JSON.parse(message);
  assert.equal(tag, '^ ');
  assert.equal(entries.length % 2, 0);
  const values = Object.create(null);
  for (let i = 0; i < entries.length; i += 2) values[entries[i]] = entries[i + 1];
  return values;
}

async function main() {
  const inputs = readFileSync(fixturePath);
  const fixtures = JSON.parse(inputs);
  const executablePath = process.env.CHROMIUM_PATH || (software
    ? '/usr/bin/chromium'
    : '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome');
  const browser = await chromium.launch({
    executablePath,
    headless: true,
    chromiumSandbox: !software,
    args: software
      ? ['--use-angle=swiftshader', '--enable-unsafe-swiftshader']
      : ['--use-angle=metal'],
    timeout: 15000
  });
  try {
    const page = await browser.newPage();
    await page.addScriptTag({path: guestPath});
    const device = await page.evaluate(async () => {
      const canvas = document.createElement('canvas');
      window.gpu = AudienceGPU.start(canvas);
      if (!await gpu.probe()) throw Error('The bundled guest failed its WebGL2 calibration');
      const gl = canvas.getContext('webgl2');
      const info = gl.getExtension('WEBGL_debug_renderer_info');
      return {
        renderer: info ? gl.getParameter(info.UNMASKED_RENDERER_WEBGL) : gl.getParameter(gl.RENDERER),
        webgl: gl.getParameter(gl.VERSION)
      };
    });
    if (software) {
      assert.match(device.renderer, /SwiftShader/i);
    } else {
      assert.match(device.renderer, /Metal/i);
      assert.match(device.renderer, /Apple/i);
      assert.ok(!/SwiftShader|software|llvmpipe/i.test(device.renderer), device.renderer);
    }

    const call = async wire => {
      const {replies, roundTripMs} = await page.evaluate(async input => {
        const start = performance.now();
        const replies = await gpu.compute(input);
        return {replies, roundTripMs: performance.now() - start};
      }, wire);
      return {reply: fields(replies[0]), roundTripMs};
    };

    const cases = [];
    for (const {layers, heads, stride, uniforms, shaderBytes, prepare, run} of fixtures) {
      const programId = fields(prepare)['~:id'];
      assert.ok(programId, 'The prepare packet must have a program ID');
      const prepared = await call(prepare);
      assert.equal(prepared.reply['~:op'], '~:ready', JSON.stringify(prepared));
      const readbacks = [];
      for (const frame of run) {
        const request = fields(frame.wire);
        assert.equal(request['~:id'], programId);
        const completed = await call(frame.wire);
        assert.equal(completed.reply['~:op'], '~:result', JSON.stringify(completed));
        const value = completed.reply['~:values'];
        assert.equal(value.slice(0, 2), '~b');
        const bytes = Buffer.from(value.slice(2), 'base64');
        assert.equal(bytes.length, frame.expected.length * 4);
        let maxError = 0;
        frame.expected.forEach((expected, index) => {
          const actual = bytes.readFloatLE(index * 4);
          const error = Math.abs(actual - expected);
          assert.ok(Number.isFinite(actual) && error <= 1e-5,
            `Layer count ${layers}, component ${index}: ${actual} vs ${expected}`);
          maxError = Math.max(maxError, error);
        });
        readbacks.push({
          jobId: request['~:job'],
          roundTripMs: completed.roundTripMs,
          bytes: bytes.length,
          sha256: hash(bytes),
          maxError
        });
      }
      cases.push({layers, heads, stride, uniforms, shaderBytes, programId,
        prepareRoundTripMs: prepared.roundTripMs, readbacks});
    }

    await page.evaluate(() => gpu.stop());
    const report = {
      device,
      chromium: browser.version(),
      platform: process.platform,
      architecture: process.arch,
      software,
      mergedAfterglow: '1f31801e61951201fc581c7515cecbc63e405ba1',
      reviewedAfterglow: 'a1443334ec7791a8a268012680c12ef12dfad4b7',
      afterglowTree: 'a1ddb449a56551d7db37e1bea2e928a8d53599a6',
      tolglow: 'e4b654a8e16b4327d6bcacb87b0a68ca3366f128',
      fixtureSha256: hash(inputs),
      guestSha256: hash(readFileSync(guestPath)),
      cases
    };
    const output = JSON.stringify(report, null, 2) + '\n';
    writeFileSync(process.env.REPLAY_RESULT || join(__dirname, 'result.json'), output);
    console.log(output);
  } finally {
    await browser.close();
  }
}

main().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
