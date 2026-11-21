const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const { chromium } = require('playwright-core');

test('calibrated GPU solver owns its buffers and obeys accepted pan history', async () => {
  const root = path.resolve(__dirname, '../../resources/gpu');
  const [source, shader] = await Promise.all(['mover-aim.mjs','mover-aim.vert'].map(name => fs.readFile(path.join(root, name), 'utf8')));
  const browser = await chromium.launch({ executablePath: process.env.CHROMIUM_PATH || chromium.executablePath(),
    args: ['--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader'] });
  try {
    const page = await browser.newPage();
    const result = await page.evaluate(async ({ source, shader }) => {
      const url = URL.createObjectURL(new Blob([source], { type: 'text/javascript' }));
      const { createMovingHeadSolver } = await import(url);
      URL.revokeObjectURL(url);
      const fixtures = [{}, { position: [3, 1, 0], 'rotation-deg': [0, 90, 0],
        calibration: { pan: { 'min-deg': -270, 'max-deg': 270 } } }];
      const solver = createMovingHeadSolver(fixtures, shader, document.createElement('canvas'));
      const aims = [[1, 0, 0], [3, 1, -1]];
      try {
        const first = await solver.solve(aims);
        const prior = first.axes.slice();
        prior[4] = 0;
        const second = await solver.solve(aims, prior);
        const rejects = async fn => { try { await fn(); return false; } catch { return true; } };
        const zero = await rejects(() => solver.solve([[0,0,0], aims[1]]));
        solver.dispose();
        return { first: [...first.axes], second: [...second.axes], zero, disposed: await rejects(() => solver.solve(aims)) };
      } finally { solver.dispose(); }
    }, { source, shader });
    assert.equal(result.zero, true);
    assert.equal(result.disposed, true);
    assert.deepEqual(result.first.slice(0, 4), [0.75, 0.5, 1, 1]);
    assert.ok(Math.abs(result.first[4] - 2 / 3) < 1e-5);
    assert.ok(result.second[4] < 1e-5);
    assert.deepEqual(result.second.slice(5), [0.5, 1, 1]);
  } finally { await browser.close(); }
});
