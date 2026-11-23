// Run: lein run -m afterglow.qa.effect-blocks /tmp/shaders.json
//      node dev/qa/capture-optical-fields.cjs /tmp/shaders.json /tmp/water
// Produces a canvas PNG and 6s MP4. Left is world space, right is surface UV.
const fs = require('node:fs/promises');
const path = require('node:path');
const {spawn} = require('node:child_process');
const {once} = require('node:events');
const {launch} = require('./browser.cjs');

async function main(input, prefix) {
  if (!input || !prefix) throw Error('Supply an emitted fixture JSON path and an output prefix');
  const proof = JSON.parse(await fs.readFile(input, 'utf8'));
  const source = await fs.readFile(path.join(__dirname, 'optical-fields.mjs'), 'utf8');
  const browser = await launch();
  const fps = 20;
  const encoder = spawn('ffmpeg', ['-hide_banner', '-loglevel', 'error', '-y', '-f', 'image2pipe', '-framerate',
    String(fps), '-i', 'pipe:0', '-c:v', 'libx264', '-crf', '18', '-pix_fmt', 'yuv420p', '-movflags', '+faststart', prefix + '.mp4'],
    {stdio: ['pipe', 'inherit', 'inherit']});
  const done = once(encoder, 'exit');
  try {
    const page = await browser.newPage();
    await page.evaluate(async ({proof, source}) => {
      const url = URL.createObjectURL(new Blob([source], {type:'text/javascript'}));
      try {
        const {demonstrate} = await import(url);
        const canvas = document.createElement('canvas');
        canvas.width = 1104; canvas.height = 424;
        const demo = demonstrate(canvas, proof);
        window.opticalFrame = beat => {
          demo.render(beat);
          return canvas.toDataURL('image/png').split(',')[1];
        };
      } finally { URL.revokeObjectURL(url); }
    }, {proof, source});
    for (let frame = 0; frame < fps * 6; frame++) {
      const beat = 0.7 + (2 * frame / fps); // Explicit 120 BPM compared at identical song times.
      const png = Buffer.from(await page.evaluate(t => window.opticalFrame(t), beat), 'base64');
      if (frame === 0) await fs.writeFile(prefix + '.png', png);
      if (!encoder.stdin.write(png)) await once(encoder.stdin, 'drain');
    }
    encoder.stdin.end();
    const [status] = await done;
    if (status !== 0) throw Error('ffmpeg exited with code ' + status);
  } finally {
    encoder.stdin.destroy();
    if (encoder.exitCode === null) encoder.kill();
    await browser.close();
  }
}
main(...process.argv.slice(2)).catch(error => {console.error(error); process.exitCode = 1;});
