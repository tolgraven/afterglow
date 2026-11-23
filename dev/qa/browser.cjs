const {chromium} = require('playwright-core');

// CI uses SwiftShader. Set AFTERGLOW_ANGLE=system to use the browser's driver.
exports.launch = function () {
  const driver = process.env.AFTERGLOW_ANGLE || 'swiftshader';
  const args = driver === 'system' ? [] : ['--use-gl=angle', '--use-angle=' + driver, '--ignore-gpu-blocklist'];
  if (driver === 'swiftshader') args.push('--enable-unsafe-swiftshader');
  return chromium.launch({executablePath: process.env.CHROMIUM_PATH || chromium.executablePath(), args});
};
