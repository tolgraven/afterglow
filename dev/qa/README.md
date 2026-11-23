# Optical field verification

Run `npm ci` and `npx playwright-core install chromium` in the Leiningen project.
The browser test asks Leiningen to emit the current shaders and evaluate their
float64 reference samples. Set `CHROMIUM_PATH` to use another Chromium executable.

```sh
node --test test/js/optical-effect-blocks.cjs
```

The test runs the emitted fragment shader for each of RGB, dimmer and focus,
then runs the same three fields together as a five-float interleaved transform
feedback batch. The fixture includes through-water modulation, a position-driven
color gel, homogeneous fog transmission and the ribbed-glass GLSL expression.
Two heads with the same XYZ carry different surface UVs. Another pair shares
its chart across different depths. A fifth head uses the individual world XY
fallback. The browser point renderer switches between charted and uncharted
geometry on the same compiled program. Every GPU component is
compared with the Afterglow reference at three beats and two fog densities.
Normalized values must agree within 1/8192 (less than 1/32 of an 8-bit DMX step).
The test prints the largest error for each path and the active graphics driver.
SwiftShader is the default reproducible software device. Use
`AFTERGLOW_ANGLE=system` for the browser's default driver.

## See the moving field

```sh
lein run -m afterglow.qa.effect-blocks /tmp/optics.json
node dev/qa/capture-optical-fields.cjs /tmp/optics.json /tmp/water
```

The capture writes `/tmp/water.png` and a six-second `/tmp/water.mp4`; encoding
requires `ffmpeg` with libx264. Both panels contain the same 84 × 48 curved LED
surface. The left panel evaluates each fixture in metres across world XYZ. The
right panel samples water and glass using its unwrapped UVs while the gel still
responds to world height. Both advance from the
same song beat at 120 BPM. A single GPU buffer carries the real computed RGB,
dimmer and focus straight into the display pass. RGB times dimmer sets emitted
color and focus shapes the spots. Camera projection, exposure and display
transfer are visualization settings. The fixture does not send hardware output.

The November 2026 run on Chromium found a maximum absolute error of
0.000000166 on Mesa llvmpipe (OpenGL ES 3.2) and 0.0000933 on ANGLE SwiftShader.
Each result includes the full fragment and transform-feedback paths, including
the hand-authored GLSL used for the focus ribbing. Both drivers ran on software.
To reproduce the Mesa run where surfaceless EGL is installed, set
`EGL_PLATFORM=surfaceless LIBGL_ALWAYS_SOFTWARE=1 AFTERGLOW_ANGLE=gl-egl`.
