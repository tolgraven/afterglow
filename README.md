# Afterglow partial-maximum shader replay

The input is the exact captured fixture for Afterglow PR #110. The fixture contains three Transit prepare packets with their original program IDs, two run packets per program, and the Afterglow CPU oracle for every float. The cases use one program each for 10, 18 and 24 partial-maximum layers on 64 charted heads. The second draw changes a parameter through the same program. Each readback is 1,024 bytes.

The merged Afterglow revision is `1f31801e61951201fc581c7515cecbc63e405ba1`. Its tree `a1ddb449a56551d7db37e1bea2e928a8d53599a6` matches the reviewed revision that generated the fixture, `a1443334ec7791a8a268012680c12ef12dfad4b7`. The committed browser guest comes from Tolglow `e4b654a8e16b4327d6bcacb87b0a68ca3366f128`, `native/AudienceCompute/Phone/audience-compute.js`. `prepare.clj` provides the generator. Use the included fixture for the physical run to retain the original program IDs.

Run on an Apple Silicon Mac with an installed Google Chrome and Node 20 or newer.

```sh
shasum -a 256 -c SHA256SUMS
npm ci --ignore-scripts --no-audit --no-fund
npm run replay
```

Use `CHROMIUM_PATH` to select a different Chrome executable. Playwright launches an isolated headless profile. By default the replay asks for ANGLE Metal and requires an Apple Metal renderer. It rejects SwiftShader or other software fallbacks. The explicit `npm run replay -- --software` option reproduces the Linux software check.

`result.json` records the renderer, Chrome version, input hashes, program and job IDs, buffer digests and maximum absolute error. The tolerance is 1e-5 per finite float. The prepare and draw times are offscreen browser guest round trips that include dispatch, readback wait and guest processing. They are separate from isolated GPU timestamps, Studio presentation cadence and DMX delivery. `swiftshader-reference.json` records the verified software run on these exact fixture and guest bytes.
