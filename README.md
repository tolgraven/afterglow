# Push 3 cue variation replay

[Still](push-3-variation-overlay.png) · [Short clip](push-3-variation-overlay.mp4) · [Owner and transfer receipts](receipts.json) · [Uncaptioned native frame](frames/03-saved-transferred.png)

This is a virtual Push 3 User Mode replay with injected MIDI and injected USB transfers. The loopback Studio serves its production display bundle. Chromium produces the 960 × 160 display raster, and the Afterglow image sink packs it and completes the two writes through a recording backend. The images inside the clip and still come from the captured wire payloads. The captions use the running show owner’s acknowledgements, exact authored values and preview dimmer bytes. The clip holds each captured stage long enough to read.

The replay launches a held cue, opens the full overlay, appends a slot, applies a generated state, switches to parameter rows, recalls the saved state and releases the original live pad. It also presses a variation while the matching image is packed but before its transfer and checks that the preceding owner receipt and authored parameters are unchanged. The release receipt names the original cue instance.

Applying and recalling moved the authored level from 0.70 to 0.15 and back to 0.70. The exact beat ratio moved from 1 to 1/2 and back to 1. The recorded preview dimmer byte followed 179 → 38 → 179. All five dispatched actions returned accepted owner receipts.

Each captured 16-byte header and 327,680-byte payload is stored alongside its Chromium source image. The decoder checks the black stride padding and compares every visible pixel with the Chromium image at BGR565 precision. The USB backend is injected. On-device timing, panel scanout and physical operation remain unqualified.

## Reproduce

Use Tolglow `ac31f60439a5edbd8a855fffacb72c5e3cb13714` with Afterglow `4207bc12c2f2ca8c061732935794bf2598728d3d`. Build the Studio bundle with `npm ci` and `npm run studio:build` in the Tolglow checkout. This recording reused the bundle built at Tolglow `5814af5b227f003aa5324d980393393875d6a8d2`, whose tracked Studio, shared frontend, resources and build inputs match the recording’s revision. [Bundle checksums](frontend-bundle-sha256.txt)

From the Tolglow checkout, with Chromium, FFmpeg, NumPy, Pillow and DejaVu Sans installed:

```sh
export AFTERGLOW_ROOT=/path/to/afterglow-push3-pad-overlay-547
evidence=/path/to/push3-pad-overlay
output=$(mktemp -d)
classpath=$(lein classpath)
java -Djava.awt.headless=true -XX:ActiveProcessorCount=2 -Xmx700m \
  -cp "$classpath" clojure.main "$evidence/replay.clj" "$output" \
  "$(command -v chromium)" "$PWD/node_modules/playwright-core" \
  "$(git rev-parse HEAD)" "$(git -C "$AFTERGLOW_ROOT" rev-parse HEAD)"
python3 "$evidence/render.py" "$output"
```

Afterglow master `0e0e100a53c0eb0cda5e50ee02e3451486f52a30` and the feature head produce clean merge tree `0f253d728183331a3d660b17a68e4a51b4fec140` with `git merge-tree --write-tree`. The capture retains the feature head as its source pin. [Merge receipt](afterglow-merge-tree.txt)
