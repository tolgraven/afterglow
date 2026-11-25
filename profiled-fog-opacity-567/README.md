# Profiled fog group fader capture

The headless Tolglow owner rendered ordinary and native-layer cues in both show modes with no output sink attached. The fixture declares DMX byte 255 off and byte 0 full. Each sample records the packed byte. The chart uses the fixture range to convert bytes to percentages of rated flow.

- Tolglow PR #567 snapshot `86a2c952b4cac56549ac662852bce9185d281245`.
- Released Afterglow `d1edde977b389404cde395d2742f7cc3046d3698` for the before capture.
- Corrected Afterglow `7b897b3ee89c5a0ab0cb78629f06f4f6de7eed96` for the after capture.
- Publication head `16b30b164d39c335d67f3ad96d5f2c42e6e6fa2b` merges Afterglow master `554ec20ec56621dae7f94209b50cb2c5c6e2c621`. The fog source and regression test files are identical to the corrected capture revision.

The corrected renderer keeps the off cue at byte 255 through the fader range. A cue authored at full flow fades toward 255, with byte 128 at half level and 255 at zero. Ordinary and native members produce the same bytes in both modes.

Replay either revision from its Tolglow checkout with the paired Afterglow source and the normal Leiningen profile. `capture.clj` takes the output JSON path, Tolglow revision, and Afterglow revision.

```sh
AFTERGLOW_ROOT=/path/to/afterglow lein run -m clojure.main /path/to/capture.clj \
  /path/to/capture.json "$(git rev-parse HEAD)" "$(git -C /path/to/afterglow rev-parse HEAD)"
python3 /path/to/render.py
python3 /path/to/animate.py
```

The still and six-step GIF read `before.json` and `after.json`. Each animation step shows the captured fixture byte for both revisions. The focused Afterglow logs cover rich, packed, typed-batch and native rendering, physical DMX inversion, a split-universe fixture, and preservation of an earlier writer at zero.
