# Afterglow engine source

Read the root `AGENTS.md` and the coordinated migration documentation in the
sibling tolglow repository before changing shared interfaces. This fork supplies
the renderer, effects, fixtures, clocks, controller adapters, and legacy web app.

## Boundaries to preserve

- `effects.clj` owns effect lifecycle and ordered assigner composition.
  `show.clj` owns effect priority, identity, scheduler, workers, and output.
- Preserve ascending effect priority and launch order for equal priorities.
  A replacement activation gets a new ID; an old ID must not stop its replacement.
- A frame uses one explicit time snapshot. Preserve per-target assigner order
  while parallelizing independent work; never merge according to task completion.
- Keep DMX universe/address conventions and coarse/fine channel packing stable.
  RGBW conversion, movement calibration, and fixture function ranges are separate
  semantics; do not replace them with unvalidated generic color math.
- New computation takes data and returns data. Confine atoms, mutable buffers,
  threads, MIDI/OSC/OLA, USB, and network calls to owned boundary adapters.
  Do not invoke callbacks or perform I/O inside retryable `swap!` functions.
- Keep startup explicit. Requiring a new pure namespace must not open devices,
  bind a port, start a scheduler, or select a global show.

## Verification and parallel ownership

Characterization tests live in `test/afterglow`; use the repository's documented
test commands and report the exact lane run. The full suite reaches dependencies
through `channels -> fixtures.qxf -> web.layout` and `show -> controllers/midi`;
a passing dependency-free subset is not evidence that those paths compile.
Tests may construct a show but must not call `show/start!` or send hardware output.
Use fixed snapshots, local buffers, and isolated show bindings. Dispose resources
in `finally` when a test needs workers.

Keep interface changes separate from device rewrites. Claim concrete files in the
shared tracker before editing; source tasks, controller tasks, and UI tasks can
run concurrently only after agreeing on command and snapshot schemas. Record
known defects separately from intended semantics rather than freezing accidental
behavior into the new API.
