# Working on the Afterglow fork

This is `tolgraven/afterglow`, paired with `tolgraven/tolglow`. Read the
[architecture index](doc/architecture/README.md), companion v1 contract and
applicable nested AGENTS.md before changing behavior. Existing `tolmaster`
parameter/color/buffer/timing/rotation work has been merged; preserve it unless
an intentional, tested contract changes it.

- `project.clj` is the legacy application manifest. It now declares stable
  Beat Link 8.0.0 and required thi.ng dependencies. The original test-only
  snapshot override is historical; real DJ Link behavior remains unverified.
  `deps.edn` and `bin/test` provide plugin-free headless test entry points.
- `./bin/test pure` includes the functional model/runtime/control/render and
  injected device boundaries. `./bin/test parity` additionally exercises real
  old-source parity oracles. Neither lane activates
  physical DMX, Art-Net, MIDI, OSC or Push output. Loopback transport tests are
  allowed only with owned startup/cleanup.
- `runtime.clj` is the pure frame kernel; `runtime/engine.clj` advances the shared
  model and `executor.clj` owns bounded workers. The new runtime must not execute
  old effect closures through a compatibility adapter. Old source exists only
  as a feature/functional parity reference; the bridge experiment was removed.
- `control/` owns semantic commands, validated parameters, pure bindings/views
  and codecs. `control/devices/` owns composable sessions and optional transport
  shells. Push 2 source-derived tests do not establish hardware parity; Push 3
  currently supports explicitly configured generic MIDI bindings only.
- `render/` owns validated fixture packing and the CPU/GLSL expression IR. Keep
  the CPU oracle, explicit tolerances and privately owned buffers. Basic aiming
  is not complete fixture photometry or a universal calibration solution.
- Move effect state out of closures into explicit context. Pure functions return
  next state, assignments and intent data; the boundary owns clocks, RNG and IO.
  Mutable objects inside maps do not become immutable. Never call external
  callbacks or IO inside CAS retry functions.
- Preserve target precedence, kind resolution and byte packing. Parallelize
  independent work and merge by priority/launch order, never completion order.
  Define buffer ownership, cancellation/deadline behavior and publication rules.
- Channel packing, cross-universe addressing, RGBW, movement history and release
  are separate compatibility gates. A green pure lane cannot prove them alone;
  representative whole-show replay remains required.
- Use the companion `docs/work-items.edn` for exact disjoint path claims,
  dependencies, acceptance and evidence. Coordinate shared schema changes before
  modifying consumers. Release claims after recording actual verification.
- The new Tolglow studio uses ClojureScript re-frame/Reagent and a Ring backend.
  Device/legacy web code must use common domain operations rather than recreate
  separate lifecycle semantics. Preserve upstream licensing when restructuring.

Nested source, effects, runtime, render, control/devices, controller, web,
resources, development and test guidance supplies folder-specific rules.

Expanded expressive work is specified in the companion
[performance requirements](../tolglow/docs/product/expressive-performance.md).
MPE, Push 3/Seaboard and X-Touch/extender profiles keep device/channel/note/instance
identity and use verified message formats; support claims name the actual mode.
Category colors/widgets and automapping consume shared metadata, never duplicate
cue semantics. Waveform/modulation state, clocks and RNG remain explicit and
deterministic across workers. Optional webview/Max hosts or Link/AbleSet adapters
must not reintroduce a legacy effect compatibility layer or own a competing show
clock. Preserve reference licenses and distinguish tested codecs from hardware.
