# Working on the Afterglow fork

This is `tolgraven/afterglow`, paired with `tolgraven/tolglow`. Read the
[architecture index](doc/architecture/README.md), companion v1 contract and
applicable nested AGENTS.md before changing behavior. Existing `tolmaster`
parameter/color/buffer/timing/rotation work has been merged; preserve it unless
an intentional, tested contract changes it.

- `project.clj` owns application dependencies, test profiles and packaging.
  Use `lein test` for all discovered tests and `lein run` to launch.
  `lein test-pure` runs the explicit hardware-free core and transport suite.
  `lein test-parity` adds the source-parity regression namespaces.
  Use owned loopback services and capture sinks when testing.
- Leave a blank line between adjacent top-level Clojure definitions. Run `lein check-definition-spacing` to check tracked source.
- `runtime.clj` is the pure frame kernel; `runtime/engine.clj` advances the shared
  model and `executor.clj` owns bounded workers. The new runtime must not execute
  old effect closures through a compatibility adapter. Old source exists only
  as a feature/functional parity reference; the bridge experiment was removed.
- `control/` owns semantic commands, validated parameters, pure bindings/views
  and codecs. `control/devices/` owns composable sessions and optional transport
  shells. Push 2 source-derived tests do not establish hardware parity; Push 3
  supports captured User Mode/MPE mappings and an explicitly selected tethered USB
  display. See the controller qualification guide before reporting hardware results.
- `render/` owns fixture calibration, blending, DMX packing, numeric expression
  compilation and native GPU execution. Package the moving-head GLSL and WebGL
  solver in `resources/gpu/`. Tolglow selects the backend in show configuration
  and consumes the resulting fixture state. Keep the CPU reference, explicit
  numerical tolerances and privately owned readback buffers.
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
- Track work in [Tolglow’s GitHub Issues](https://github.com/tolgraven/tolglow/issues).
  Apply `project: afterglow` to core work. Add `project: tolglow` for work that
  also spans the wrapper or Studio. Record the owner, claimed paths,
  dependencies and acceptance checks on the issue.
  Coordinate shared schema changes with the Tolglow owner before editing
  consumers. Link the PR and its verification evidence from the issue.
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

The shared performance layer stores opacity/AR/private-clock controls under
instance `:system`, independent of authored parameters. Pause freezes evolution
but live parameter/global inputs remain responsive. Never cache typed output
arrays in the model; regenerate paused outputs without repeating intents. Group
selectors use captured output-derived categories and one atomic command receipt.
Phone/Watch sensor middleware must carry explicit immutable state, provenance,
units/calibration and musical timing; use supported APIs rather than infer raw
finger gestures from unrelated motion capabilities.
