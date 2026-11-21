# Functional rendering and expression compilation

Read the repository instructions and Tolglow's implementation contract first.
These namespaces are independent of the legacy show scheduler and perform no I/O.

- `frame/compile-patch` validates relative offsets, universe spans and physical
  channel ownership. Reuse its immutable plan until the rig revision changes.
- `frame/resolve-frame` accepts ordered contributions. Levels and linear RGB
  components are normalized to [0,1]; invalid values and overflowing blends fail.
  Color vectors and explicit emitter channels have distinct precedence. RGBW
  extraction is opt-in. Apply master/dimmer once, including real dimmer channels.
- Coarse/fine packing preserves the existing fractional-255 convention, not an
  assumed 0..65535 linear convention. Inversion and cross-universe fine offsets
  have dedicated tests. Change these semantics only with explicit migration.
- Inputs and compiled plans remain immutable. Private scratch arrays/transients
  and fresh returned byte arrays have one owner. Do not retain or mutate output
  arrays after publishing them to consumers. No atom, global clock or shared pool
  belongs in these namespaces.
- `:include-values? false` avoids preview maps. Its dense numeric path must match
  general-path bytes; exact Ratio/BigDecimal inputs and geometry use the general
  path. Keep the dense scratch bounds for heterogeneous fixtures. Request rich
  or compact values when the caller needs movement history or preview data.
- Geometry currently models explicit local +Z forward, +Y up, Euler fixture
  placement and calibrated yaw/elevation. It is not a complete legacy moving-head
  kinematics adapter or fixture-function interpreter.
- `ir/compile-expression` is the CPU oracle. Types, arity, finite results, domains,
  parameter references and complexity limits must be validated without eval.
  `ir/emit-glsl` generates GLSL ES 3 source and bindings; it does not execute GPU
  work. Keep float32 limitations and shader operator domains explicit.
- Run `afterglow.render.frame-test` and `afterglow.render.ir-test`. The benchmark
  `afterglow.bench-backend` verifies byte parity and measures stages/allocations
  without hardware. Only compare equivalent workloads; preserve raw results and
  report p95/p99 and allocations, not just one favorable median.
- `:compact-values? true` returns owned float64 fields and validity masks from
  the same target calculation. `project-compact` converts selected target indices
  to UI maps later; no second effect evaluation or DMX packing is needed. Use
  compact pan values as explicit next-frame movement history when omitting rich
  values; compact buffers do not update history on the caller's behalf.
- `resolve-batches` consumes ordered named typed arrays with explicit target IDs.
  It validates every input before accepting a completed frame. Scalar/color
  dense batches avoid one contribution map per head/attribute; geometry, rich
  values and highly heterogeneous patches use the tested general path. Keep both
  paths byte-equivalent. No input arrays may be mutated during a call.
- Dense fixture/channel plans contain only final fields and persistent values.
  Owned mutable scratch belongs to an invocation, never to these shared plans.
- `ir/compile-batch` compiles scalar float64 components without eval or generated
  Clojure code. `evaluate-batch` returns independent named fields, including aim
  (vec3) and focus (number). It is CPU batching, not SIMD. Exact numeric inputs
  convert to doubles; use appropriate oracle tolerances and quantized-output
  comparison. Preserve per-operator finite/domain rejection.
- Musical nodes `:beat`, `:bar`, and `:phrase` use captured `:beat` or
  `:elapsed-beats` and explicit positive finite `:meter` divisions. They return
  continuous phases. `:time` remains explicitly milliseconds. GLSL declares only
  musical inputs used by the expression; no live transport or wall clock reads.
- The benchmark accepts `--stages` as a comma-separated selection to profile an
  equivalent stage in isolation. The IR-through-DMX stage includes compact
  preview and validates every measured buffer; it excludes model/command
  scheduling, worker dispatch, transport and whole-show deadline behavior.
- `resolve-contributions` is the canonical mixed stream backend. Merge ordinary
  blocks between typed batches in their original order and pack once. The batch
  convenience API must not perform a separate physical render for each layer.
- Its transport path partitions by target: any geometric or exact-number write
  keeps that target's entire ordered history in general arithmetic; unrelated
  pixel batches stay dense. Exact master levels, rich values and excessive dense
  stride still use the full general oracle. Validate both partitions, pack each
  target once, and retain compact history by stable ID. Never convert an earlier
  exact target contribution to doubles merely because a later write is typed.
- Explicit fixture :footprint reserves the whole physical span, including gaps
  and universe crossings, and covers every coarse/fine offset. Use interval
  validation rather than allocating one entry per reserved channel.
- :previous-compact supplies pan/tilt history by stable target ID, including rig
  reordering. Avoid full map projections just to maintain movement history.
  portable-frame deliberately projects all targets and copies bytes at save time;
  a bounded browser preview must never become the complete saved output state.
