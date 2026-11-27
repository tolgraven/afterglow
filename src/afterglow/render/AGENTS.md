# Functional rendering and expression compilation

Read the repository instructions and Tolglow's implementation contract first.
Keep fixture blending, geometry, DMX packing and shader source generation pure.
The show owns the optional GPU sessions. Their workers own OpenGL calls, fences
and readback. Effect steps return data to the renderer.

- `frame/compile-patch` validates relative offsets, universe spans and physical
  channel ownership. Reuse its immutable plan until the rig revision changes.
- `frame/resolve-frame` accepts ordered contributions. Levels and linear RGB
  components are normalized to [0,1]; invalid values and overflowing blends fail.
  Color vectors and explicit emitter channels have distinct precedence. RGBW
  extraction is opt-in. Apply master/dimmer once, including real dimmer channels.
  `photometry/emitter-spectrum` owns additive channel names, their approximate
  photopic weights and linear RGB preview tints. Master, blackout and late
  presentation apply to named emitter channels. A UV channel has no visible
  RGB contribution. RGBW-only patches retain a specialized packing path.
- Continuous coarse/fine channels span all 65,536 physical codes. Use the DMX
  helpers for encoding and feedback. Profiled function ranges and fog retain
  coarse-byte boundaries. Test inversion, the byte carry and cross-universe pairs.
- Inputs and compiled plans remain immutable. Private scratch arrays/transients
  and fresh returned byte arrays have one owner. Do not retain or mutate output
  arrays after publishing them to consumers. Keep clocks, queues and mutable
  driver state inside the execution boundary of the session that owns them.
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
  The one exception is `::target-plans`, a bounded memo of each typed batch's
  target indices and the attributes all its targets support. Only a
  `PersistentVector` of target IDs is memoized, keyed weakly by its identity.
  A hit also needs the patch's own `:by-id` and `:target-order` and rows that
  still match the plan, because `vec` of a small `Object[]` aliases the array.
  Hold one vector per compiled effect to hit it. Entries are immutable once
  published; never write to their shared `int[]` indices. A failed check is not
  cached and still reports the first row. A new plan never evicts a live one:
  a full 8-slot probe window doubles the table (128 slots, up to 2048), and
  past that the plan is not cached. A miss clears entries whose vectors were
  collected, so retired effects free their plans on the next new vector. Until
  then the memo retains the index arrays of recently dropped vectors: measured
  4.9 MB for 127 stale 10,000-row reordered subsets on JDK 25 (prefix groups
  hold none). Fixtures with equal support share one interned set, so
  computing a plan intersects only distinct sets and allocates nothing else.
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
- Contribution blocks may carry opaque `:source` data. Validation/merge errors
  preserve their cause and ex-data while adding `:effect-source`. Final geometry
  uses the last positive-opacity source of effective aim, otherwise direction;
  zero-opacity or overridden writes must not steal attribution. Keep global
  patch/options/history failures unattributed. Track provenance at block and
  geometric-target level, without copying source maps into pixel assignments.
- Explicit fixture :footprint reserves the whole physical span, including gaps
  and universe crossings, and covers every coarse/fine offset. Use interval
  validation rather than allocating one entry per reserved channel.
- :previous-compact supplies pan/tilt history by stable target ID, including rig
  reordering. Avoid full map projections just to maintain movement history.
  portable-frame deliberately projects all targets and copies bytes at save time;
  a bounded browser preview must never become the complete saved output state.
- Rich movement history uses explicit top-level pan/tilt first, then packed
  channel values when an axis was not authored (for example all opacity zero).
  Missing axes may fall back to compact history or the neutral calibration
  default. Keep this consistent across reordered rigs and rich/compact output.

The calibrated shader, mount buffer layout and GPU readback live in this project at
`resources/gpu/`. Access the assets from the classpath through `afterglow.render.gpu`.
Keep show choreography in the caller. Test wrap history and numbers against `frame/resolve-frame`
and report float32 error and completed readback cost before enabling a physical-output path.

`ir/emit-glsl-batch` and the CPU batch compiler accept the same map of named
expressions. Bind varying names in returned order. Offsets and stride measure
float32 components per fixture. Validate the device's interleaved component
limit and use the declared clock and parameter bindings before a draw.

Keep expanded arrays for public GPU evaluations and distributed results.
The local fixture renderer can carry one detached tuple for a proven uniform
field. Exercise reversed or repeated targets, masked sources, geometry, fault
attribution and ordinary dense arrays when changing the physical column reader.

The optional JVM moving-head solver uses a private desktop OpenGL context and the
same packaged GLSL. Keep geometry out of the JOGL binding. Reuse the CPU frame
history lookup for stable fixture IDs, and explicitly retire failed contexts.

For physical native output, feed the ordered contribution stream to
`gpu.movement/resolve-contributions!` after deferred field evaluation. Blend
before rotation. Keep one bounded owner per show and pass only accepted movement
history. Native results must stay with their submitting frame. Check the
published rich and compact poses and coarse/fine DMX, including fallback.
The rounding guard takes its margin from `native-gpu/rounding-margins` by
`GL_RENDERER`. Add or narrow a row only from the seeded sweep's measured error
on that driver, and keep unmeasured drivers on the final row. Pan error grows
without bound toward the pan axis, so compare the scaled error with a margin.

Keep compound cue members in their declared order through native composition.
Resolve fields and group opacity before edge tracking, pan/tilt solving, RGBW
extraction and DMX packing. Preserve untouched attributes and the final
contributing member's fault source. Cover both rich and compact output.

A full-opacity compound containing only physical replacement writes can move
the original typed buffers to its anchor in slot order. Native colors, musical
scratch fields, transforms and nontrivial blends need the typed field reducer.
Test both paths, including ordered source attribution and later reads of
previous values, before changing dispatch. The companion Tolglow profiler
compares these cases on 64 animated moving heads.

A profiled fog channel has [off full] endpoints in physical coarse DMX units.
Its idle/blackout byte comes from the fixture definition, including reversed
pumps and cross-universe fine channels. Explicit cue assignments still take a
normalized logical value. Use atmosphere/physical-level to request a physical
value through an inverted channel, and frame/idle-universes for shutdown.

Use `afterglow.render.emission` for changes to the light in a completed frame.
Read actual emitter drive after the physical dimmer. Keep packed universes and
rich/compact previews consistent and hold shutter, strobe and other discrete
channels. When enforcing a budget, quantize toward lower delivered intensity,
including on inverted and cross-universe fine channels.

Compile output processors against the fixture order once per patch. A budget
can supply one normalized gain per fixture in `double[]`. For asymmetric
output response, keep the last unquantized emitter drives as immutable state
and seed newly selected heads from their last committed output. Quantize only
at publication. Compare compact and rich output against the same packed bytes.

When HDR is enabled, blend nonnegative emitter overrange before tone mapping.
Compute spatial spill from one untouched frame, including the shutter gate and
original dimmer. Preserve gain and opacity as independent controls. Validate
nonemission channels at their original ranges in both typed and rich output.
[Gain and spatial highlight spill](../../../doc/architecture/highlight-spill.md)

Effect blocks lower to numeric IR so CPU steps, native transform feedback and
mesh materials use the same arithmetic. Dry inputs and shader varyings come from
the captured frame. Return a pure observation in result metadata for a subscribed
display. Keep material definitions data-only and avoid serializing live observers.
Exercise authored GLSL through the scalar oracle and an actual shader readback.

Charted materials use optional fixture `:surface-uv [u v]` alongside world XYZ. Keep the original single-attribute path for rigs without charts and compare mixed coordinate fields across scalar, packed and GPU runners. [Shader fields](../../../doc/architecture/numeric-shader-fields.md)
