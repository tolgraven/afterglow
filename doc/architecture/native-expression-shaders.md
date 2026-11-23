# Numeric lighting expressions on a JVM GPU context

Afterglow can evaluate a map of lighting fields for a rig in one native draw.
Each input point is a fixture or pixel position. A vertex invocation runs the
expressions and writes one interleaved row of scalar/vector results. The host
waits on that draw, reads the rows back and returns one owned array per field.

```clojure
(require '[afterglow.render.gpu.expressions :as shader]
         '[afterglow.render.frame :as frame])

(def fields
  {:color {:op :multiply
           :args [{:op :param :key :wash :type :vec3}
                  {:op :position :axis :x}]}
   :focus {:op :param :key :focus :type :number}})

(with-open [program (shader/open! fields [[0.0 0 0] [0.5 0 0] [1.0 0 0]])]
  (let [batch (shader/evaluate! program {:params {:wash [1.0 0.25 0.5] :focus 0.7}})]
    (frame/resolve-batches patch [(assoc batch :target-ids [:left :center :right])])))
```

Supply the compiled `patch` and target IDs in the same order as the positions.
Results have the same shape as `ir/evaluate-batch`, including separate `:type`,
`:components` and `:values` per field. GPU evaluation uses float32. Reading each
component into a double array lets the regular fixture packer consume the
result and keeps returned frames independent. The example computes DMX bytes
in memory. Physical output continues using its selected backend.

Open the plan once with `lein with-profile +native-gpu repl`. Opening uploads
the positions and validates the GPU’s interleaved component limit. Position
inputs may be vectors of triples or packed double arrays. Every evaluate call
takes a fresh environment with only the clock inputs and parameters used by its
expressions. Musical operations read the same `:beat`, `:elapsed-beats`,
`:meter {:beats-per-bar ... :bars-per-phrase ...}` as the CPU evaluator. A
missing uniform, invalid meter, out-of-range float or nonfinite result rejects
the batch. Operator domains are the caller’s responsibility on both backends.

The program shares the moving-head solver’s native context lifecycle and fence
handling. Rebuild for fixture/expression changes and close old programs after
their callers are finished. Interactive applications can keep the last
published program until a replacement compiles. The returned plan supports
one in-flight evaluation. Its timeout bounds fence waiting. Keep it on a
render worker when the caller must remain responsive.

Run `lein with-profile +native-gpu test afterglow.render.gpu-expressions-test`
for multi-field CPU/GPU comparisons, explicit musical clocks, uneven positions,
nonfinite-result recovery and complete DMX universe comparison. Use
`xvfb-run -a` with Mesa on headless Linux. Software OpenGL establishes correctness
on the tested cases. Physical GPU throughput and general byte equivalence
require measurements on the target machine.


The macOS 15 Apple Software Renderer returned absolute errors of 0.00075151 at
`abs(sin(8.5))` and 0.00065782 at `abs(sin(0.75))`. The two sampled sine
values have an exploratory 0.001 absolute tolerance. Arithmetic/vector fields
use 0.000003 absolute plus 0.000003 relative tolerance. The 256-pixel packing
case uses exactly representable arithmetic and requires identical DMX bytes.
These measurements do not bound transcendental error for other inputs.

## One context for a show

```clojure
(require '[afterglow.render.gpu.session :as gpu])

(def spots (gpu/group fields [[0 0 0] [0.5 0 0] [1 0 0]]))

(with-open [owner (gpu/open! {:max-programs 8 :queue-capacity 4 :timeout-ms 25})]
  (let [rendered (gpu/evaluate! owner spots {:params {:wash [1 0.25 0.5] :focus 0.7}})]
    (frame/resolve-batches patch [(assoc rendered :target-ids [:left :center :right])])))
```

Create one owner at show startup. Prepare a group when editing effects or
patching fixtures and reuse it across frames. The value key contains the complete
definitions and copied positions in patch order, normalized to the GPU's float32
inputs. Equal descriptions reuse a program even if built independently from a
packed double array or vectors. Moving or reordering fixtures produces a new
group whenever the ordered GPU inputs change. Keep the matching target IDs in
the caller’s frame snapshot. The cache retains up to `:max-programs` (default
eight). It compiles one prospective replacement before evicting the least
recently used group, so a rejected shader preserves the prior program. Use
`(gpu/evict! owner group)` to explicitly discard a retired rig or definition.

One worker serializes GPU calls. Multiple frame workers can call `evaluate!`
or use `(gpu/submit! owner group env)` for a Java Future. Submission captures
uniforms immediately. The queue has room for `:queue-capacity` waiting jobs
(default four) plus one active job. Saturation throws `::gpu/busy` immediately.
The host chooses how to handle a late frame. Each successful evaluation owns
its output arrays; later draws and eviction cannot change them. `gpu/status`
reports renderer, queued and resident counts, cache hits, misses and evictions.

`(gpu/close! owner)` stops intake, cancels waiting futures, lets the active draw
finish and releases the context before returning. `(gpu/close! owner 25)`
waits up to 25 ms for cleanup and returns false if the worker is still releasing
the context. Cleanup then completes independently. Driver calls and compilation
can outlast the fence timeout. Cancelling a future never interrupts an executing
native call. The show publisher controls whether to accept a completed frame.

## One deadline for expressions and physical movement

`afterglow.render.compute` owns native submission, the time budget, CPU fallback
and physical rendering for a show. Set `:compute-backend` and `:movement-backend`
independently to `:native-gpu` to opt in. Each defaults to `:cpu`. A CPU-only
owner acquires no worker or graphics context. Choose a `:budget-ms` that leaves
room for CPU packing and the output sink. The core default is 25 ms.

```clojure
(require '[afterglow.render.compute :as compute]
         '[afterglow.render.frame :as frame]
         '[afterglow.render.ir :as ir])

(def patch (frame/compile-patch
             [{:id :spot :universe 0 :address 1 :channels {:focus [1 2]}}]))
(def fields {:focus {:op :param :key :focus}})
(def group (compute/prepare-group fields [[0 2 0]] (ir/compile-batch fields)))

(let [owner (compute/open! {:compute-backend :native-gpu :budget-ms 10})]
  (try
    (let [render (compute/frame-renderer owner (System/nanoTime))]
      (render patch
              [{:kind :batch :source :focus-sweep
                :batch {:target-ids [:spot]
                        :field-request {:group group :env {:params {:focus 0.35}}}}}]
              {:compact-values? true}))
    (finally (compute/close! owner))))
```

Keep the owner for the show's lifetime and the prepared group for the lifetime
of that effect definition and ordered fixture selection. A group retains its
float64 plan and a snapshot of the original xyz positions. The CPU can therefore
evaluate a prepared request even when native libraries are unavailable or the
host selects CPU rendering. `expressions-enabled?` lets a compiler decide
whether to prepare future requests for native evaluation. Ordinary assignments
and already evaluated numeric batches are accepted by the same renderer.

Create a renderer for each frame when its clock is captured. Reuse that function
only for fault-isolation retries of that frame. Completed requests reuse their
owned arrays on a retry. A new frame captures new parameters, a fresh cache and
a new deadline. Calibrated movement receives the same deadline after the field
results are blended. A late result uses the float64 fallback and cannot update
another frame. Pass the last accepted rich or compact state in the regular
render options, and let the show's output owner decide when to publish.

`(compute/status owner)` reports the configured and active expression backend,
completed native batches, CPU fallbacks, deadline fallbacks and native session
metrics. `(compute/movement-status owner output)` reports the movement decision
and head counts for that output. Pass nil for a status before the first output.

## CPU batch costs on dense pixel rigs

The CPU evaluator samples clock, beat, bar, phrase and parameter inputs once
per batch invocation. It copies each fixture's xyz coordinates into three
scratch slots as it evaluates the spatial expression. Scratch belongs to the
invocation, so workers can share a compiled plan and callers can retain its
previous output. The renderer identifies batches whose target IDs form a
prefix of patch order and writes their rows directly. Other orders and repeated
IDs retain their own row mapping.

The following measurements compare Afterglow `9b7e456` and `fa22954` on a
shared AMD EPYC 9V74 Linux host. Each stage had 130 warmups and 150 samples
in OpenJDK 21.0.13, Clojure 1.12.7, with three visible processors and a 1 GiB
heap. Each sample included compact preview generation. The harness compared
every universe byte with the scalar renderer outside the timed interval.

| RGBW pixels | Stage | CPU time p50, before → after (ms) | Wall time p95, before → after (ms) | Allocation p50, before → after (bytes) |
| ---: | --- | ---: | ---: | ---: |
| 1,000 | Typed fields through DMX | 1.29 → 0.91 | 6.16 → 1.76 | 366,832 → 322,384 |
| 1,000 | Spatial expression through DMX | 1.73 → 0.92 | 2.03 → 1.77 | 746,584 → 337,416 |
| 10,000 | Typed fields through DMX | 9.75 → 3.58 | 30.78 → 7.66 | 5,169,824 → 3,240,032 |
| 10,000 | Spatial expression through DMX | 11.30 → 7.44 | 27.74 → 25.92 | 7,650,184 → 3,326,768 |

Run the same stages from each revision's project root. The report includes
wall time, current-thread CPU time and allocation samples.

```sh
JAVA_TOOL_OPTIONS="-XX:ActiveProcessorCount=3 -Dafterglow.benchmark.revision=$(git rev-parse HEAD)" \
  lein with-profile +benchmark run -m afterglow.bench-backend \
  --heads 1000,10000 --warmup 130 --samples 150 \
  --stages typed-batch-resolution-with-compact-preview,ir-spatial-effect-through-dmx-with-compact-preview
```

The companion Tolglow sculpture benchmark exercises differently mounted moving
heads alongside 10,000 or 20,000 RGBW pixels on twisted strips. It includes
effect scheduling, fixture blending, compact preview and encoded ArtDMX. With
Afterglow `fa22954` and Tolglow `ebfbcc2`, the 20,000-pixel, 64-mover direct
output run took 30.09 ms at the median and 48.26 ms at p95. With independent
output scheduling the corresponding times were 24.81 and 33.80 ms. A 40 Hz
physical-output target leaves 25 ms per frame. See the
[Tolglow workload and capture checks](https://github.com/tolgraven/tolglow/blob/ebfbcc20eb4da1793e2862ef048c4d364e1da2da/dev/tolglow/bench_show.clj).

The native shader backend can perform spatial color and motion arithmetic. It
still reads back fields for CPU blending and packing. Compare complete
publication times, readback stalls and DMX bytes on the intended GPU when
selecting that backend. These measurements used the float64 CPU renderer and
a capture sink. [Moving-head shader calibration and precision](moving-head-shaders.md)
