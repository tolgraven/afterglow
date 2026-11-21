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
