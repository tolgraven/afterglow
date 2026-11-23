# Named fixture shader outputs

`afterglow.render.ir/emit-glsl-batch` compiles a map of named expressions into a
vertex shader. One vertex represents one fixture or pixel. The same definition
can be passed to `compile-batch` and evaluated on the CPU.

```clojure
(require '[afterglow.render.ir :as ir])

(def outputs
  {:color {:op :multiply :args [{:op :param :key :wash :type :vec3}
                                {:op :param :key :gain}]}
   :focus {:op :fract :args [{:op :bar}]}
   :aim   {:op :vec3 :args [{:op :position :axis :x}
                            {:op :const :value 1.5}
                            {:op :sin :args [{:op :beat}]}]}})

(def shader (ir/emit-glsl-batch outputs))
```

The shader above returns seven components per fixture. In each record, `:aim`
starts at offset 0, `:color` at 3 and `:focus` at 6. Field order is deterministic.
Use the returned offsets and types for each compiled definition.

Attach `:source` as a vertex shader. Set transform feedback to interleaved mode
with the `:varying` names from `:outputs`, in order, before linking. Compare
`:stride` with the context's maximum interleaved component count. Position is
a vec3 at location zero. For charted fixtures pass `{:surface-uv? true}` to `emit-glsl-batch`. When an expression uses `{:op :surface-uv :axis :u}` or `:v`, bind one additional vec2 at location one. Uncharted rigs use world XY and retain the three-float input. Native groups upload these static coordinates once. Use `(ir/evaluate-batch plan env positions surface-uvs)` for the CPU reference, with an ordered vector of pairs and nil for individual uncharted heads.

Supply the requested clock, meter and parameter uniforms
from a single captured show frame, disable rasterization and draw points in patch
order. Allocate four bytes per component per fixture. Keep frame ownership until
the GPU fence signals and the readback is complete.

The generated vertex shader targets GLSL ES 3. For desktop GL 3.3+, replace the
version directive with the desktop profile's directive. Results use float32.
`evaluate-batch` returns the corresponding float64 CPU reference fields.
Mechanical calibration, priority blending, fixture channel mapping and physical
publication are later stages of the show renderer.

## Evaluating outside effect middleware

An effect may return a batch with a `:field-request` instead of allocating device
resources in its step. The batch retains its normal target IDs, blend and opacity.
The request captures an evaluator-specific immutable group, the current input
environment, and optional per-field envelope gains.

Create `afterglow.render.fields/frame-evaluator` once for each output frame,
passing an evaluator with the call shape `(evaluate! group env)`. Apply its
returned function to the ordered contributions, then pass the result to
`frame/resolve-contributions`. Evaluate only on the frame owner. A successful
group's detached buffers remain available if an unrelated effect fails and the
owner retries that same frame. Discard this cache at the end of the frame.
