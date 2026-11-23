# Numeric effect materials

`afterglow.render.blocks/plan` lowers a dry signal and an ordered vector of prefab stages into one numeric IR expression. Pass the expression to `ir/compile-expression` for a scalar sample, `ir/compile-batch` for a packed array per attribute, or `ir/emit-glsl-batch` for native transform feedback. The latter preserves separate layouts for linear color, dimmer, focus and other fixture fields.

```clojure
(def water {:block :optics/through-water :coordinates :surface-uv :inputs {:phase {:op :bar}}})
(def rgb (blocks/plan {:base [0.9 0.6 0.4]
                       :stages [water {:block :optics/gel}]}))
(def shader (ir/emit-glsl (:expression rgb)))
(def sample ((blocks/compile-trace rgb) {:elapsed-beats 2.5 :meter {:beats-per-bar 4}
                                         :position [4.2 2.6 -1.0] :surface-uv [0.2 0.6]}))
```

Set `:coordinates :surface-uv` on a stage to sample a fixture’s `:surface-uv [u v]`. For example, a water pattern can follow the seams of a folded LED surface while a gel in the same chain uses its physical height. Omitting a pair uses that fixture’s world X and Y. Pairs can tile beyond the unit square. A mapped stage reads zero for depth. For fragment rendering bind the requested `v_uv` and `v_position` varyings. A stage can also project onto a plane via two coordinate expressions, or supply all three field coordinates.

A template defines a name, a default blending mode, named input defaults and a numeric IR expression or portable GLSL expression. The GLSL reader accepts arithmetic, stage-local `position.x/y/z`, physical `world.x/y/z`, independent `uv.x/y`, numeric GLSL functions and vector constructors. Its result goes through the normal type, domain and size checks. The standard catalog includes through-water, ribbed-glass and gel transmission, uniform fog attenuation and musical sine, saw, pulse and triangle oscillators.

Use `blocks/middleware` to attach a chain to a numeric or vector leaf in an existing effect context. It reads the dry leaf on entry and returns a new context. `blocks/compile-trace` builds an on-demand evaluator for the base, signed change and value of each stage, and final result. A compiled effect can expose a query function under `:afterglow.runtime/observe` in result metadata. `runtime/observe` calls it after a successful commit. Evaluate the trace off the lighting deadline and keep observer closures out of saved data.

The optical-field test compiles actual fragment and transform-feedback programs for UV and world coordinates and compares readback to the JVM. The capture draws two folded LED surfaces using five native output components per head. See the instructions and tolerances in [the shader QA harness](../../dev/qa/optical-fields.mjs).
