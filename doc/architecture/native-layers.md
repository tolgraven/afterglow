# Native effect layers

A compound cue can launch several effects into one layer by attaching
`:native-layer` to each launch source. One run owns one layer ID. Each slot
supplies its zero-based `:member`. The ordinary priority and launch ordering
place the complete layer at its last contributing member. Within the layer,
members run in slot order. Multiple blocks from one member keep their original
order, including duplicate target rows. A later overlapping sequence instance
with the same slot index retains its own controls. Independent effect workers
still compute their own raw outputs in parallel. The renderer materializes
deferred fields and folds these native values together before solving fixture
movement, extracting RGBW or packing coarse/fine bytes.

For code that directly invokes `afterglow.render.frame/resolve-contributions`,
put the same descriptor on each contribution block. Each member can contain
ordinary assignment blocks, typed batches, or a mixture of both.

```clojure
{:native-layer
 {:id "dance-floor/run-7" :member 1 :opacity 3/4 :targets :previous
  :transforms
  [{:attribute :beat-ratio :value {:op :divide :args [1 3]}}
   {:attribute :aim
    :value {:op :add
            :args [{:op :previous :attribute :aim}
                   {:op :multiply :args [[2 -1 3] {:op :field :attribute :beat-ratio}]}]}}
   {:attribute :color
    :value {:op :rotate-hue
            :args [{:op :previous :attribute :color}
                   {:op :field :attribute :beat-ratio}]}}]}}
```

Each target starts with the lower-priority native fields visible at the layer’s
position. A member can replace, mix or transform its own output and earlier
fields. Transforms execute in declaration order. A removed member contributes
nothing to the next frame. There is no cross-frame scratch state.

| Expression | Value |
| --- | --- |
| `{:op :previous :attribute k}` | Value at the beginning of this member |
| `{:op :incoming :attribute k}` | This member’s own value accumulated against zero |
| `{:op :field :attribute k}` | Value after applying this member’s writes and any preceding transforms |
| `:add`, `:multiply`, `:divide` | Two scalar or componentwise operands, including scalar/vector broadcast |
| `:rotate-y` | World-space XYZ vector rotated about +Y by the supplied radians |
| `:rotate-hue` | Color rotated by the supplied number of hue turns |

Each operator takes its operands in `:args`. Field references can specify a
`:default` expression for a missing value. Otherwise a missing upstream field
reports a fault on that member’s source. Literals may be numbers, exact Clojure
ratios, XYZ triples or thi.ng colors. Color fields are evaluated as native
colors. Physical RGB packing uses their red, green and blue components. Use
member or layer opacity for light mixing. Signed aim and direction retain world
units. The transient per-target `:beat-ratio` field accepts fractional and
out-of-unit values and can drive later color, aim and physical attributes. It
has no DMX address. Typed float batches retain their input precision. Use exact
numbers in assignments or transform expressions when rational arithmetic is
needed.

By default transforms apply to the fixtures written by the member’s incoming
blocks. `:targets :previous` additionally includes any head touched by earlier
members of this layer, including for a transform-only slot. It does not select
the rest of the rig. Each member’s instance opacity and envelope mix its result
with its input once. A layer's common `:opacity` then mixes the group result
against the lower layers once. Omitted opacities default to one. Fields that
the group never writes remain available from their original effects.

`afterglow.render.layers/validate-transforms!` accepts an ordered vector of at
most 128 transforms. Invalid arithmetic, fields and fixture values keep the
responsible effect's identity for the existing show fault handler. Native
operations are deterministic. Caches of independent input field evaluations
can be reused while the actual composition is reevaluated against the current
lower members and their captured values.

A reusable effect definition can declare a `:layer` map with `:transforms` and
optional `:targets :previous`. Its program executes before the slot-specific
transforms. The runtime uses the active definition revision on each frame.
Definitions may supply their own explicit fixture `:targets`, including for a
member that only transforms an earlier result. If launched separately, the
effect gets a layer at its ordinary priority. With `:targets :previous` and no
explicit fixture IDs, that standalone effect applies to heads with prior
writes in the current frame.
