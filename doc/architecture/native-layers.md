# Native effect layers

A compound cue can launch several effects into one layer by attaching
`:native-layer` to each launch source. One run owns one layer ID. Each slot
supplies its zero-based `:member`. The effective instance ordering
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

### Reordering active instances

Submit `{:op :instance/move-after :instance-id source-id :after-instance-id
target-id :expected-revision captured-revision}` through the show owner. Use the
instance IDs and revision captured from the committed view. The owner rejects
stale captures and endpoints that have stopped or entered release. The accepted
receipt contains `:instance-ids` in the new render input order. Read
`afterglow.control.views/snapshot` or `afterglow.control.instance-order/ordered`
to project that order in a dedicated active-cue view.

A standalone instance moved across tiers takes its destination's effective
priority. Its original priority and launch order are retained. Compound moves
carry every member together within one tier, including any releasing members.
The owner rejects a target compound with interleaved members because its render
position can change as individual members contribute or finish. The optional
`{:op :instances/shuffle :seed 42}` command shuffles running standalone slots
inside each effective tier while keeping compound and releasing slots in place.

Saved instances can carry `:render-order` and `:render-priority`. A save reader
can use `afterglow.control.instance-order/valid-render-position?` to check that
the rank is a nonnegative integer and that a tier override is finite and has
an explicit rank. Retain these fields when rekeying instances into a new show
epoch. Missing fields use the original priority and launch order.

### Overwritten packed columns

After native groups read their backdrop and compose, the packed renderer walks
physical batches in reverse priority order. An opaque replacement of the first
`n` targets in patch order covers the same field in earlier opaque replacements
for those targets. The original forward pass still validates the covered
values and attributes failures to the effect that produced them. It can then
skip reading, blending and writing those destinations. The remainder of a
partly covered column keeps its usual blend and order.

A target permutation, varying mask, partial opacity, `:add` or `:max` can use
the previous field. The planner drops coverage for fields touched by those
batches. Arbitrary row assignments clear all coverage. General geometry retains
its calibrated arithmetic and movement history. Effects continue to advance
state, emit events and produce diagnostics each frame. Removing a cover or
changing opacity rebuilds the plan on the affected frame.
