# Fixture selection in a virtual venue

A volume selects fixture positions in the same metres and Y-up world space as an aim point. Use a static shape for a persistent zone, a moving ball for a performance control, or a highlight field to react to another head's HDR excess. A selection and its events are portable show data. The host decides whether entry launches a cue, whether exit releases its instance, and which functions subscribe to a bounce.

```clojure
(require '[afterglow.spatial :as spatial])

(def stage
  (spatial/prepare
    {:bounds {:min [-4 0 -4] :max [4 5 4]} :gravity [0 -9.81 0]
     :volumes {:throw {:shape :ball :position [-1 2 0] :velocity [4 2 0]
                       :radius 0.35 :restitution 0.92 :hardness 0.4
                       :angular-velocity [0 2 0] :throw-id 1}
               :well {:shape :ball :position [1 2 0] :radius 0.2
                      :fixed? true :attraction 2.5}
               :front {:shape :box :min [-4 0 -3] :max [4 2 0]}
               :halo {:shape :hdr :source-id :key :threshold 0.08}}}))

(def rig (spatial/prepare-rig [{:id :key :position [0 2 0]}
                               {:id :mirror :position [0.5 2 0]}]))
(def first-frame (spatial/advance nil stage {:time-ms 0 :epoch 1} rig {}))
(def next-frame (spatial/advance (:state first-frame) stage {:time-ms 25 :epoch 1} rig {}))
(get-in next-frame [:signals :throw :position])
```

`:signals` exposes a ball's position, velocity, speed, direction, rotation in radians, radius and deformation. `:members` maps each volume ID to a set of fixture IDs. `:events` gives timestamped `:spatial/enter`, `:spatial/exit` and `:spatial/bounce` maps. Membership events carry the volume and fixture IDs. A wall bounce includes `:surface [:x :max]` or the corresponding axis and side. A body collision sends one bounce to each ball with the other ball's ID. Both report incoming normal impact speed and deformation. A resting contact produces no recurring bounce events.

## Throws and gravity

A ball's initial position and velocity are in metres and metres per second. Change `:throw-id` to repeat the same throw. Changing its initial position, velocity or rotation also starts a fresh trajectory. Edits to radius, restitution, angular velocity or gravity take effect on the running body. Pass resolved numeric values each time a musical modulator changes those controls. A ball must fit within the room bounds. `:restitution` ranges from zero to one. With zero gravity and unit restitution it can bounce indefinitely. `:hardness` ranges from soft at zero to rigid at one and controls collision deformation. `:mass` sets relative inertia for pair collisions. A positive `:attraction` in m³/s² pulls other bodies toward the ball with a softened inverse-square force. A fixed ball can serve as a gravity well.

Physical time advances in 5 ms steps independently of render cadence. The integrator takes up to 80 steps on one call and reports any unprocessed time as `:dropped-ms`. Between substep positions the sphere sweeps its path for fixture entry and exit, so a small fixture can be crossed entirely between rendered frames. Ball-to-ball collisions are discrete pair contacts. Extremely fast, small balls can cross one another in a substep. Pair contacts resolve in stable volume-ID order. The room resolves up to eight wall impacts per axis in one substep. These bounds keep a long time jump from monopolizing the show thread.

Only pass `:state` into the next tick or a show file. Cache the prepared rig until placement changes and the prepared configuration until the resolved controls change. The host can skip the entire simulation while there are no bindings or listeners. Use `(spatial/rebase saved-state clock)` when resuming from sleep or moving a saved run into a new epoch. This preserves ball dynamics and current member sets without replaying elapsed hidden time or relaunching leases. A transported pause with `:playing? false` also freezes motion.

## Other shapes

A sphere uses `:position` and `:radius`. A box uses inclusive `:min` and `:max` coordinates. A cylinder uses a center, radius and full height along the Y axis. For a convex polyhedron, pass `:planes [{:normal [nx ny nz] :distance d} ...]`. Each plane includes points where the dot product is at most `d`. Combine these primitives with `:union`, `:intersection` and `:difference`, supplying a vector of nested shapes in `:parts`. Difference cuts every following part out of the first.

## React to HDR without changing a receiver's color

Pass `:observe-hdr? true` as a frame option. The resulting `:hdr-contacts` maps each radiating fixture to the receiving fixtures and their positive incoming excess. The observation samples actual composed native light after the emitting dimmer and shutter and before whitening, optical spill gain, master and DMX packing. For 0.4 red excess and linear falloff at half the radius, the contact strength is 0.2. Set optical `:spill` to zero to leave the receiver's authored color intact while the logical contact can still start an effect. Explicit blackout, zero master and a closed emitting shutter clear contacts. A pan/tilt-only receiver can participate.

Pass the last committed frame's `:hdr-contacts` to `spatial/advance`. A volume with `:shape :hdr` selects receivers above its `:threshold`. Supply `:source-id` to listen to a particular source, or omit it to accept any. Reading the previous committed frame decouples effects launched by a halo from the render that produced it. Optical gain and whitening follow the [HDR renderer](highlight-spill.md).

## Paint a sculpted volume

`afterglow.spatial.field/sample` takes a resolved volume, a fixture vector or
prepared rig, and the last committed optical observation. It returns two maps
keyed by head ID. `:weights` contains positive native-layer strengths and
`:aims` contains reachable world targets when requested.

For several volumes evaluated against the same output, create
`(afterglow.spatial.field/sampler rig observations)` and call the returned
function with each volume. The first optical query reads the committed
emission once per head. Subsequent queries share light levels and resolved
poses, while retaining each volume's own shape, range and receiver checks.
Position-only volumes leave the optical input unread. Create a fresh sampler
for the next output or a different patch.

```clojure
{:shape :ball :position [2 1 -1] :radius 0.3 :restitution 0.9
 :geometry {:shape :difference
            :parts [{:shape :rounded-box :position [0 0 0]
                     :size [3 1 2] :rounding 0.65}
                    {:shape :sphere :position [0.6 0 0] :radius 0.4}]}
 :selection #{:position :beam}
 :strength 0.85 :falloff {:inner-m 0.2 :outer-m 0.4 :curve :smoothstep}}
```

Supply the body's current simulated position when sampling between throws.
The ball's radius controls wall and body collisions. Its attached geometry
controls the selection, including multiple passages through a cut-out in one
physics step. Any primitive or compound can take a positive XYZ `:scale`
followed by a world `:translation`. Stretch uses the shape position, centre of
its finite bounds or world origin as pivot, in that order. Rounding runs from
sharp corners at zero to the largest radius that fits the shortest side at one.
The same CLJC geometry is usable by Studio.

Distance is negative inside a primitive. The inner and outer distances set the
widths over which strength reaches full and zero. Both default to zero for a
hard edge. Nonuniform stretching scales distance by the shortest axis ratio.
This preserves exact membership and makes the world-space feather conservative
around anisotropically stretched and Boolean shapes.

The caller passes the resulting map as `:target-weights` on a native group.
Each member effect runs once. The compositor applies group strength once at each
head over the existing native backdrop. A head outside the field keeps that
backdrop. Supply `:beam` to include a lit cone or `:aimable` to include a
reachable mover. Alpha uses the strongest qualifying contribution. The previous
frame supplies emitted RGB, pose, fog attenuation and known receiver planes.
[Optical selection and probe limits](spatial-beam-selection.md)

Translated and stretched spheres can calculate distance directly from the three
world coordinates. The calculation retains the inverse scale and subtraction
order of the local sphere, including hard-edge membership at the boundary and
the minimum-axis rule for feathering. Compound shapes still transform their
children through their prepared geometry.

A paired replay on 20,000 RGBW pixels and 64 moving heads placed four moving
beam-aware fields in a room with finite receivers. Each revision ran 5 warmup
frames and 9 measured frames, in alternating order. The median allocation per
complete frame fell from 240.95 MB to 114.52 MB, summed coordinator/worker CPU
from 347.78 to 255.04 ms, and wall time from 547.56 to 396.69 ms. Each frame's
model, intents, selected previews and ArtDMX bytes agreed. The p95 wall times
were 758 and 1,810 ms respectively on this shared machine. All 18 measured
frames exceeded 25 ms. This profile uses Tolglow `2a6b8ce`, Afterglow
`742d17b`, a 768 MiB heap and two effect workers with in-memory output.

The sphere sampler prepares its radius, fade widths and response curve once
per volume sample. For floating-point widths it can reuse the same unboxed
response when evaluating fixture positions and when finding the strongest
point reached by a beam. Sampling a fixture position keeps the nested `hypot`
calculation used by the shape’s signed distance. Translated and scaled spheres
retain their local-coordinate distance. Decimal or fractional widths and large
integral world coordinates preserve the original arithmetic at the boundary.
