# Beam footprints and moving-head edge tracking

A circular lens projects a circle on a perpendicular wall and an ellipse on an
oblique wall. The centre of that ellipse moves away from the centre-ray hit as
the beam becomes more oblique. Use the full ellipse when arranging neighboring
spots. Every coordinate and radius in the API is in world metres.

```clojure
(require '[afterglow.render.frame :as frame]
         '[afterglow.render.optics :as optics])

(def floor {:id :floor :point [0 0 0] :normal [0 1 0]
            :u-axis [1 0 0] :size [12 8]})
(def beam {:position [0 4 -1] :direction [0.15 -1 0.4]
           :beam-angle 24 :lens-radius-m 0.08})

(def spot (optics/nearest-footprint beam [floor]))
(optics/edge-aim spot {:position [2 4 -1] :beam-angle 16 :lens-radius-m 0.06}
                 floor [1 0 0])
```

Supply **full included degrees** for `:beam-angle`. A zoomable fixture can give
`:zoom-range-deg [narrow wide]`; `fixture-beam` interpolates those angles using
the committed zoom. An explicit fixed angle remains constant. The preview
defaults are 12° at zero zoom, 46° at full zoom, and 0.119 m lens radius.
For a standalone beam map, omitting the lens radius specifies a point aperture.
For a patched fixture, reconstruct the direction from its actual normalized
channels and mounting calibration:

```clojure
(optics/fixture-beam fixture
  (assoc committed-values :pose (frame/fixture-pose fixture committed-values)))
```

## Surface geometry

Receivers are two-sided planes identified by `:id`. The optional rectangle is
centred at `:point`. Its horizontal direction is `:u-axis` projected onto the
surface. The other direction follows from the normal. Omit `:size` for an
infinite plane. The hit reports the normal pointing back towards the emitter.

`:hit` is the centre-ray intersection and `:distance-m` is its distance from
the lens. `:center`, `:major-axis`, `:minor-axis`, `:major-radius-m` and
`:minor-radius-m` describe the full ellipse. A finite aperture widens the cone
from the lens face. `:clipped?` means some of the ellipse lies beyond the
rectangle. The centre ray determines which surface owns the footprint. A nearer
grazing hit occludes farther receivers. Rays pointing away or missing the
rectangle, unbounded conic sections, and a receiver cutting the aperture
produce no footprint. This model describes the primary planar receiver; rim
spill onto neighboring surfaces and reflections from curved objects require
scene geometry.

## Tracking in a running frame

Pass an ordered vector of constraints in the normal render options, alongside
master and the last accepted movement history. Each link names a leader, a
follower, a receiver, and the direction on the receiver where the follower
should touch the leader.

```clojure
{:edge-tracking [{:leader :left :follower :middle :surface floor :along [1 0 0]}
                 {:leader :middle :follower :right :surface floor :along [1 0 0]}]}
```

The renderer blends all ordinary assignments, zoom, directions and aims first.
It resolves the leader's calibrated pan and tilt, including mechanical stops,
then finds the boundary point furthest along the requested direction. It aims
the follower so both illuminated ellipses meet at that point with a common
tangent line, each on its own side. A valid solution accounts for both lens
radii, different beam angles, different mounting positions and oblique
incidence. The calculation repeats every frame. A chain on one surface using
the same `:along` direction produces disjoint neighboring footprints. Put links
in dependency order and place each follower once.

On a receiver used by several links, independently aimed leaders reserve space
first. Each successful follower then reserves space in link order on the
receiver where it was placed and on shared receivers where it leads another
link. A common tangent is allowed. A follower whose footprint overlaps an
existing reservation yields and darkens, along with followers that depend on it.

A link is reported under the published frame's `:edge-tracking` vector with
`:aim` and `:contact` on success. A missed receiver, clipped ellipse, unavailable
fixture, unreachable calibrated aim, overlap or upstream failure gives a `:reason` and
sets the affected follower's dimmer to zero for that frame. Tracking resumes
when the next frame has a solution. Original effect definitions, user parameters,
and channel patching stay intact. The geometry uses nominal commands. Physical
DMX quantization, fixture backlash, motor lag and a soft optical beam edge affect
where the visible boundary falls in a venue.

`resolve-frame`, `resolve-contributions`, `resolve-batches` and the normal
CPU/native compute owner all accept this option. The constrained heads use the
float64 reference solver, while unrelated eligible heads can use native GPU
rotation. Run `lein test afterglow.render.optics-test afterglow.render.edge-tracking-test`
to exercise the geometry, packed multi-universe DMX and live tracking.
