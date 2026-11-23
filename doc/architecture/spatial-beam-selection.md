# Beam and moving-head selection in a volume

`afterglow.spatial.beam/contribution` tests one fixture against a weighted
volume in world metres. It returns nil when no sampled point qualifies. Its
result carries the strongest sampled weight and, when a moving head can aim
at a point in the volume, the suggested world-space `:aim`.

```clojure
(require '[afterglow.spatial.beam :as beam])

(def optical-options
  (beam/prepare-options {:selection #{:beam :aimable}
                         :range-m 35 :extinction-per-m 0.08
                         :min-transmission 0.03 :intensity-threshold 0.02
                         :surfaces [{:id :back-wall :point [0 0 15] :normal [0 0 -1]}]}))

(beam/contribution fixture current-fixture-values volume
                   {:weight-at sample-volume :bounds world-aabb :center world-center}
                   optical-options)
```

Pass a rich or projected compact fixture output from the same frame. A beam
uses the strongest component of its emitted RGB, including rendered dimmer
and blackout. A closed shutter reported as `:shutter-open? false` cuts off the
beam. The committed pose or physical pan and tilt determine the direction.
A fixed light can supply a world `:direction` or use its rotated local +Z
axis. Zoom, full included beam angle and lens radius use the fixture's optics
definition. Each sample traces a separate ray through the lens. A finite wall
can block part of a beam while another part passes beside it. Points on the
wall itself can receive light.

Transmission is `exp(-extinction-per-m × path-length-m)`. For a calibrated
fog model pass the current density times the fluid's extinction coefficient.
By default the optical distance limit is 100 m, the minimum transmission is
0.01, and the intensity threshold is zero. Beam weight is the sampled volume
weight times transmission times emitted level. Aimability uses potential
full output and the same range and occlusion tests. It asks the physical
renderer to check pan/tilt channels, calibration, mount and reachable travel
before suggesting a point. It can therefore select a head while it is dark.
With both modes enabled the higher of the two weights wins.

The caller supplies a pure function returning nil or a weight from zero
through one. Its optional axis-aligned bounds include the full weighted
region, including any feather. The field can also supply up to 64
`:witnesses`. A world xyz point seeds a component. A map
`{:center [x y z] :radius r}` additionally tests a spherical component against
the finite beam. Positions and radii refer to the resolved world frame, so
translated, scaled and attached shapes can use the same query. For nonuniform
scaling, a conservative inscribed sphere supplies possible interior points.
Every witness still passes through the full volume weight function, including
subtractions and falloff. Standalone callers with simple untranslated shapes
can omit the witnesses. The query looks at up to 128 authored nodes for seeds.

For a sphere, projection onto the finite lens disk and sloping side produces
contact candidates even when the sphere centre falls outside the cone. The
end of each diverging ray depends on its origin on the physical lens. Spheres
near this range limit also test the curved end cap. Its calculation brackets
stationary distances in eight angular intervals with up to 45 refinement steps
per bracket. A sphere adds its centre, a possible optical contact and, for
aimability across the range limit, a point on its near side.

Bounds and range checks reject distant boxes before sampling. Bounded volumes
also have up to 37 general probes at the centre, near face, beam axis and edge,
and on a 3×3×3 grid. Convex polyhedra without bounds clip rays against each
half-space. The central ray and eight lens-rim rays each contribute up to
three points. Aimability adds six world-axis rays, for up to 46 general probes
including a supplied centre. Other unbounded shapes use probes along the
current axis and toward the supplied centre.

General CSG and weighted fields are sampled. Components beyond the witness
budget, thin intersections between shapes, shadows covering some witnesses,
and arbitrarily narrow weighted regions can still be missed. Brightness is
an emitted-level and transmission estimate. Each eligible point costs up to
one scan of the receiver surfaces per mode. Prepare the options once per set
of surfaces and current fog parameters and share them across fixture queries.
The queries read captured data and leave DMX output untouched.

A CPU-only check scanned a 100×100 array of fixed lights one metre apart at
z = −10 m. All faced +Z with a 20° full beam and 0.1 m lens radius. A 1 m
box centred at [0, 0, 5.5] and a 20 m range selected 45 lit fixtures. On a
shared AMD EPYC 9V74 and OpenJDK 21, 40 scans after 20 warmups took a median
10.1 ms of caller CPU time with red at 0.8 and 1.4 ms with all emitters dark.
This measures one volume query without surfaces, output or transport.
Additional active queries share the show tick’s 25 ms budget.

A second run on the same rig compared fixed probes with component witnesses.
Sixteen spheres of radius 0.25 m formed a 4×4 grid at z = 5.5 m, spaced 1 m
apart and centred on the origin in x and y. The fixed probes selected 16
fixtures. Sphere contacts selected 77, matching a separate calculation of
each sphere's signed distance to the conical side. For this scene every
sphere was ahead of the lens and within optical range. Median caller CPU time
for the union was 11.32 → 10.91 ms, with p95 of 15.62 → 18.80 ms. The single
box retained 45 fixtures and took 12.46 → 6.92 ms at the median. Each run used
40 warmups and 55 timed scans. A fully weighted, unattenuated sample now lets
the scan finish that head immediately.
