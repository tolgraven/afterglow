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
region, including any feather. Bounded probes use the centre, near face,
beam axis and edge, and a 3×3×3 grid. Axis and optical range checks reject
distant boxes before sampling. At most 37 different points are sampled for a
bounded volume. Convex polyhedra without bounds clip rays against every
half-space. The central ray and eight lens-rim rays each contribute up to
three points. Aimability also checks six world-axis rays, for at most 46
samples including a supplied centre. Other unbounded shapes use probes along
the current axis and toward the supplied centre.

Sampling is deterministic. Small disconnected features or a thin grazing
overlap can fall between probes. Brightness is an emitted-level and
transmission estimate. Each eligible probe costs up to one scan of the
configured receiver surfaces per selection mode. Prepare the options once per
set of surfaces and current fog parameters and share them across fixture
queries. The queries read captured data and leave DMX output untouched.

A CPU-only check scanned a 100×100 array of fixed lights one metre apart at
z = −10 m. All faced +Z with a 20° full beam and 0.1 m lens radius. A 1 m
box centred at [0, 0, 5.5] and a 20 m range selected 45 lit fixtures. On a
shared AMD EPYC 9V74 and OpenJDK 21, 40 scans after 20 warmups took a median
10.1 ms of caller CPU time with red at 0.8 and 1.4 ms with all emitters dark.
This measures one volume query without surfaces, output or transport.
Additional active queries share the show tick’s 25 ms budget.
