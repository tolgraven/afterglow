# Calibrated moving-head GPU solver

Afterglow owns the world-space target convention, inverse mounting rotations, fixture calibration, wrap selection and GPU readback. `afterglow.render.frame/resolve-frame` is the CPU reference. Physical frame packing defaults to CPU rotation. The optional WebGL2 solver produces numeric axes for consumers that can tolerate float32 precision.

A host reads the packaged vertex source with `(afterglow.render.gpu/source :moving-head-vertex)` and serves the module at the `:moving-head-solver` resource URL. Pass fixtures in stable patch order with the same `position`, `rotation-deg` and pan/tilt `calibration` used by the CPU renderer. The solver uploads the mount data once per rig.

```javascript
import { createMovingHeadSolver } from './mover-aim.mjs';

const solver = createMovingHeadSolver(fixtures, vertexSource);
try {
  const first = await solver.solve(worldTargets);
  const next = await solver.solve(nextWorldTargets, first.axes);
  // Four floats per head: normalized pan, tilt, reachability and validity.
} finally {
  solver.dispose();
}
```

Each input can be a world target `[x, y, z]`, an assignment with `{aim: [x, y, z]}`, or an assignment with `{direction: [dx, dy, dz]}`. Mix input types within one draw. As in `frame/resolve-frame`, an explicit aim takes precedence when both attributes are present. Direction vectors use the mount rotation and calibration directly and can have any finite, nonzero length representable by the solver.

Supply the axes of the last frame the consumer accepted. Keep them paired with the same patch order. A fresh solve without history chooses the legal pan nearest neutral. An out-of-range angle clamps and reports reachability separately. A zero-distance target rejects the frame. Each result owns its array, and one frame may be in flight per solver. Use a dedicated canvas. Rebuild the solver after rig changes or context loss.

The whole-show integration benchmark in Tolglow compares every returned axis and packed DMX slot against Afterglow. Software WebGL tests found occasional one-unit differences in a 16-bit channel word. Hardware GPU acceleration and physical-output equivalence remain unverified. [Measurements and corpus](https://github.com/tolgraven/tolglow/blob/master/docs/moving-head-shader.md)

## Native JVM show hosts

`afterglow.render.native-gpu` executes the same calibrated vertex shader in a
private JOGL desktop OpenGL 3.3+ context. A host can solve targets while Studio
is closed. Start a REPL with `lein with-profile +native-gpu repl` to include
the platform libraries. Ordinary Afterglow startup acquires no graphics device.
On a Linux machine without a desktop, run the JVM under `xvfb-run -a` with Mesa
installed for software execution. On macOS, JOGL uses the system OpenGL context.

```clojure
(require '[afterglow.render.frame :as frame]
         '[afterglow.render.native-gpu :as native])

(def patch (frame/compile-patch
            [{:id :spot :position [0 3 0] :address 1 :universe 0
              :channels {:pan [1 2] :tilt [3 4]}}]))

(with-open [solver (native/open! patch)]
  (native/solve! solver {:spot [-2 0 4]}
                 {:previous-values {:spot {:pan 0.75}}}))
```

Create the solver once for a compiled patch. Each request includes a world-space
aim or direction for every pan/tilt fixture, for example
`{:spot {:direction [0 -1 0]} :wash {:aim [-2 0 4]}}`. The short vector
form specifies an aim. An explicit `:aim` takes precedence over `:direction`
on the same fixture. Other fixtures in the patch take no GPU slots.
The caller can supply the last accepted CPU frame’s `:values` as
`:previous-values`, or its `:compact` as `:previous-compact`. Target IDs
remain stable across patch reordering. The result is an immutable map by ID
with `:pan`, `:tilt` and `:aim-reachable?`. Calls retain no implicit history.

`solve!` is synchronous. Run it on an owned worker if other show work must
continue during readback. Concurrent submissions report `::native/busy`.
A fence bounds the wait for a submitted draw. Set `:timeout-ms` on `open!`
to control that wait, allowing separately for compilation, driver calls and
CPU work. A GPU failure retires the solver. Reopen it to try again. Invalid
input and zero-distance targets reject that frame and leave the solver usable.
Closing the owner releases the context and its buffers.

Run `lein with-profile +native-gpu test afterglow.render.native-gpu-test` to
exercise the actual shader against the CPU fixture model. The 64-head scene has
differently mounted fixtures and carries committed CPU history through twelve
successive frames. CI exercised native execution and readback on Mesa llvmpipe
OpenGL 4.5 on Ubuntu and Apple Software Renderer OpenGL 4.1 on macOS 15.
Performance on physical Mac GPUs and byte-equivalence for DMX remain unverified.

The [JVM lighting-expression runner](native-expression-shaders.md) uses the
same context, fence and readback ownership for named color, focus and other fields.

`afterglow.render.frame/fixture-pose` reconstructs the commanded beam from the
normalized pan and tilt in a committed frame. It accepts either rich target
values or one projected compact target. The result includes the unwrapped
mechanical angles and the world-space beam direction after fixture mounting.
For example, a wide-pan head may reach a requested −170° bearing by turning
to +190°. A target beyond the tilt range stops at the calibrated end of travel.
Use the pose for visualisation and the original aim for an editing handle.
This projection describes channel commands. Optical calibration, motor lag
and fixture feedback require measurements from the physical fixture.


## Render movement after effect blending

A show that opts into native rotation owns one `afterglow.render.gpu.movement`
instance. Supply the same ordered contribution stream and compiled patch that
the CPU renderer uses. Reuse the compiled patch across frames. If effects
produce deferred numeric fields, first materialize them into contribution
blocks. Feed previous values only from the last accepted physical frame.

```clojure
(require '[afterglow.render.gpu.movement :as movement])

(with-open [owner (movement/open! {:budget-ms 25 :timeout-ms 1000})]
  (movement/resolve-contributions!
    owner patch
    [{:kind :assignments :source :sweep
      :assignments [{:target-id :spot :attribute :aim :value [-2 0 4]}]}]
    {:include-values? false :compact-values? true
     :previous-values {:spot {:pan 0.75}}}))
```

Blend order, opacity, aim precedence and error attribution use the CPU frame
reducer. The movement shader receives the resulting targets, solves mounting
rotations, calibration and wrap from the captured pans, then returns the axes
to the same physical DMX packer. Direct pan/tilt and zero-opacity assignments
retain the CPU renderer’s behavior. The output adds a `:movement` map with
`:backend`, `:gpu-heads` and `:cpu-heads`. If a small float32 margin around a native axis
straddles a physical rounding boundary, the reference solver resolves that
head. The margin depends on the driver, as the next section describes.
The check uses the packed channel format, including 8-bit, fine, and
inverted channels. Exact coordinates, unstable float32 subtraction, and
ambiguous wrap, clamp or pole decisions also go through the reference solver.
This guard applies to the movement solve. When an effect supplies a target
from native float32 expression evaluation, it still carries that upstream
precision.

### Rounding guard by renderer

The guard only keeps the packed bytes equal to the reference while the
driver's float32 axis error is smaller than the margin. That error differs
between drivers, so `native-gpu/open!` reads `GL_RENDERER` and takes the
margin from the table `afterglow.render.native-gpu/rounding-margins`. Rows are
tried in order and must match the whole renderer string. One ulp is the
float32 step at 1.0, about 1.19e-7 of a normalized axis.

| Row | `GL_RENDERER` | Margin | Largest scaled axis error measured |
| --- | --- | ---: | --- |
| `:apple-m-series` | `Apple M<n>`, optionally ` Pro`, ` Max` or ` Ultra` | 8 ulp, 9.54e-7 | 1.83e-7 on an M4 Pro with `4.1 Metal - 91.7`, 1.5 million samples |
| `:mesa-llvmpipe` | `llvmpipe (LLVM …)` | 128 ulp, 1.53e-5 | 1.89e-6 unscaled on Mesa 26.0.8 with LLVM 21.1.8, 1,344 samples |
| `:unqualified` | anything else | 256 ulp, 3.05e-5 | none |

A solver reports its row as `:rounding {:row … :ulps … :margin …}` beside
`:renderer` and `:version` under `:resources`. A movement owner returns the
same three keys from `(movement/renderer owner)` once a frame has opened its
context. The `:movement` map of a frame is unchanged.

The margin decides how much work stays native. A 16-bit axis has a code step of
1/65535, about 1.53e-5. The Apple window of twice 8 ulp covers an eighth of
that step, so about three quarters of 16-bit heads stay native. The llvmpipe
and unqualified windows are two and four steps wide. Under those rows every
16-bit axis resolves on the reference, and a frame with only 16-bit heads
reports `:backend :cpu` with `:reason :ambiguous`. The native draw still runs.
An 8-bit axis has a step of 1/255, so it stays native under every row for all
but about 1% (llvmpipe) or 2% (unqualified) of its range.

The llvmpipe margin is eight times an error that was measured on only 1,344
samples from one seed. Four times that error is already half a 16-bit step,
so no margin with that headroom keeps 16-bit axes native on llvmpipe. The
wider value costs nothing more for those axes and little for 8-bit axes.
llvmpipe runs on the CPU, so the native path there is a test lane and not a
faster backend. The Apple row matches only the exact chip names of Apple's own
driver. Apple Software Renderer, a chip name with any other suffix, other
vendors' GPUs and translation layers are unqualified.

#### Pan error near the pan axis

The pan error has no fixed bound. The shader rotates the aim into the fixture
frame in float32 and takes the pan angle from the two components that lie
across the pan axis. As the beam nears that axis those components shrink, and
the same rounding error becomes a larger angle. The error grows with the
secant of the requested elevation. Over 256,000 heads on the M4 Pro the
largest unguarded pan error was 1.2e-7 beyond 30° from the pan axis and
1.15e-6 within 0.3° of it. That is 1.2 times the Apple margin.

`native-gpu/pan-margin` therefore widens the pan margin in proportion once the
secant exceeds 8, about 7.2° from the pan axis. On Apple hardware a 16-bit pan
within about 0.9° of the axis always resolves on the reference. The tilt
margin is the row margin everywhere. The errors in the table are scaled the
same way: the tilt error, and the pan error divided by the factor that widens
its margin. With that scaling the M4 Pro maximum was 1.55e-7, 1.70e-7 and
1.83e-7 in three sweeps of 512,000 samples, against 1.5e-7 over 51,200. All
12,000 frames packed the reference bytes. The scaling moved 2 of 1,280 heads
in the 32-head sweep to the reference (1,026 stay native).

The table is static. A measurement at `open!` would be a small sample of
targets that the show may never use, and its largest raw error depends on how
near one sample came to a pan axis. Each host would get a different margin and
a different share of native heads. A row is therefore a reviewed measurement.
To qualify another driver, run the native test lane on it. The test
`a-seeded-movement-sweep-packs-the-reference-bytes` prints one
`Movement sweep` line per rig with the renderer, the matched row, the largest
scaled and raw axis errors and the number of heads that stayed native. It
fails if the scaled error reaches the row's margin or any frame differs from
the reference bytes. Add a row only with a margin of at least four times the
largest scaled error over at least 51,200 samples, and record the driver
version here.

The rows were measured with pan ranges of 270° and 540° and tilt ranges of
100° and about 306°. A narrower calibrated range turns the same angular error
into a larger normalized error. A 60° pan range with a 40° tilt range reached
a scaled error of 4.6e-7 on the M4 Pro, about half the Apple margin. Narrower
ranges have not been measured.

The host can pass `:deadline-nanos` from its frame clock (`System/nanoTime`).
The GPU stage honors the earlier of that deadline and the owner's frame budget.
A timeout, busy owner, missing native library or driver failure sends this
call's captured targets to the CPU. Its `:movement :reason` identifies the
fallback. CPU packing and transport still take their normal time. One worker
owns a single mounted rig, with at most one outstanding draw and no backlog of
frames. A late draw can finish but only its original call could consume it.
A changed compiled patch replaces the resident rig. Close and reopen an owner
to retry an unavailable context on the same patch. `(movement/close! owner ms)`
allows a bounded shutdown wait while any native cleanup continues.

The native tests exercise layered aim and opacity, direct axes, exact values,
ID-based compact history across rig changes, coarse/fine DMX across universes,
deadline expiry, and an intentionally delayed draw. Their expectations follow
the active renderer's row: on llvmpipe the 16-bit scenes resolve on the
reference, and 8-bit copies of the boundary, published-frame and sweep scenes
keep native results in the compared bytes. Physical fixture travel
and GPU speed on show hardware still require measurement.
