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
`:backend`, `:gpu-heads` and `:cpu-heads`. Native float32 values can round to an
adjacent 16-bit DMX word. Exact coordinates, unstable float32 subtraction, and
ambiguous wrap, clamp or pole decisions go through the reference solver.

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
deadline expiry, and an intentionally delayed draw. Physical fixture travel
and GPU speed on show hardware still require measurement.
