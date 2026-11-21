# Calibrated moving-head GPU solver

Afterglow owns the world-space target convention, inverse mounting rotations, fixture calibration, wrap selection and GPU readback. `afterglow.render.frame/resolve-frame` is the CPU reference and the physical-output backend. The optional WebGL2 solver produces numeric axes for consumers that can tolerate float32 precision.

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
aim for every pan/tilt fixture. Other fixtures in the patch take no GPU slots.
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
