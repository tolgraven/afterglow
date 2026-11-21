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

Each input can be a world target `[x, y, z]`, an assignment with `{aim: [x, y, z]}`, or an assignment with `{direction: [dx, dy, dz]}`. Mix input types within one draw. As in `frame/resolve-frame`, an explicit aim takes precedence when both attributes are present. Direction vectors use the mount rotation and calibration directly and can have any finite, nonzero length representable by the solver.

Supply the axes of the last frame the consumer accepted. Keep them paired with the same patch order. A fresh solve without history chooses the legal pan nearest neutral. An out-of-range angle clamps and reports reachability separately. A zero-distance target rejects the frame. Each result owns its array, and one frame may be in flight per solver. Use a dedicated canvas. Rebuild the solver after rig changes or context loss.

The whole-show integration benchmark in Tolglow compares every returned axis and packed DMX slot against Afterglow. Software WebGL tests found occasional one-unit differences in a 16-bit channel word. Hardware GPU acceleration and physical-output equivalence remain unverified. [Measurements and corpus](https://github.com/tolgraven/tolglow/blob/master/docs/moving-head-shader.md)
