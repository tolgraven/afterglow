# Afterglow typed keyframe validation

Draft [#111](https://github.com/tolgraven/afterglow/pull/111) still addresses code in released `4f65f06c`. Commit `3d668112` already replaced iteration over target IDs with direct vector reduction. Released `valid-column?` still sends three boxed doubles to a generic three-argument comparison for every finite field component in the compiled code. The local backport `6672aa21` is the draft's one-file change, with two primitive binary comparisons. Both bounds are inclusive and the finite check still comes first. The typed checks run when predictive samples are built, when saved predictive windows are restored, and when dependency-driven output is recalculated. Interpolated frames reuse validated endpoints. Assignment rows continue through their existing numeric path.

## Allocation

The [measurement harness](measure.clj) invokes `values/validate-blocks!` on preconstructed typed batches and checks the returned blocks retain identity. It measures calling-thread allocation with `ThreadMXBean` on Java `21.0.13`, Clojure `1.12.7`, two reported CPUs and a 512 MiB heap. Each JVM runs seven measured windows after 200 warm-up calls on large batches and 3,000 on the mover batch. Each measured window has 40 calls on large batches and 4,000 on the mover batch. The default-tier trial order was `A1 B1 B2 A2`, where `A` is released source and `B` is the local candidate. A second trial used `-XX:TieredStopAtLevel=1` to hold off C2 optimization and isolate the allocation from the generic comparison.

| Validation input | Components per call | Default-tier released A1 / A2 | Default-tier candidate B1 / B2 | C1 released / candidate |
| --- | ---: | ---: | ---: | ---: |
| Normalized dimmer on 20,064 fixtures | 20,064 | 1,606,592 / 1,472 B | 1,472 / 1,440 B | 2,569,664 / 1,472 B |
| HDR RGBW plus dimmer on 20,064 fixtures | 100,320 | 8,028,184 / 2,584 B | 2,584 / 2,552 B | 12,843,544 / 2,584 B |
| Aim, focus and beat ratio on 64 movers | 320 | 27,901 / 2,288 B | 2,360 / 2,288 B | 43,352 / 2,392 B |

Values are median allocated bytes per validation invocation rounded to the nearest byte where needed. Both C1 pairs give the same medians and remove exactly 128 B per field component. With default tiering, released A2 reached candidate-like allocation, while released A1 allocated about 80 B more per component throughout its measurement. The candidate stayed low in both default-tier runs. [Released bytecode](A-bytecode.txt) shows three `Double.valueOf` and one generic `IFn.invoke` per finite value. [Candidate bytecode](B-bytecode.txt) shows two calls to primitive `Numbers.lte(DD)`. The observed default-tier variation is consistent with C2 eliminating the original allocations in one process. The shared host and JVM tier variance make the raw timing windows unsuitable for inferring live render or publication speed.

## Precision and replay

Each measurement JVM passed 17,629 checks against the expected field bounds. The cases cover signed zero, the adjacent doubles on each side of normalized zero and one, finite extremes, NaN payloads, infinities, seeded double bit patterns, HDR emission and non-emission fields, and every component of vec3 fields. Accepted values retained their raw bits. The focused keyframe and frame tests passed 86 tests and 1,257 assertions. The pure runner passed 747 tests and 11,503 assertions.

The [replay harness](replay.clj) feeds the existing in-memory [reactive retargeting capture](../afterglow-reactive-effect-settling-534/trace.csv) through a 64-fixture patch. It exercises typed dimmer and beat-ratio transitions alongside an authored predictive RGB, focus and zoom effect. It captures all pre-composition field components as raw double bits and compares rich and compact renderer DMX buffers on each frame. The source capture supplies reactive changes, held values and the original first-fixture dimmer and ratio oracle. DMX bytes are captured in memory.

All 369 frames matched for 188,928 packed DMX bytes and 165,312 raw double components. The rich and compact renderer buffers matched on every frame. Both runs validated 181,824 components across 3 reactive calculations and 567 predictive samples. The [capture digests](replay-sha256.txt) cover both runs. The [still](keyframe-replay.png) and [5.93-second replay](keyframe-replay.mp4) plot the first 89 frames and show the actual packed color and dimmer values for the 64 fixtures. The preview applies a display gamma to the resulting RGB.

## Reproduce

Run `./run.sh measure` for the default-tier allocation probe and `KEYFRAME_JVM_MODE=c1 KEYFRAME_TRIAL_PREFIX=c1- ./run.sh measure` for the C1 control. `./run.sh bytecode` records the per-method JVM calls. `./run.sh replay` runs the released-source overlay and candidate against the same captured input and compares the trace, packed DMX and native field files. Run `MPLCONFIGDIR=/tmp/afterglow-387-mpl python render_replay.py` to recreate the still and video from the matching captures.
