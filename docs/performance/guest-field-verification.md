# Verifying audience GPU results

When a host admits an audience bridge, pass `:verification :full` to the worker pool. Derive this policy from the bridge's own authenticated role. A participant must never select its own trust level. Full verification recomputes the complete returned slice in the local float64 evaluator. The host checks every returned component with absolute tolerance 1e−5 below unit magnitude and relative tolerance 1e−5 above it. Any nonfinite or mismatched result drops the complete batch, disconnects the failing peer, and invokes local fallback. Accepted physical fields come from the local float64 reference. This also preserves DMX quantization at byte boundaries.

Hosts that deliberately accept statistical verification can instead admit a bridge peer with `:verification :redundant` and a `:subject` string that identifies the independently admitted participant. The two subjects in a pair must differ. Both evaluate the same slice and the host compares every returned float. After both replies arrive, the host chooses four distinct rows with its own secure random source and checks those rows against the CPU. A single peer, two copies of the same subject, or a dispute invokes full local checks. Late or incomplete jobs keep the physical frame on local fallback. An honest peer remains connected when the full reference identifies which witness was wrong.

Correlated float32 errors can produce near-boundary differences in redundant mode. Two colluding participants can supply the same incorrect unsampled row. Full verification covers those cases. A participant ID is a session admission, independent of biological identity; several devices can be under one person's control.

## Measurement

```sh
lein run -m afterglow.bench.guest-verification 2048
```

The retained group calculates three direction components over 2,048 spatial positions, returning 6,144 floats. The microbenchmark creates the input buffers before timing, warms each policy 16 times and then measures 64 runs. On a shared OpenJDK 21 Linux host the full check took 1.53 ms at the median and 35.33 ms at p95. Two witnesses plus four CPU rows took 0.31 ms at the median and 18.74 ms at p95. These numbers cover verification alone. Radio traffic doubles for paired witnesses, and the show still needs enough independently admitted devices and room in the frame deadline.
