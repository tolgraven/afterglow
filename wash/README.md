# Spatial wash measurements

The fixture is the registered wash from Tolglow commit c25dc4b377b5c9517619e8988bf1f72187265085. On that revision with the Afterglow revision 84b3821a27099efdb5cb95c69eba442549523b0e on the JVM classpath, run export.clj with the desired output fixture path as its argument. It asks the production Tolglow effect compiler for the normalized expression and selects all 1,023 original rig positions in order.

The CPU benchmark runs each implementation in a fresh JVM with a 256 MiB initial heap, 512 MiB maximum heap, and four visible processors on Linux x86-64 with OpenJDK 21.0.13 and Clojure 1.12.7. The previous Afterglow evaluator is identical between 84b3821a27099efdb5cb95c69eba442549523b0e and 52db646c290fd8f396e788000230bcd220f9f8bc. The candidate is 5fd21129c88bbc12d1b8bc7bba2f12e831ea2738. File names number the order of runs. The benchmark records calling thread CPU, monotonic wall clock and thread allocations around the batch call. Output hashing and exact scalar comparisons run outside that interval.

With the JDK counters available, repeat the candidate measurements from the Afterglow checkout with the downloaded fixture.

```sh
lein with-profile +benchmark run -m afterglow.bench.typed-expression wash.edn report.edn 450 360
```

For the previous version of the evaluator, put its original src/afterglow/render/ir.clj ahead of the candidate src on the classpath and load the same benchmark with the same JVM flags.

The production series uses frame.clj with the original pinned Tolglow and Afterglow sources above, substituting only the typed expression implementation on the candidate runs. It sends completed frames to the original memory sink. Four independent runs each sampled 120 warmup and 240 measured nominal slots, using two effect workers and the original 40 Hz physical scheduler. Several tasks shared the test machine. Tail and deadline counts vary substantially even within a version.

The animation shows the actual linear RGB output at 17 musical positions, beats 0 through 32. Coordinates and all 52,173 channel values were bit-identical between CPU implementations before projection to the image. The binary stream produced by wash-rgb.clj, which contains the count, XYZ coordinates, and float64 RGB samples in network byte order, has SHA-256 e3e49d681fcd35f16ec8f54d9032238404016e423a24181d9a8f656d7c12292d for both revisions.
