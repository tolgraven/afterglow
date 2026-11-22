# Architecture migration

Afterglow owns the rendering path from ordered effect contributions to physical
fixture channels. Tolglow supplies show configuration and authored effects.

* [Beam footprints and live edge tracking](beam-footprints.md)
* [Calibrated moving-head rotation after effect blending](moving-head-shaders.md#render-movement-after-effect-blending)
* [Named fixture field expressions and their GLSL layout](numeric-shader-fields.md)
* [Native execution and GPU readback for fixture fields](native-expression-shaders.md)
* [Physical output and RDM](physical-output.md)
* [Documentation index](../../../tolglow/docs/README.md)
* [Current code survey](../../../tolglow/docs/codebase-survey.md)
* [Functional runtime](../../../tolglow/docs/architecture/functional-runtime.md)
* [Rendering and acceleration](../../../tolglow/docs/architecture/rendering.md)
* [Shared controls and web](../../../tolglow/docs/architecture/control-and-web.md)
* [Work ledger](../../../tolglow/docs/work-items.edn)

These relative links assume both repositories are siblings. If viewing this
repository alone, clone `https://github.com/tolgraven/tolglow` beside it and use
the architecture change there; the documentation may not yet be on its default branch.

This change adds characterization tests and an experimental pure runtime; it
does not replace the live engine or device drivers. The old `IEffect` API, show
atoms and render loop remain. The new kernel requires callers to supply pure
steps and any worker mapper, and returns data without publishing a frame.

Run `lein test` from the project root. CI runs on Java 17, 21 and 25.
`lein test-pure` and `lein test-parity` select the namespaces in
`dev/afterglow/test_runner.clj`. The same `project.clj` supplies both classpaths.
`bin/bench` uses the benchmark profile and records the current Git revision.

Run `lein run` to start Afterglow. Packaging with `npm ci` and `lein uberjar`
builds the embedded Antora guide, API docs and Git version resources.
