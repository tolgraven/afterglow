# Development tooling

Read ../doc/architecture/README.md and the companion tolglow docs/testing.md.
Run pure or legacy tests explicitly; never skip failing namespace loads. Read,
do not eval, project.clj to derive legacy dependencies. Explain the Beat Link
release override and keep the generator copy in Tolglow synchronized.
Benchmarks must use local buffers/capture sinks, record inputs/environment,
validate outputs and distinguish measured stages from end-to-end rendering.
