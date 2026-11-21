# CI

The architecture test workflow is separate from existing release/doc packaging.
Do not claim release builds pass because plugin-free test lanes pass. Preserve
nonzero failures and Java 17/21 coverage. Coordinate test manifest or dependency
changes with the companion Tolglow CI pin and legacy dependency reader.
