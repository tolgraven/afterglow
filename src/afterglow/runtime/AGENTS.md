# Declarative runtime

`engine/advance` is the pure coordinator for the new control model. The legacy
`afterglow.show` scheduler remains separate. Do not claim legacy parity from tests
of this runtime alone.

- Preserve captured definitions, stable instance identity, current parameter
  values, explicit logical time and deterministic priority/launch ordering.
- `:revision` belongs to accepted commands. Rendering advances `:frame-number`;
  consumers compare epoch, revision and frame number together.
- Reload defaults to `:pinned`. The explicit `:preserve-state` and `:restart`
  policies validate retained parameters against new schemas. Launch/release
  durations stay fixed until relaunch. Failed reloads do not publish a frame.
- Duration expiry starts release at its exact timestamp. The compiler owns the
  envelope during its declared release period; expired instances contribute
  nothing at or beyond the release deadline. A step may finish earlier.
- `executor` is an explicit mutable boundary. Requiring it starts no threads.
  Bound worker count, in-flight jobs and elapsed work; cancel unfinished futures
  and close pools. Never add global executor/cache/time/RNG ownership to `engine`.
- Keep tests under `test/afterglow/runtime`. Cover real command/lifecycle paths,
  parallel equivalence, failures, deadlines, cleanup and hot reload. Cross-repo
  compiler/renderer tests belong in tolglow's integration lane.
- Kernel/engine output now has ordered `:contributions` assignment/batch blocks.
  Effect contexts keep vector `:assignments`; append-contributions flushes that
  tail before adding blocks. Aggregate :assignments is nil if batches exist, so
  consumers must resolve the complete stream instead of silently dropping data.
- Typed result arrays are exclusively owned until evaluation returns and then
  read-only. They are output payloads, not mutable state shared between effects.
  Preserve mixed block order under worker completion reversal and final frames.
