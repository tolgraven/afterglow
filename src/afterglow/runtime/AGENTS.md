# Declarative runtime

`engine/advance` is the pure coordinator for the new control model. The legacy
`afterglow.show` scheduler remains separate. Do not claim legacy parity from tests
of this runtime alone.

- Preserve captured definitions, stable instance identity, current parameter
  values, explicit logical time and deterministic priority/launch ordering.
- `:revision` belongs to accepted commands. Rendering advances `:frame-number`;
  consumers compare epoch, revision and frame number together.
- Reload defaults to `:pinned`. The explicit `:preserve-state`, `:restart` and
  `:migrate` policies validate retained parameters against new schemas. `:migrate`
  runs the pure state migration attached to the new compiled step once, at the
  takeover frame; a failing migration is a `:migrate` reload fault. Launch/release
  durations stay fixed until relaunch. Recoverable candidate failures retain the
  captured last-good revision; valid newer versions or :instance/retry recover.
  A faulted current revision contributes nothing and retains its last valid state.
  Never repeatedly execute a quarantined revision on every frame.
- A host whose frame inputs already follow a candidate (modulated parameters,
  modulated layer priority) supplies `::engine/reload-fallback`. That frame reads
  one input set throughout: candidates are attempted first, and one rejection
  evaluates every captured revision on the fallback inputs and leaves the accepted
  candidates pending, without a fault, for the next frame. Keep the fallback a
  plain frame-input map and report the set read in `:reload-inputs`. Without it,
  candidates keep their independent per-instance fallback.
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
- Keep per-effect faults separate from global model/executor failures. Cancellation,
  interruption and VM failures must not become user-code faults. Portable events
  have bounded history; source traces stop at runtime scheduling boundaries so
  serial/parallel replay agree. Logging belongs to an asynchronous host owner.
- Renderer attribution may reject one completed effect evaluation. Roll back its
  attempted state/intents and discard its blocks, then resolve healthy results
  without running their code twice. Never retain typed results in saved state or
  silently hold stale emission. See doc/architecture/effect-fault-isolation.md.
  The one exception is a rejected candidate in a frame that supplied
  `::engine/reload-fallback`: that frame is evaluated once more on the fallback
  inputs, so its last-good revisions render with the inputs computed for them.

Use `afterglow.runtime.reuse` for declared pure calculations. Fold only captured
inputs and immutable bindings into their results. Preserve per-frame intent
delivery and distinct caller-owned output arrays, unless the binding declares
`:shared-outputs? true` and every reader keeps its arrays read-only. See
[the declaration and cache contract](../../../doc/architecture/pure-effect-reuse.md).

Only certify stateless, continuous-output samplers for [predictive effect
keyframes](../../../doc/architecture/effect-keyframes.md). Test future clock reads
and resulting native state through `engine/advance`, including parallel workers,
faults on a forecast and recovery on the real timeline. Keep read-only endpoint
arrays under frame ownership. Persistence goes through
`afterglow.runtime.keyframes.storage`.
