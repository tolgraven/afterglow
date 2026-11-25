# Effect failure isolation

`afterglow.runtime.engine/advance` isolates recoverable failures per instance.
The lower-level `runtime/render-frame` remains a strict kernel; the coordinator
owns recovery policy. Both use the same result validation and ordered merger.

## Failure and recovery

Compilation, evaluation or result failure preserves the last committed `:state`
and discards the attempt's output, intents and completion flag. Healthy instances
continue. The failed current version stores `:fault` and is suppressed until an
explicit retry or a newer definition under the selected reload policy.

For `:preserve-state`, `:restart` and `:migrate`, a bad candidate stores `:reload-fault` while
the captured last-good definition is retained. Preparation/compile/evaluation
failure evaluates that captured version in the same frame. Separate fields
preserve suppression if both candidate and captured versions fail. Pinned cues
remain pinned. Timed/releasing faulted instances still reach their normal expiry;
pause retains its private-clock semantics.

## State migration on reload

`:migrate` adopts a newer definition like `:preserve-state` (retained time,
system controls and compatible parameters), then transforms the instance's
private state for the new version. The shell's compiler attaches a pure function
to the new definition's compiled step with `engine/with-state-migration`:

```clojure
(engine/with-state-migration step
  (fn [old-state old-version new-version context] new-state))
```

`context` is portable data: instance/cue/effect IDs, both captured definitions,
the retained parameters, the frame (`:show-id :epoch :revision :number :time-ms`)
and the instance's private clock. The engine calls the function once, on the
frame where the candidate first takes over, immediately before that step first
runs, on the same worker that evaluates the instance. `advance` is pure, so the
call is outside any `swap!` or CAS retry; the function must not perform IO, read
clocks or own RNG. Definitions stay data: the migration lives on the compiled
step, never in the registry. `with-state-migration` returns a direct unary
step (no variadic wrapper) that keeps the step's other metadata. Paused
instances defer the reload and its migration.

The result must be plain EDN: nil, booleans, strings, characters, keywords,
symbols, UUIDs, instants, finite numbers and maps, vectors, sets or lists of
those. Functions, records, host or mutable objects (atoms, arrays, Java
collections), lazy sequences and NaN/infinite floats are rejected.

A missing migration, a non-EDN result, or a recoverable exception from the
function is a `:reload-fault` with `:stage :migrate`, `:effect-version` (the
rejected version) and `:from-version`. Its first cause carries
`{:type :afterglow.runtime.engine/state-migration-failed :path [:state-migration]}`
and later causes keep the authored `ex-data` location, such as
`{:path [:state-migration :steps 0]}`. The instance evaluates its last good
definition with its last good state in the same frame, exactly as it would had
the new version never been published. Other instances, ordering and output are
unchanged. The quarantined migration is not retried every frame; a newer version
or `:instance/retry` tries again from the last good state. Interruption,
cancellation and VM errors propagate unchanged.

Control validates `:reload-policy` on cue publication and on launch. An explicit
`nil` policy, as found in older documents, means the default `:pinned`.

Every path that advances a model must use a compiler that attaches the same
migrations, or a `:migrate` instance faults there and diverges from live.
`replay/record` and `replay/replay` evaluate with the caller's compiler, so a
recording replays only with that compiler; a compiler without the migration
reports `::replay/mismatch`.

`:instance/retry` is an ordinary idempotent command addressed to the current
instance and epoch. It retries with retained parameters/state/time. A failed
retry reports failure, never a false recovery on the following suppressed frame.

Exceptions, assertions and linkage errors are recoverable. Interruption,
cancellation, ThreadDeath and VirtualMachineError, including wrapped causes,
remain owner/frame failures. Invalid global model/time and missing/duplicate
executor results also fail the entire frame. In-process isolation cannot undo
IO/mutation by code that violates the pure contract or safely kill code that
ignores interruption.

## Renderer attribution

Output blocks carry `:source` with instance/cue/effect/version. Existing renderer
validation and merge passes report `:effect-source` on attributable errors; see
[render provenance](render-error-provenance.md). Global patch/options/history
errors are not attributed to an arbitrary effect.

`engine/reject-output` accepts the evaluated result and attributed error. It
discards only the culprit's attempted state/output/intents and rebuilds ordered
contributions. The host resolves again without reevaluating healthy effects.
Repeated/unknown sources reject, bounding recovery to one rejection per instance.
A candidate rejected this late is omitted for the current frame; its captured
last-good version resumes next frame. No stale emission or failed output buffer
is held indefinitely. Private evaluation records never enter the saved model.

## Diagnostics

Events are `:effect/failed`, `:effect/reload-failed` and `:effect/recovered`, with
show/epoch, logical time/frame, instance/cue/effect/version, stage and bounded
cause/source details. The latest 64 are at `[:variables :runtime :events]`, with
monotonic `:event-sequence`. Suppressed revisions emit no repeated events.
Trace collection stops at scheduling boundaries so deterministic replay does not
depend on serial versus worker execution. No Throwable is persisted.

The companion Studio provides asynchronous logs, snapshots, durable subscriptions
and Ring retry commands. Hardware recovery is a separate qualification gate.
