# Effect failure isolation

`afterglow.runtime.engine/advance` isolates recoverable failures per instance.
The lower-level `runtime/render-frame` remains a strict kernel; the coordinator
owns recovery policy. Both use the same result validation and ordered merger.

## Failure and recovery

Compilation, evaluation or result failure preserves the last committed `:state`
and discards the attempt's output, intents and completion flag. Healthy instances
continue. The failed current version stores `:fault` and is suppressed until an
explicit retry or a newer definition under the selected reload policy.

For `:preserve-state` and `:restart`, a bad candidate stores `:reload-fault` while
the captured last-good definition is retained. Preparation/compile/evaluation
failure evaluates that captured version in the same frame. Separate fields
preserve suppression if both candidate and captured versions fail. Pinned cues
remain pinned. Timed/releasing faulted instances still reach their normal expiry;
pause retains its private-clock semantics.

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
