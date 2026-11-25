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

## Frame inputs that follow a candidate

A host computes some frame inputs before `advance`, from the definitions it
expects the frame to evaluate. Tolglow's modulated parameters and modulated
layer priority are examples: a controller owned by one cue changes the
parameters of other cues, and its configuration comes from its owner's
definition. When that owner has a reload candidate, the inputs of every modulated
instance depend on whether the candidate is accepted, which only `advance` can
decide. A per-instance fallback is not enough there. The last-good revision
would render with inputs computed for the candidate, and the host would have
committed controller state for a definition that never ran.

Such a host passes the inputs of both outcomes:

```clojure
(engine/advance model
                (assoc frame ::engine/reload-fallback
                       {:keyframe-params last-good-params
                        ::engine/priority-overrides last-good-priorities})
                compile-effect map-work)
```

`::engine/reload-fallback` is a map of frame inputs that replace the frame's own
when the frame rejects a reload. It may carry any input, including
`::engine/opacity-factors` and `::engine/priority-overrides`, but not `:time-ms`,
`:delta-ms`, `:epoch` or `:show-id`. With it the frame reads one input set
throughout:

1. Every instance is prepared. A candidate rejected at preparation selects the
   fallback before any step runs.
2. The remaining candidates are attempted, in one mapping call, on the frame's
   own inputs. Compilation, migration and evaluation can reject them here.
3. If every candidate was accepted, their results stand and the other instances
   evaluate on the same inputs. `:reload-inputs` is `:frame`.
4. If any candidate was rejected, every instance evaluates its captured revision
   on the merged fallback inputs. A rejected candidate stores its `:reload-fault`
   and emits `:effect/reload-failed` as usual. An accepted candidate's attempt is
   discarded with its state, intents, restart and migration; it stays a candidate,
   without a fault, and is attempted again next frame. `:reload-inputs` is
   `:fallback`.

The result is the frame a show renders when the rejected revision was never
published and the fallback inputs were the frame's own. The host commits the
state that produced the set named by `:reload-inputs`. Healthy instances
evaluate once, after the candidates are decided. A deferred candidate costs one
discarded attempt, and a `:migrate` candidate runs its pure migration again when
it is adopted. A frame with candidates makes two mapping calls, each with its own
executor deadline. Frames without candidates, and hosts that supply no fallback,
keep the single pass and the independent per-instance fallback described above.

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

A frame that supplied `::engine/reload-fallback` is the exception. Its other
results were evaluated on inputs that assumed the candidate, so `reject-output`
evaluates the whole frame again on the fallback inputs: the rejected candidate
stores an `:output` reload fault, its last-good revision renders in this frame,
and any other candidate is deferred. This is the only case in which healthy
effect code runs twice in a frame. The last-good revision's own output can still
be rejected once, as a current-version `:fault`.

## Diagnostics

Events are `:effect/failed`, `:effect/reload-failed` and `:effect/recovered`, with
show/epoch, logical time/frame, instance/cue/effect/version, stage and bounded
cause/source details. The latest 64 are at `[:variables :runtime :events]`, with
monotonic `:event-sequence`. Suppressed revisions emit no repeated events.
Trace collection stops at scheduling boundaries so deterministic replay does not
depend on serial versus worker execution. No Throwable is persisted.

The companion Studio provides asynchronous logs, snapshots, durable subscriptions
and Ring retry commands. Hardware recovery is a separate qualification gate.
