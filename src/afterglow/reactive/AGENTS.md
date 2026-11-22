# JVM reactive owner boundary

This is a control-plane boundary, not an effect or pixel implementation. Source
ratoms have ordinary immediate `@`, `reset!`, `swap!` and watch behavior. Each
`publish!` captures their values once; tracked reactions and registered effect
handlers see that same immutable snapshot. Callbacks run under the owner lock,
never inside atom CAS retries or renderer workers. Keep source data immutable.

`reg-sub!` handlers receive a context and query. A value-returning handler is
recomputed from tracked dereferences. A handler returning a zero-argument
function constructs it once per cached query; its inner dereferences are then
tracked. Propagate changes to downstream nodes only when values differ.

Registered effect watchers emit portable semantic action maps. Drain them at the
start of the next owner cycle, stamp the current model epoch/source/time/command
identity there, and use the ordinary command reducer. Do not apply commands from
inside a reactive callback. Explicit source writes during a batch are visible
to derivations in the next batch.

Persistence stores definitions and comparison data, not live functions or
handles. Validate source without reader evaluation or custom tagged readers.
Only an explicit trusted-source restore compiles a literal function form; never
evaluate code merely because a fixture or imported EDN document contains it.
A saved Var descriptor uses the locally registered function when its kind, id
and qualified symbol match, including across a staged restore using
`:local-system`. A cold import may supply a host-owned `:allowed-vars` set of
qualified symbols. Keep that policy outside the saved show.
Keep the public portable schema coordinated with Tolglow state persistence.

Run `afterglow.reactive-test` with real callbacks and controlled thread/latch
tests. No hardware, clocks, pools or subscriptions start at namespace load.

## Subscription ownership and coeffects

Direct REPL `subscribe` returns a cached signal retained until `dispose!`. UI,
socket and temporary code consumers should use `acquire!` and its idempotent
`:close!`. The initial value and listener are installed under one owner lock.
Listeners receive only distinct committed changes. `watch!` also retains its
query. Dropping the last lease or watcher releases the whole unused dependency
branch, removes external atom watches, and cancels queued and active reads.
`demanded-queries` inspects live registrations without evaluating a handler.

```clojure
(reg-ref! system :orientation sensor-atom :orientation)
(reg-cofx! system :weather {:mode :background :interval {:beats 1/2}
                            :initial 0 :sample (fn [db] (read-temperature db))})
(reg-sub! system :temperature
          (fn [{:keys [cofx]} _] (cofx :weather))
          {:validate number? :fallback 0 :on-error :last-good})
(let [{:keys [value close!]} (acquire! system [:temperature] deliver-reading!)]
  (try (display-first! value) (finally (close!))))
```

A registered reference accepts an optional projection function (a keyword also
works). An update outside the selected path suppresses downstream work.
`:mode :demand` samples only when a subscribing calculation actually reruns.
Call `invalidate!` to request another calculation on the next publication.
`:mode :frame` samples once on each publication while observed. Concurrent
calculations read the same captured input. Background samplers run on two owned
workers with a bounded queue. Physical `{:fps n}` and `{:ms n}` cadences use
a scheduler while observed; musical intervals use the published transport and
skip missed beats. A busy source has at most one outstanding sample. Disposing
and reacquiring gives the new lease a distinct result slot, even if a cancelled
external read ignores interruption.

Use `:validate` with a predicate or a registered clojure.spec keyword. Options
with a durable descriptor can include a named spec and a portable fallback.
The default `:on-error :last-good` retains the most recent validated value and
can use a fallback until the first success. With `:on-error :fallback`, each
failure selects the configured fallback. Omitting that value makes the signal
unavailable until validation succeeds again. Listeners and effect handlers
receive an explicit `:fallback nil` only when the validator accepts nil. Attach an `:owner` map of
`:cue-id`, `:instance-id` and/or `:effect-id` for diagnostics. Application
ratoms including `db-signal` support normal IRef validators. A rejected owner db
publication retains its prior value while independent sources continue.

Each failed registered effect discards its own queued actions. Its siblings still
run. Read recent bounded diagnostics at the REPL with `faults`. Publications
return new diagnostics under `:faults`. Default reporting goes through the
show’s Timbre appenders with the throwable. A host can inject `:on-fault!`
when constructing the graph. Keep diagnostic callbacks nonblocking. Restore
reopens coeffect lifetimes against the existing application's registered input
definitions. Runtime references, worker jobs and network handles are not saved.
