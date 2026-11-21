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
Keep the public portable schema coordinated with Tolglow state persistence.

Run `afterglow.reactive-test` with real callbacks and controlled thread/latch
tests. No hardware, clocks, pools or subscriptions start at namespace load.
