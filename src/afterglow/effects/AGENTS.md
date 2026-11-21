# Effect implementations

Read `../../AGENTS.md` and the root instructions. The legacy `IEffect` methods
are `still-active?`, `generate`, and `end`; `IAssigner/assign` receives the prior
value for its target. `params.clj` distinguishes frame-dynamic evaluation from
construction-time resolution; preserve that distinction during migration.

## Functional migration contract

- Evolve instance-local lifecycle state explicitly in the effect context.
  Return the new state, assignments, and requested external actions as data.
  No captured atoms, clocks, randomness, or global `*show*` reads in new kernels.
- Treat the immutable frame snapshot as shared input to workers. Each effect
  owns only its instance state; assignment groups are folded in stable order.
- Model graceful release and forced removal separately. One-shots, tweens,
  envelopes, scenes, and chases must have deterministic completion behavior.
- Keep code-effect execution at the coordinator boundary. Legacy `code` calls
  user code inside `swap!`; it is not proof of exactly-once execution under
  contention and must not be copied into new implementations.
- Preserve parameter units, range validation, static simplification, per-head
  context, and RGBW/movement semantics. An accelerated backend must match the CPU
  reference within stated tolerances before use for physical output.

## Tests

Before replacing behavior, extend `test/afterglow/effects` with fixed snapshots
and expected assignments or bytes. Cover nil versus absent assignments, ordering,
ending, relaunch identity, and replay. Run the original fade/step tests too when
their complete dependency classpath is available. Do not replace dependencies
with empty namespaces to claim that legacy integration passes.
