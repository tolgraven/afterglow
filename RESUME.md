# Resume: performance profiling and renderer fault attribution

Paused at root/user request to conserve remaining allowance. Do not treat the
current attribution patch as complete or verified. No profiling/build/CI polling
should run until work is resumed.

## Completed

- Afterglow optimization PR https://github.com/tolgraven/afterglow/pull/8 merged
  as master `6e82fcf`. Original implementation commit `41e3643` kept unrelated
  pixel batches dense alongside geometric/exact-number target histories.
- On matched full matrices, 10,000 RGBW pixels + eight movers, two workers:
  complete host median 73.56 -> 18.22 ms; allocation 77.16 -> 13.05 MB/frame.
  Tail timings remained noisy; repeat had an overlapping frontend build. No
  stable 40 Hz claim. All model/intent/ArtDMX/preview oracle checks passed.
- Optimization tests: render/IR 41 tests / 478 assertions, pure 256 / 2,966,
  source parity 293 / 3,303, all passing before attribution changes.
- Tolglow profiler/report/workflow PR https://github.com/tolgraven/tolglow/pull/17
  is pending at `18515b7` on `codex/master-performance`, worktree
  `/workspace/tolglow-performance`. It has the complete raw matrices, documented
  exclusions, scoped master-push/manual/weekly artifact workflow, exact paired
  SHA/JVM/hardware/workload recording, and no timing thresholds. Most added lines
  are raw observations. Integrated-master small host/pipeline smoke and ledger
  validation passed. Artifact-attachment tool stalled for both PRs.

## Current WIP / ownership

This worktree `/workspace/afterglow-render-attribution`, branch
`codex/render-fault-attribution`, starts from Afterglow master `6e82fcf` (includes
MPE work). Only renderer `src/afterglow/render/frame.clj` has attribution WIP.
Runtime/kernel/engine and Studio host error recovery belong to agent
`effect_error_isolation_recovery_events_and_logs`; coordinate before editing.

Agreed contract: each contribution block may carry
`:source {:instance-id ... :effect-id ... :effect-version ... :cue-id ...}`.
Renderer failures from that output add the exact map as `:effect-source` in
ex-data, retaining original cause and ex-data/type. Global patch/options errors
remain unattributed. Host will quarantine/rebuild from already evaluated healthy
results, not evaluate effects again; retry at most once per culprit.

Current partial patch introduces `attributed-error` / `with-effect-source`, splits
general assignment reduction into mutable private merge + persist helpers, and
adds a private geometry source array passed via options. Positive-opacity
geometry writes record their source; unattributed replacement writes clear an
earlier source. Geometry resolution receives a source and wraps its calculation,
while malformed prior pan/tilt history remains outside attribution.

**Not yet wired:** contribution block validation/merge wrappers, allocation and
passing of geometry source arrays, general contribution reducer, tests and docs.
The ordinary `reduce-assignments` caller currently passes nil provenance, so
this patch alone does not provide working effect attribution. A namespace load
was launched just before pause (tool exec session `20175`); its result was not
inspected. It requires only the pure renderer and should exit on its own. No
benchmark/server/browser was started by the attribution work. Treat syntax and
behavior as unverified until explicitly checked.

## Next steps

1. Explicitly fetch both master refs:
   `git fetch origin master:refs/remotes/origin/master`. Root found that Tolglow's
   old fetch specification tracked only `effects`; do not trust implicit fetches
   or stale `origin/master`. Root has now corrected its fetch specification.
2. Finish provenance without per-effect double rendering or per-pixel metadata
   copies. Wrap existing block shape/batch validation and dense block merges.
3. In the mixed partition, merge sparse general assignments per block into one
   private object array rather than flattening them first. Pass block source and
   a private per-target geometry-source array, persist once, then pack once.
4. Refactor the rich/heterogeneous/exact-master general contribution fallback to
   reduce blocks with provenance before the shared general packing helper. Keep
   direct `resolve-frame` semantics unchanged.
5. Attribute final geometry failure to the last effective positive-opacity aim
   source, otherwise direction. Aim takes precedence over direction regardless
   of order. Do not prematurely reject a bad geometric value later overwritten
   with a valid one; zero-opacity writes must not steal attribution. Global
   malformed previous-values/previous-compact errors stay unattributed.
6. Add focused tests covering dense invalid batch/ordinary values, overflow,
   sparse exact arithmetic errors, geometry cancellation/overwrite/opacity/order,
   original cause/type, global errors and unchanged valid bytes/ownership.
7. Coordinate implementation checkpoint with the isolation agent so its kernel
   attaches `:source` and host consumes `:effect-source`. Keep runtime files out
   of this branch. Then run render/IR, pure/parity and actual host oracle smoke.
8. Open a separate attribution PR after verification. Do not rewrite merged PR8.
   Resume master profiling after integration; inventory all active agent lanes
   before requesting a quiet CPU window (new rig/LiDAR lanes appeared during the
   previous interval). Dedicated CI artifacts are preferable for tail evidence.

## Tool environment

```
PATH=/workspace/.tools/clojure-1.12.7.1681/bin:$PATH
JAVA_TOOL_OPTIONS=-Duser.home=/workspace/.tools/java-home
CLJ_CONFIG=/workspace/.tools/clojure-config
AFTERGLOW_ROOT=/workspace/afterglow-render-attribution
```

Prefix each independent shell command or export explicitly; temporary variable
assignments before the first command do not apply after `&&`. Use an explicit
Afterglow local dependency override for Tolglow worktrees; their default
`../afterglow` points to root's separate checkout.

No claim of an ongoing background profiler after this agent stops. The repeatable
command and pending CI workflow are the durable monitoring handoff.
