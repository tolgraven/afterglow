# Paused effect fault isolation — unverified WIP

Paused on coordinator request to conserve remaining credits. Branch
`codex/effect-error-isolation`, worktree `/workspace/afterglow-effect-isolation`.
Base is `f951313`; newer master must be merged before completion. Fetch explicitly:
`git fetch origin master:refs/remotes/origin/master` (the Tolglow remote previously
tracked only `effects`, so a plain named fetch did not update origin/master).

## Implemented here

- Strict kernel evaluation/merge helpers; new engine isolates recoverable effect
  compile, reload, evaluation and result failures while healthy effects advance.
- Failed revisions are suppressed, last-good hot reload code runs as fallback,
  and `:instance/retry` clears quarantine through the shared command reducer.
- Separate `:fault` and `:reload-fault` preserve suppression if both candidate and
  last-good version fail. Timed/releasing faulted instances still expire.
- Portable bounded diagnostics, 64-entry reactive journal, per-block source,
  and `engine/reject-output` to discard one renderer-attributed result without
  evaluating healthy code again. Private evaluation records stay outside model.
- Cancellation, interruption, VM errors and ThreadDeath remain frame failures;
  ordinary exceptions, assertions and linkage errors are recoverable.

## Verification so far

Focused kernel/engine/new faults tests: **36 tests / 198 assertions, all passed**.
Full pure lane: **262 tests / 2914 assertions, 8 failures**, no errors. Log:
`/tmp/afterglow-effect-isolation-pure.log`.

Failures are old contract assertions needing intentional updates and regression
review: replay_test.clj:251–254 expects whole-frame step failure; system_test.clj:160
expects three paused/hidden invalid-result throws; system_test.clj:166 compares
contribution maps without newly added provenance. Do not simply delete these:
assert fault isolation, discarded invalid output and preserved opacity behavior.

## Resume next

1. Merge current master; root approved narrow control/model.clj retry addition.
2. Update the old assertions above; add bounded history, paused failure and
   malformed-candidate-output rollback tests. Review explicit retry marker
   clearing and deterministic result order for equal orders.
3. Profiler owns renderer attribution follow-up in
   `/workspace/afterglow-render-attribution`, branch `codex/render-fault-attribution`,
   based optimized commit `41e3643`. Do not edit frame.clj concurrently. Contract:
   block `:source {:instance-id :effect-id :effect-version :cue-id}` becomes exact
   `:effect-source` in ex-data; global patch/options failures remain unattributed;
   final geometry uses effective positive-opacity aim/direction source.
4. Integrate that attribution commit and test scalar, typed, geometry failures
   with real renderer through paired Tolglow host. Healthy path must not render twice.
5. Update runtime AGENTS and architecture docs: old whole-frame-failure doctrine
   is no longer correct. Characterization audit: old show.clj:320 catches Throwable
   around entire send-frame and keeps looping; frame callbacks have separate catches.
6. Run full pure/parity; commit verified completion, push and create focused PR.
   Root owns merge after checks. No PR exists for this WIP yet.

Companion host work: `/workspace/tolglow-effect-isolation/RESUME.md`.
No owned server/worker/test process remains running at pause.
