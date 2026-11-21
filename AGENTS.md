# Working on the Afterglow fork

This is `tolgraven/afterglow`, paired with `tolgraven/tolglow`. The current
architecture program is indexed in [doc/architecture/README.md](doc/architecture/README.md).
Read it and applicable nested AGENTS.md files before changing behavior.

* Keep `project.clj` as the application manifest. `deps.edn` and `bin/test`
  provide plugin-free, headless test entry points; the legacy test lane reads
  application dependencies and explicitly substitutes Beat Link 8.0.0 for an
  unavailable 8.0.0-SNAPSHOT. Do not mistake that for a validated app upgrade.
* Run `./bin/test pure` for the experimental context runtime and show binding;
  run `./bin/test legacy` for engine behavior. Preserve existing fade tests.
  No test should start real DMX, Art-Net, OSC, MIDI or controller output.
* `src/afterglow/runtime.clj` is an additive experimental kernel. It is not
  wired into `show/send-frame`. Do not claim the legacy engine has migrated.
* Move state out of effect closures into explicit instance context. Functions
  return next state, assignments and intent data; the boundary owns I/O.
  Avoid mutable values inside ostensibly immutable snapshots, implicit wall
  clocks/randomness, and callbacks inside CAS retry functions.
* Preserve ordered reduction within each target, kind resolution order and
  output packing behavior. Parallelize independent work only; combine results
  by priority/launch order, never by completion order. Define buffer ownership.
* Treat channel packing, cross-universe addressing, RGBW semantics, movement
  history and lifecycle/release as separate compatibility gates. A green pure
  lane proves none of these on its own.
* Use tolglow's `docs/work-items.edn` for cross-repo work ownership, prerequisites,
  acceptance and evidence. Claim disjoint paths, coordinate public contracts,
  and record completed tests before marking an implementation item done.
* Keep legacy adapters explicit. Do not globally serialize the new runtime to
  hide shared mutable state, or run legacy closures concurrently without proving
  their safety. Bounded resource use and transport failure handling belong to
  the coordinator, outside pure effect evaluation.
* Source, effects, controllers, web, resources, dev and test folders have local
  guidance. Preserve upstream license attribution when restructuring code.
