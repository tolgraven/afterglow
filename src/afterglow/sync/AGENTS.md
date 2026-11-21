# Synchronization

The public lifecycle is in `afterglow.sync`. Construct a manager per show and
supply its clock and event callbacks explicitly. Construction, configuration,
loading a saved show, and requiring a namespace must leave devices closed.

* `config` validates clock and pairing data. `session` owns generation-stamped
  events, bounded queues, published clock samples and IO submissions.
* `midi`, `beat-link` and `ableton-link` each acquire and close their own
  transport. Preserve timestamps received at capture, source selection, Link
  transport-follow settings and exclusivity of singleton Beat Link resources.
* Additional source adapters are keyed by their config section in `:adapters`.
  The manager merges `:defaults`, calls an optional `:normalize`, and calls
  `:transport` with the settings, monotonic clock and run ID only at start.
  The returned map supplies `:open!` (taking the event callback) and `:close!`
  (taking its handle). The source can subscribe to event types through
  `:events` and `:receive!` or implement periodic maintenance with `:tick!`.
* `:prepare-state` transforms state at configure, start and rebind. `:run-state`
  allocates per-run resources, `:lifecycle!` receives opened, rebind and
  stopping phases, and `:status` projects public status. Use namespaced
  extension keys for independent adapters. Clip recording, DAW commands and
  other application-specific behavior belong in the host.
* Keep slow IO outside the event owner. A timed-out stop retains ownership
  until all transport handles and workers have finished. Exercise acquisition,
  cancellation, rebind and partial failure using `lein test afterglow.sync-test`.
