# Functional control layer

Read repository and source AGENTS.md files, then Tolglow's
`docs/implementation-contract-v1.md`. This folder is core-only and must load
without ports, clocks, worker pools or global show bindings.

- `model/apply-command` is the authoritative pure transition. Rejections preserve
  the original model; accepted changes emit event data and an acknowledgement.
  Keep bounded command receipts, epoch checks and explicit instance release IDs.
- Command time is supplied by the admitting shell. Physical device timestamps
  may be metadata; delayed events must receive current authoritative logical time
  before admission. Reducers never repair clocks by reading wall time.
- Parameter schemas in `params` match the portable authoring schemas. Coordinate
  changes with `tolglow.registry`; preserve captured definition versions for
  running instances and archived registry versions after cue deletion.
- `bindings` owns only passed-in interaction state. Soft takeover, relative
  controls and held gestures return commands; they never send them. Multiple
  gestures, early releases and stale acknowledgements must remain independent.
- `views` publishes selected domain data, never arbitrary model keys, raw source,
  private configuration or transport handles. Keep device rendering separate.
- Codecs only translate bytes/messages. Their tests establish protocol behavior,
  not physical device support. Push 2 helpers are source-derived; native display,
  hardware lifecycle and Push 3 verification remain separate work.
- Run all `afterglow.control.*-test` and codec test namespaces when modifying
  these contracts. Tests need no connected hardware or network listeners.
