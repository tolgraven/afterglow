# Controller adapters

Read the repository AGENTS.md and source-level instructions first. The migration design lives in the sibling Tolglow checkout at `docs/architecture/control-and-web.md`; status there distinguishes proposals from shipped APIs.

- Preserve existing public controller binding/deactivation behavior while introducing the common control model. `controllers.clj` already supplies grid, overlay, recognizer and cue helpers; characterize these rather than assuming no shared functionality exists.
- Keep protocol parsing/encoding, pure interaction state, view projection and resource lifecycle separate. MIDI/SysEx numbers and native display details belong in device adapters; cue, parameter, macro and transport semantics belong in the common control layer.
- New pure helpers receive time and state explicitly and return state/messages. Do not hide atoms, show bindings or port sends inside composable transformations. Mutable resource handles and owned display buffers belong in the session shell.
- Importing new namespaces must not open devices, start scheduler threads or alter an active show. Acquire resources explicitly and release only the session's ports, callbacks, timers and display buffers on stop/disconnect.
- Associate releases with gesture and launched instance IDs. Stale callbacks and device acknowledgements must not mutate a replacement session. Bound input/output queues and preserve launch/release ordering.
- Preserve palette restoration, relative encoder signs, touch/hold behavior, user-mode handoff and feedback rate limits during Push 2 migration. Avoid a global callback that prevents multiple independent devices.
- Push 3 requires verified identity/protocol/mode capabilities. Do not infer compatibility with Push 2 SysEx, display transport or Wayang. Record firmware/mode and hardware evidence separately from simulator tests.
- Use recorded/documented messages for codec tests and pure fixtures for behavior. Run focused tests without connected devices. Hardware checks are explicit and must not run as a side effect of ordinary CI.
- Avoid editing shared command schemas while another agent owns them; agree on the contract first. Update tests, compatibility notes and migration status with implementation changes.
