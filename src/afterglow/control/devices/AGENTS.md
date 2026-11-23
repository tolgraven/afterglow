# Device sessions and transport boundaries

Read `../AGENTS.md` and the shared implementation contract first. This folder is
the explicit I/O boundary: domain/effect state remains in the pure control model.

- Profiles return local interaction state, commands, MIDI messages and display
  views. Keep parsing, cue rules and projections independently testable.
- Session locks serialize one adapter's resources only. The host's synchronous
  `dispatch!` owns authoritative show admission; do not mutate its model here or
  introduce callbacks inside CAS retries.
- Use current authoritative logical time when admitting commands, including
  deferred releases. Capture session/generation for callbacks; invalidate old
  scheduler ownership separately on suspend/resume. Keep multiple devices isolated.
- Requiring these namespaces must never enumerate/open hardware, start workers,
  load native libraries or bind OSC. Only explicit factory/open calls acquire them.
- Close every acquired resource on partial startup failure, including missing
  native-library errors. Disconnect cleanup still releases this session's held
  instances while skipping protocol writes to absent hardware.
- Push 2 palette capture precedes LED mutation; preserve white components and
  restore captured palettes on handoff/close. Keep LED batches bounded and use
  device acknowledgements/timeouts. Never fabricate palette responses.
- Wayang uses static native methods and supports one process-wide display lease.
  Refuse concurrent leases; injectable independent displays remain supported.
- Push 3 uses captured MIDI mappings. The optional tethered screen owns only the
  verified display interface. Use the libusb recorder and physical qualification
  guide for changes. Standalone hosting and pad LED output remain unqualified.
- Run session/transports tests plus control model and codecs. Tests use real
  reducers with recording transports and headless images; no physical device
  support is established until captures and hardware checks are recorded.
