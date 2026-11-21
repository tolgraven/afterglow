# Pure control codecs

Read the parent control guidance. Codecs consume explicit complete messages or
capture data and return immutable results. Do not open ports, read clocks or
infer device support from a related model's packet format.

- Push 3 User Mode message families are documented; numeric addresses must come
  from explicit captures. Push 2 SysEx/display packets are not Push 3 evidence.
- Keep channel, note and activation identity in MPE. Never collapse rotating
  channels into a single selected pad. Manager-channel messages stay distinct.
- Glide is pitch-bend expression, not an absolute X coordinate or calibrated
  physical displacement. Pressure/velocity are not force measurements.
- New expressive axes require source evidence and declared capabilities. Add
  capture tests for channel reuse, ambiguity, malformed input and exact release.
- Source-derived synthetic tests establish software behavior, not hardware
  qualification. Record the actual firmware, mode, setup and captured traces
  when physical tests become available.
