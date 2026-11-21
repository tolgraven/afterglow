# Push 2 control parity

The composable profile now edits all supported shared parameter types through
the real command reducer. These are source-derived protocol behaviors with
capture-sink tests; physical Push hardware has not been verified.

## Parameter editing and selection

The eight encoders edit a bank of eight parameters. A definition's `:param-order`
is followed first, then schema `:order`, then stable parameter-key order. Shift
and the Page buttons (CC62/63) move between banks. The Page buttons without Shift
move through active instances without launching or ending them. Each instance
retains its own bank and composite-component selection.

Numeric values clamp to declared bounds, integer values retain integer type,
booleans use direction or the corresponding top button, and enum values retain
their original data (including registered waveform-selection maps). Shift makes
continuous relative edits ten times finer. Color editing uses hue, saturation
and brightness over the model's linear RGB values. Vector components and range
endpoints can be selected separately; range endpoints cannot cross.

Touch an encoder (notes0–7) to address its parameter with the pitch-bend strip.
The corresponding top button (CC20–27) cycles a composite value's component.
Touching a color or enum parameter temporarily assigns the pad grid to that
picker. Releasing the encoder returns the grid to cue launching. Multiple held
encoders retain touch ownership; releasing the newest returns to the previous
touch. Changing banks or active instances clears the old touch binding. If an
instance disappears, a delayed strip input cannot edit the replacement instance.

`afterglow.control.parameter-edit` supplies the pure typed editing operations;
the Push profile supplies only MIDI addresses and local interaction state.
Every write is a normal `:param/set` command carrying the exact instance ID.

## Display contract

`:parameters` contains the visible bank, with existing schema/value fields plus
`:component` and `:component-label`. `:parameter-bank` exposes index/count/total/
offset. `:touched-parameter` is nil or an explicit instance/parameter/encoder/
component selection. `:active-effects` is a bounded eight-instance window, with
`:active-effect-navigation` containing index/count/offset. Waveform and captured
audio projection remain on the offscreen display worker, outside the show clock.

## Remaining parity

Pressure/velocity mappings, Shift held-cue override, cue parameter presets,
tempo/beat controls, distinct stop/run semantics and linked viewports remain
separate acceptance work. Do not infer those interactions from display widgets.
The comprehensive cross-surface checklist lives in Tolglow's
`docs/control-parity-audit.md`.

## Verification

Focused real-session/typed-helper tests pass26 tests/204 assertions. They exercise
the actual MIDI decoder, composable session, parameter validation and shared
command reducer with capture transports. No MIDI port, native display or physical
lighting output is opened.
