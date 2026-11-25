# Push cue-pad gestures

`afterglow.control.devices.push-cue-gesture` is the shared interaction policy for
[#543](https://github.com/tolgraven/tolglow/issues/543). The shipped Push 2 and
Push 3 profiles still use their existing gesture paths. Profile integration and
physical replay remain open.

| Pad at note-on | Short release | Held through the deadline |
| --- | --- | --- |
| Idle, without an available expression destination | Launch a persistent cue | Launch a temporary cue and release it on note-off |
| Running | End the captured instance | Enable that instance's expression while the pad stays down |
| Running with the configured modifier | Select the instance on note-on | Same selection, with no lifecycle command |

An idle cue with expression keeps its authored launch mode on note-on. The
modifier offers tap and hold for that cue. A timed or one-shot cue retains its
explicit launch behavior. An armed target selector applies to the next launch
and is consumed only when the policy emits that launch. The compound pad editor
and open target picker can claim new pad presses. The cue policy retains the
release path for a note it already owns, including across page changes.

## Timing and ownership

The default hold threshold is 220 ms, configurable through `:hold-ms`. A short
tap launches on note-off. The show model exposes launch and end, and an instance
keeps its launch mode. Waiting for classification allows one launch per gesture.
A hold starts on the first host-driven tick at or after its deadline. A release
at or after the deadline before a tick arrived does not produce a late flash.
Pressure and X/Y events leave the classification deadline alone.

Grid launches use the existing host queue. A tap submits a persistent launch
on note-off. A hold submits its held launch at classification, with the original
strike timestamp as metadata, and releases by queue ID. The host cancels a hold
whose boundary has yet to fire, or releases the exact instance from the terminal
receipt. A page change detaches waiting decisions and selection feedback from
their original view. Committed launches retain their captured cue ID. Show ID,
epoch, per-press token and pad key fence late receipts.

## Profile integration

- Normalize pad and expression messages into `step` events. User Mode pads use
  their captured channel and note as the key. MPE uses the decoder's full voice
  ID, including generation. Mark MPE retrigger and all-notes-off releases with
  `:cancelled?`; an existing hold still cleans up. Route monophonic pressure
  only when the adapter can identify a unique owning note.
- Pass the decoded pressed control IDs and captured `:button-bindings`.
  `:gesture-modifier` names an action and defaults to `:cue-gesture`. `nil`
  disables it. Shift fine editing stays a separate action. Call `step` with
  `:context` when changing page or origin and project `:selection` into the
  profile's selected cue and instance.
- Respect `:pass-through?` for an overlay-owned pad. Retain the overlay's own
  press, release and expression bookkeeping. Clear the one-use target picker
  after `:target-consumed?`.
- Drive `:tick` with the input's logical clock, including when the display is
  disabled. `next-deadline-ms` gives the next time needed. Call `acknowledge`
  for launch feedback, `stop` on teardown and initialize the state on show reset.
  Carry the supplied show identity and epoch through admission of every gesture
  command. At this base the device session checks epoch explicitly for grid
  launches and cancellations. Ordinary commands also need that admission check
  when the session adopts the policy. Use the owner's current logical time for
  dispatch.

## Expression

The shared expression planner uses available axes, valid parameter schemas,
authored `:control/axis` and `:control/semantic` metadata, and device and cue
overrides. `:param-mappings` and the persisted expressive policy can assign
components by index, disable individual parameters or disable individual axes.
For example, `{:xyz {:axis :slide :component 2}}` maps Slide to the third XYZ
component while preserving the other two. Color components use the schema's
declared color representation. The touch strip has its own mapping.

Use `:legacy-velocity? true` for Push 2 authored strike and poly-pressure ranges,
including reversed endpoints. A portable explicit mapping takes precedence for
that parameter. Push 3 User Mode supports strike and qualified aftertouch modes.
Push 3 MPE also has Glide (signed pitch bend) and Slide (CC74) on member channels.
An adapter can translate an existing Push 3 `:pressure-param` into an explicit
`:pressure` parameter binding. A pending launch has no instance to edit until
its accepted or fired receipt. An active hold edits the instance by its captured
definition and uses its latest parameter values for untouched components.

## Replay coverage

The focused tests use the real show reducer, quantization queue, Push 3 User
Mode decoder, and MPE decoder with synthetic bytes. They cover deadline and missed-timer
behavior, exact-instance stop and release, per-note expression, captured-layout
modifier decode, editor and target-picker precedence, and late receipts after
page and show changes.

Physical qualification needs timestamped Push 2 strike and poly-pressure, Push 3
User Mode pad and modifier bytes, and Push 3 MPE notes, pressure, pitch bend and
Slide from two simultaneously held pads on distinct member channels. Record the
mode, firmware, captured layout or MPE zone, and logical admission time. Replay a
tap and hold on an idle cue, an active hold with expression, an active tap, the
modifier and encoder editor collision, and both sides of a quantized release.
Compare emitted commands and instance IDs with the physical input trace.
