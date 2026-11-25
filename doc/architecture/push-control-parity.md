# Push 2 control parity

## Select and reorder active cues

Set `:active-cue-grid? true` in the Push 2 connection options. Press **Select**
to open the active edit grid or **Duplicate** to open the reorder grid. The
active mode's button lights up. Press it again to return to the cue launch grid.
Page Left and Right navigate banks of 64 running launches.

The bottom-left pad is the first running launch in compositing order, followed
by the remaining pads from left to right and bottom to top. Two running copies
of the same cue occupy separate pads. In Select mode, tap a pad to edit that
launch's parameters. In Duplicate mode, tap the launch to move, then tap the
launch it should follow. Duplicate gets brighter when a source is selected.
Tap the source a second time to clear it. The pads update to the committed order
after the show accepts the move.

Pad input waits for acknowledgement of the visible LED layout. A running
launch that ends between feedback and a press cannot redirect the press to its
replacement. The two modes use the shared
[instance reorder operation](native-layers.md#reordering-active-instances).
The virtual MIDI tests qualify the controller profile and reducer. Physical
Push 2 verification remains open.

The composable profile now edits all supported shared parameter types through
the real command reducer. These are source-derived protocol behaviors with
capture-sink tests; physical Push hardware has not been verified.

## Parameter editing and selection

The eight encoders edit a bank of eight parameters. A definition's `:param-order`
is followed first, then schema `:order`, then stable parameter-key order. Shift
and the Page buttons (CC 62/63) move between banks. The Page buttons without Shift
move through active instances without launching or ending them. Each instance
retains its own bank and composite-component selection.

Numeric values clamp to declared bounds, integer values retain integer type,
booleans use direction or the corresponding top button, and enum values retain
their original data (including registered waveform-selection maps). Shift makes
continuous relative edits ten times finer. Color editing uses hue, saturation
and brightness over the model's linear RGB values. Vector components and range
endpoints can be selected separately; range endpoints cannot cross.

Touch an encoder (notes 0–7) to address its parameter with the pitch-bend strip.
The corresponding top button (CC 20–27) cycles a composite value's component.
Touching a color or enum parameter temporarily assigns the pad grid to that
picker. Releasing the encoder returns the grid to cue launching. Multiple held
encoders retain touch ownership; releasing the newest returns to the previous
touch. Changing banks or active instances clears the old touch binding. If an
instance disappears, a delayed strip input cannot edit the replacement instance.

`afterglow.control.parameter-edit` supplies the pure typed editing operations;
the Push profile supplies MIDI addresses and local interaction state. Each
command carries the exact instance ID.

## Temporary parameter edits

Tolglow enables operator gestures on dedicated Push 2 connections. A custom
host can enable them with `:operator-gestures? true` and trusted command
dispatch. Accent is the default temporary modifier. Set
`:temporary-encoder-modifier` to another button's MIDI CC if desired. That CC
takes precedence over the button's usual action. Shift controls encoder step
size, and old `:shift` and CC 49 settings now select Accent. [Push 2 MIDI reference](https://github.com/Ableton/push-interface/blob/5eb352fe3da9d07891efb7447191c03a66d9fbdd/doc/AbletonPush2MIDIDisplayInterface.asc#L2061)

Hold Accent as you touch an authored parameter encoder. Turns, strip
changes and the touched parameter's checkbox or picker apply live. Numeric,
integer, boolean, enum, color, vector and range parameters are supported. The
encoder remembers its mode until lift, even if you let go of the modifier first. On lift or disconnect, the show owner
restores the pre-touch value if the gesture still owns it. A newer edit to the
same parameter takes precedence. Temporary gestures leave no undo entry, and
an unadmitted temporary gesture ignores turns for that touch. This includes
empty slots and targets that have stopped running. Each encoder tracks its own
touch. Ordinary scalar touches still record an undo entry.

Push 3 supports temporary numeric edits through its captured User Mode touch,
turn and modifier mappings. The same gesture works with Poly/Mono Aftertouch
and MPE. See the [Push 3 setup](expressive-devices.md#push-3-user-mode).

If a live effect reload makes the starting value invalid, release closes the
gesture and keeps the current value accepted by the new definition.

## Physical strip, master and tempo

The strip receives source-derived mode and 14-bit value messages for the touched
component. Level, centered, point and dark modes are diffed; an untouched strip
is cleared. Handoff and orderly close restore Push's default point/return mode.
Disconnect cleanup avoids writes to absent hardware.

Touching the master encoder (note 8) assigns the strip to master level. Turning
CC 79 adjusts master by 1% per tick, or 0.1% with Shift. Touching the tempo encoder
(note 9) assigns the strip to BPM. CC 15 changes tempo by 0.1 BPM, or 1 BPM with
Shift, using the original controller's 20–200 BPM range. Tempo edits use the
existing shared `:transport/set` operation and are disabled when the snapshot
identifies an external clock source. These global controls also work with no
active cue. Releasing a newer touch restores the previous touch target.

## Pad expression

Numeric parameter schemas can opt into pad velocity and polyphonic pressure
with `:velocity true`. Optional `:velocity-min` and `:velocity-max` define the
response endpoints and can reverse direction. Defaults use schema bounds, or
0–1 for an unbounded schema. Values remain schema-valid and integer parameters
remain integers. Only opted-in numeric parameters respond.

Velocity overrides apply to both held and persistent launches. Subsequent
pressure addresses the exact launched instance using its captured definition,
even while another instance is selected. Releasing the pad drops ownership;
late pressure cannot follow a new instance of the same cue. Holding Shift while
pressing a held cue launches it persistently, so releasing the pad leaves it
running. A later Shift press ends that persistent activation.

## Saved cue defaults

Hold Record (CC 86) and press a top button to save all current values of the
selected instance as that cue's defaults. Hold Shift and Record to clear those
saved defaults. These gestures call generic `:cue/save-params` and
`:cue/clear-saved-params` commands with `:cue-id` and `:expected-version`; saving
also supplies the exact `:instance-id`.

The model publishes a new cue version with a portable `:saved-params` map.
Authored `:params` remain separate. Launch precedence is effect defaults,
authored cue parameters, saved parameters, then explicit launch parameters
(including pressure/velocity overrides). Clearing removes the saved overlay.
Neither operation mutates running instances. Stale cue versions, unrelated
instances and values incompatible with the cue's current effect schema reject
atomically. Ordinary command receipts make retries idempotent.

## Display contract

`:parameters` contains the visible bank, with existing schema/value fields plus
`:component` and `:component-label`. `:parameter-bank` exposes index/count/total/
offset. `:touched-parameter` is nil or an explicit instance/parameter/encoder/
component selection. `:active-effects` is a bounded eight-instance window, with
`:active-effect-navigation` containing index/count/offset. Waveform and captured
audio projection remain on the offscreen display worker, outside the show clock.
`:preset` contains `:saved?`, `:changed?`, `:record?` and the intended `:action`
(`:save` or `:clear`); it carries no source code or private controller state.
`:touched-control` is nil or `{:target :master|:tempo :editable? boolean}` for
global control emphasis and explicit sync-lock feedback.

## Remaining parity

Tap/beat/bar/phrase alignment, distinct stop/run semantics and linked viewports remain
separate acceptance work. Do not infer those interactions from display widgets.
Phase changes require Tolglow's whole-model clock rebasing, including composition,
auto, modulation, routing and sensor timing; device code must not mutate beat
coordinates independently.
The comprehensive cross-surface checklist lives in Tolglow's
`docs/control-parity-audit.md`.

## Verification

The complete `./bin/test parity` lane passes 290 tests / 3,188 assertions. The
control cases exercise the actual MIDI decoder, composable session, parameter
validation, versioned cue publication and shared command reducer with capture
transports. No MIDI port, native display or physical lighting output is opened.

## Choosing a display view

Display actions are local to each controller session. Push 2 Session opens an eight-page bank. The upper display buttons choose the corresponding page, and Page Left/Right change banks. Choosing a page resets the cue grid origin. Shift + Session cycles the miniature color scheme through combined, cue and type colors. The regular cue pads still control the selected page.

Layout opens the simulator. Shift + Layout opens rig configuration. In either scene, Mix changes the camera between fit, panorama and audience. In rig configuration, Page Left/Right select fixtures. Press the same display button again to return. Device opens parameters, and Shift + Device cycles the visual format. In the history view Shift + Page Left/Right zoom the beat window from half a beat to sixteen beats. Clip selects captured audio. Shift + Clip selects the material stage trace.

Push 3 User Mode can bind captured buttons to the same semantic actions, including `:display/pages`, `[:display/select-page 0]`, `:display/rig`, and `:display/zoom-in`. The device profile sends the same typed Push view to an optional [tethered USB display](push-3-display.md). `push-3/control-view` also provides a pure grid and keyed values for external consumers. The captured button tests use virtual MIDI transports.

## Cue pad visualization

An optional session feedback source acquires a handle with `:open!` and calls
`:project! [handle local-state committed-model]` on refresh. The private
projection may supply `:afterglow.control.views/pad-colors`, keyed by cue ID with
normalized RGB vectors. Push 2 samples the active page through this projection
and keeps its authored selection swatch on the display. Missing previews fall
back to parameter color, authored cue color or hex swatch. Normal, active and
releasing pads retain their relative brightness. The session calls `:close!`
on suspension, disconnection and projection failure. Cue launches and other
input commands always use the committed model. The paired Tolglow host owns
page interest, musical sampling and interpolation.

### Control projection cost

Each Push 2 feedback pass sorts the active instances by priority, order and
instance ID and groups them by cue. The display and all pad LEDs share that
local index. The next feedback pass builds a fresh index from its committed
model, including launches, releases, parameter changes and removals.

A loopback capture with 32 running cues on a 64-cue page replayed 80 identical
show frames before and after indexing. The four comparison runs produced all
8,910 MIDI messages and 80 display views identically. Active-instance sorts
fell from 47,440 to 720 across device and cue-preview consumers. Mean session
CPU fell from 14.51–17.61 ms to 5.87–6.30 ms per committed frame. The
emulated surface returned 560 acknowledgements. These timings measure CPU
work in the session and exclude physical USB latency.
