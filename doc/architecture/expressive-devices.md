# Expressive device controls

The Push 3 and Seaboard adapters use the same immutable control model as the
web UI. MIDI decoding, held-note ownership, parameter mapping and device views
are pure functions. Only an explicitly opened device session owns the transport
and lock. Requiring these namespaces does not enumerate ports or send MIDI.

This is a source-grounded, capture-tested implementation. No Push 3, Seaboard,
Ableton Live or Max hardware host was connected for these tests. Numeric Push 3
addresses, native LED/display protocols and standalone USB transport have not
been verified. No Push 2 SysEx is reused.

## Sources and signal meanings

The [Ableton Push manual](https://www.ableton.com/en/push/manual/) sections on
Expression, expressive pads, and [User Mode](https://www.ableton.com/en/push/manual/#user-mode)
describe pressure, vertical Slide, horizontal per-note pitch bend, and pad
velocity. User Mode retains the selected expression mode; MPE rotates MIDI
channels between presses. Encoders send relative CC messages with the recommended
linear two's-complement mode, encoder touches send notes, buttons send CC, and
the strip continues sending pitch bend. User itself cannot be mapped.

Horizontal Glide is normalized pitch bend, **not calibrated absolute pad X**.
Push's Finger/Pad tuning setting, width and pitch-bend configuration alter its
response. Slide represents the vertical expression dimension, not millimetres.
Strike is note-on velocity and Pressure is continuing aftertouch; neither is a
calibrated force measurement. Firmware/Live settings and a capture from the
actual User port must confirm the emitted data before hardware support is claimed.

ROLI's official [MIDI message guide](https://support.roli.com/en/support/solutions/articles/36000019142-what-midi-messages-do-seaboards-and-lightpads-transmit-)
and [Seaboard M Live setup guide](https://support.roli.com/en/support/solutions/articles/36000576272-using-the-seaboard-m-with-ableton-live-12)
identify the five Seaboard dimensions and MPE operation. The message mapping is:

| Axis | MIDI message | Normalized range | Timing |
| --- | --- | --- | --- |
| `:strike` | Note-on velocity | 0–1 | At press |
| `:pressure` | Member-channel pressure | 0–1 | While held |
| `:glide` | Member-channel pitch bend | −1–1 | While held |
| `:slide` | Member-channel CC74 | 0–1 | While held |
| `:lift` | Note-off velocity | 0–1 | Before release |

The [MIDI Association's MPE overview](https://midi.org/midi-polyphonic-expression-mpe-specification-adopted)
explains the channel-per-note mechanism. The receiver implements MIDI 1.0
channel messages for one explicit lower or upper MPE zone. Manager-channel
expression is reported separately and does not alter a selected cue. RPN zone
negotiation, semitone pitch-range conversion, sustain-pedal interpretation,
MIDI 2.0 and multiple simultaneous zones are not implemented. The ROLI guides
were available through official indexed documentation; direct support-page
fetches redirected to the support service's sign-in endpoint during this work.

## Push 3 User Mode

Manually set the desired Expression Mode, enter User Mode in Control Mode,
and choose the actual User MIDI input. The application does not change device
mode using an undocumented packet. Set `:user-mode? true` to acknowledge this
setup. Live-mode handoff uses `session/suspend!` / `session/resume!`; stopping a
session releases only its owned held instances.

`afterglow.control.codecs.push-3/capture` learns one address from a supplied
complete MIDI message. A capture is data, not proof of which device emitted it.
All channel numbers in these APIs are **zero based**. For example:

```clojure
(require '[afterglow.control.codecs.push-3 :as push-codec])

;; Substitute messages captured from your own device. These bytes are synthetic.
(def layout
  (-> {}
      (push-codec/capture {:kind :pad :id [0 0] :bytes [0x93 12 127]})
      (push-codec/capture {:kind :encoder :id :level :bytes [0xb2 19 1]})
      (push-codec/capture {:kind :encoder-touch :id :level :bytes [0x92 9 127]})))
```

The layout supports `:pads`, `:encoder-touches`, `:encoders`, `:buttons`,
`:touch-strip` and `:mono-pressure`. It rejects overlapping note/CC identities
within each message family. There is no default numeric address map.

```clojure
(require '[afterglow.control.devices.push-3 :as push])

(def profile
  (push/profile
    {:user-mode? true :expression-mode :poly-aftertouch
     :layout layout :page-id :main
     :encoder-bindings {:level {:param :level}}
     :pressure-param :level}))
```

In Poly/Mono Aftertouch mode, pad cells follow the page's cue launch mode;
default persistent cues toggle, held cues release their exact activation, and
one-shots use the model's finite-duration rules. Repeated note-on and CC-down
messages do not create repeated edges. Poly pressure targets the corresponding
pressed pad's activation. Mono pressure and an explicitly bound strip target
the selected activation. Encoder mappings use current schema bounds; integer
parameters step by one unless overridden. Captured buttons can control blackout,
transport, page scroll or suspend. `control-view` returns labels and values for
another UI; it does not drive Push 3's screen.

For MPE, capture the note-to-pad relationship across repeated presses on rotating
member channels. This is a separate explicit mapping, not a collapsed channel
address:

```clojure
(def expressive-push
  (push/profile
    {:user-mode? true :expression-mode :mpe
     :layout {}                       ; add fixed encoders/buttons if captured
     :zone {:manager-channel 0 :member-channels [1 2 3 4 5 6 7 8]}
     :mpe-note-cells {40 [0 0] 41 [1 0]} ; synthetic example, verify your unit
     :page-id :main}))
```

MPE member channels belong exclusively to the expressive receiver. Fixed controls
must be captured on channels outside that member range. Each note launches a
held cue activation; member pressure/bend/slide address that activation. This
mode exposes Strike, Pressure, Glide and Slide. Push 3 Lift capability is not
assumed merely because MIDI note-off has a velocity field. Native display,
automatic LEDs and offscreen web rendering remain separate work.

## Seaboard and generic MPE

`afterglow.control.devices.seaboard/profile` enables all five documented axes.
Match `:zone` to the device's configured Dashboard settings. No default zone or
note-to-cue arrangement is guessed:

```clojure
(require '[afterglow.control.devices.seaboard :as seaboard])
(def seaboard-profile
  (seaboard/profile
    {:zone {:manager-channel 0 :member-channels (vec (range 1 16))}
     :note-cues {60 :wash 62 :sweep}}))
```

The generic `devices.mpe/profile` additionally requires explicit `:axes`.
Instead of `:note-cues`, use one `:cue-id` for all member notes or `:note-cells`
and a page ID. Same-pitch notes on different channels remain independent.
Each activation gets `[channel note generation]` identity. Note-off releases
only its voice; delayed launch receipts preserve pending expression and apply
Lift before release. Rejection removes pending ownership. Restart clears local
voices; stale transport callbacks are rejected by the common session generation.

Before-note expression is retained, then reset after the last channel note ends.
If multiple notes share a member channel, note ownership is retained but channel
expression is withheld with an `:ambiguous-member-channel` diagnostic. A repeated
note-on at the same channel/note ends the prior voice and starts a new one. MIDI
1.0 has no generation field, so a physically delayed note-off with exactly the
same channel/note cannot be distinguished from the new note's release.

To acquire resources, use each adapter's `connect!` with the profile options plus
the common session options: `:session-id`, `:model!`, synchronous `:dispatch!`,
`:now-ms!`, and an injected `:midi` transport. Close explicitly. The REPL facade
also exposes `open-push-3!` and `open-seaboard!` through the common host lifecycle.

## Automatic parameter mapping

Parameter schemas declare semantic intent once:

```clojure
{:level {:type :number :default 0.5 :bounds [0 1] :control/axis :pressure}
 :pan {:type :number :default 0 :bounds [-180 180] :control/axis :glide}
 :pattern {:type :enum :default :a :values [:a :b :c] :control/axis :slide}}
```

`devices.expressive/plan` combines these annotations with the device's declared
available axes. Numeric values scale into finite schema bounds; integers stay
inside integer bounds, booleans use the midpoint threshold, and enums use ordered
bins. Glide zero maps to the numeric midpoint. An explicit `:control/axis nil`
opts out. Profile `:param-mappings` and per-cue `:cue-mappings` override metadata.
Builtin recipes can carry annotations so the common path needs no manual mapping.

Unannotated conventional names such as level, pan and focus produce suggestions
with reasons and require selection before use. Unknown parameters, unsupported
types, unknown axes and unavailable axes produce diagnostics. Color/vector/range
parameters are not silently flattened to a scalar. Plans capture the cue's exact
effect version when the note starts, including pinned registry versions. Relaunch
to adopt changed mapping metadata. Parameter commands still pass the authoritative
model's validation, including any schema changes introduced by hot reload.

## Verification

The four new codec/device test namespaces contain 17 tests and 115 assertions at
this checkpoint. They exercise real command admission, channel isolation, typed
mapping, pinned definitions, delayed acknowledgements, held cleanup, restarts,
relative encoders and explicit capture validation. They use synthetic input
captures and injected owned transports; the transports fail if these profiles
attempt an unverified MIDI write. No physical support claim follows from them.

Run `./bin/test pure` for the shared suite. Relevant namespaces are
`afterglow.control.codecs.push-3-test`, `afterglow.control.devices.push-3-test`,
`afterglow.control.codecs.mpe-test` and `afterglow.control.devices.mpe-test`.
