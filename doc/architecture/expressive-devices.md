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
within each message family. Capture the physical control addresses. The
temporary encoder modifier can use the factory Accent address described below.

```clojure
(require '[afterglow.control.devices.push-3 :as push])

(def profile
  (push/profile
    {:user-mode? true :expression-mode :poly-aftertouch
     :layout layout :page-id :main
     :encoder-bindings {:level {:param :level}}
     :pressure-param :level}))
```

Tolglow enables operator gestures on dedicated Push 3 connections. A custom
host can use `:operator-gestures? true` with trusted command dispatch. Give the
touch note and turn CC the same logical encoder ID. Hold Accent before touching
the encoder. A temporary edit changes the live value while the encoder is held
and restores the original value on encoder lift, even if Accent was released
first. Shift controls fine adjustment. If the layout has no Shift binding, the
profile uses a captured `:shift` button or the available factory address,
zero-based channel 0 and CC 49. Legacy `:shift` selections and selections of a
Shift button use the Accent default. [Physical Shift mapping](https://github.com/federico-pepe/ableton-push-hack/blob/fe358111493a04062c177bc4c8647ad8b79834e1/docs/push3-button-map.md#L179)

The profile prefers a captured `:accent` button or an unbound capture at the
factory Accent address, zero-based channel 0 and CC 57. It adds that address
only when free and outside the MPE member channels. An address already mapped
to another control or action keeps its existing behavior. For a conflicting
custom layout, set `:temporary-encoder-modifier` to a dedicated captured button
ID. This explicitly assigns that button to temporary edits. [Physical Push 3 mapping](https://github.com/federico-pepe/ableton-push-hack/blob/fe358111493a04062c177bc4c8647ad8b79834e1/docs/push3-button-map.md#L151) · [Button MIDI channel](https://github.com/danielknng/push3-protocol-docs/blob/main/docs/buttons.md#performance) · [User Port routing](https://github.com/federico-pepe/push-tethered-app/blob/5bb4be81a30989a89084617e3180365dacf0be83/docs/protocol/midi-input.md#L27-L35)
The same setup works with configured MPE when the paired touch and turn use
channels outside the zone's member channels. Capture both on fixed channels
before using a temporary modifier. Virtual recordings cover the software
path. Qualification on a physical Push 3 needs MIDI input recorded from the
actual User port, including both edges of the modifier and the encoder touch,
turn and lift.

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

Unannotated semantic names now map automatically: level/dimmer/brightness/
intensity use Pressure; velocity/strike use Strike; pan/azimuth/rotation use
Glide; tilt/elevation/focus/zoom use Slide; lift uses Lift where available.
`:control/semantic` and words in the schema's display `:name` can also express
this intent. Automatic mapping is conservative: unrelated parameters remain
unmapped, and compound values are never flattened implicitly.

The portable policy lives at `[:settings :expressive :devices device-id]`:

```clojure
{:enabled? true
 :auto? true
 :disabled-axes #{:glide}
 :params {:level {:axis :pressure :range [0.15 0.85]
                  :input-range [0.1 0.9] :curve :smoothstep :inverted? false}
          :pattern nil
          :position [{:axis :glide :component 0}
                     {:axis :slide :component 1}]}
 :cues {:wash {:params {:level {:axis :slide :range [0.2 0.6]}}}
        :sweep {:enabled? false}}}
```

The device ID is `:mapping-id` when supplied, otherwise the session ID. Profile
`:mapping-policy`, `:param-mappings` and `:cue-mappings` provide defaults;
persisted device settings and then cue settings override their parameter entries.
Manual entries win over annotations and automatic matches. `nil` or
`{:enabled? false}` disables a parameter. `:auto? false` disables inferred names
while keeping manual and explicit schema annotations. `:enabled? false` disables
expression, **not cue launch or note-off release**. A disabled device remains
disabled even if a cue enables expression. Disabled axes combine across levels.

Scalar mappings support output range, optional input dead-zone endpoints,
inversion and linear/ease-in/ease-out/smoothstep curves. Out-of-range inputs clamp.
Enum and boolean targets use bins/thresholds; custom numeric output ranges do not
apply to them. Integer output ranges must contain an integer. Color, vector and
ordered-range targets require explicit zero-based component mappings; untouched
components keep their current values, and range endpoints cannot cross. Invalid
schema/range/axis targets are withheld with diagnostics. At most 62 parameters
are mapped per plan, leaving command-budget space for release plus a same-note
retrigger. Component mappings are limited to 16 entries per parameter.

`expressive/normalize-config` validates portable settings and normalizes JSON
axis/curve strings. `expressive/policy` resolves precedence; `expressive/plan`
returns actual mappings, schemas, diagnostics and disabled reasons;
`expressive/values` maps one event using current parameter values. These are the
same functions used by the Studio preview and device sessions.

Policies are re-read for each expression event, so overrides and disable switches
apply while a note is held. Active instances use their captured definition,
including a successful hot reload; a registry edit alone cannot change an older
instance's parameter bounds. Pending launches retain their captured schemas and
expression values. Save/load restores policy data only; it does not open MIDI
ports, recreate held fingers or restore transport resources.

## Verification

The shared parity suite passes 297 tests and 3,234 assertions at this checkpoint;
the expressive device namespace covers 12 tests and 79 assertions. These exercise real command admission, channel isolation, typed
mapping, pinned definitions, delayed acknowledgements, held cleanup, restarts,
relative encoders and explicit capture validation. They use synthetic input
captures and injected owned transports; the transports fail if these profiles
attempt an unverified MIDI write. No physical support claim follows from them.

Run `./bin/test pure` for the shared suite. Relevant namespaces are
`afterglow.control.codecs.push-3-test`, `afterglow.control.devices.push-3-test`,
`afterglow.control.codecs.mpe-test` and `afterglow.control.devices.mpe-test`.
