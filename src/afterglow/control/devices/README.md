# Connecting control devices

These adapters use the new immutable control model. They are independent of the
legacy `afterglow.controllers` binding system; do not bind both to the same port.
Requiring `afterglow.control.devices.repl` performs no I/O.

```clojure
(require '[afterglow.control.devices.repl :as device])

;; Explicitly enumerate first, then select the intended input/output ports.
(device/ports)

(def push
  (device/open-push-2!
    {:session-id "push-stage-left"
     :model! host-model-snapshot
     :dispatch! host-dispatch-command!
     :now-ms! host-logical-time-ms
     :input-index 2 :output-index 3
     :expected-input-name "Ableton Push 2 User Port"
     :expected-output-name "Ableton Push 2 User Port"
     :device-id 0 :page-id :main
     :native-display? true
     :refresh-ms 40}))

(device/status push)
(device/suspend! push)
(device/resume! push)
(device/reconnect! push)
(device/close! push)
```

The indices, names and MIDI device ID above are examples; use the connected
device's actual values. `host-dispatch-command!` returns the common command result
with `:ack`, synchronously. The host serializes model updates. The session supplies
unique command IDs, source/session identity, epoch and current logical time.

Push 2 sequentially reads all 128 palette entries before changing LEDs, then
enters user/poly-pressure mode. Pads launch/toggle cues; cues with `:held true`
or `:launch-mode :held` release on note-off or disconnect. Numeric parameters of
the selected instance map to encoders 71–78 in sorted parameter-key order; master
uses encoder 79. Arrow buttons move the page viewport by eight cells, button 85
toggles blackout, and User toggles suspend/resume. LED changes use acknowledged
batches. The display shows page, transport/master, selected parameters and labels.
This is a working core adapter, not complete feature parity with every old overlay.

Native display is optional and requires Wayang on the application classpath.
Wayang exposes one global display, so a second native display lease is rejected.
MIDI sessions and injected displays are independent. On suspend, held gestures
release, palettes restore, display ownership is relinquished and feedback stops;
MIDI input remains solely to detect User/resume. Explicit close also releases
ports. Reconnect invalidates old callbacks and reacquires resources. Idle
backlight queries detect loss of response. Palette timeout or repeated missing
LED acknowledgements fail the session, release held instances and close its
resources; status retains the failure code. No physical hardware verification
has been performed in the headless test environment.

For generic MIDI, pass `:bindings` to `open-midi!`. Each binding has an `:event`
partial match and either a common `:command` template with scaling options or a
`:cue-id` and `:launch-mode`. For example:

```clojure
{:event {:type :control-change :controller 7}
 :command {:op :master/set}
 :output-range [0 1]}

{:event {:type :note-on :note 60}
 :cue-id :red-bloom :launch-mode :held}
```

`open-osc!` accepts an explicit `:port` and `:mappings`, such as
`{"/master" {:op :master/set}}`. It lazily acquires the existing Overtone OSC
implementation and disables Zeroconf registration. `open-sensor!` takes an
injected `:transport` and normalized input maps. A sensor binding may use
`:threshold` for edge-triggered held cues, or ordinary scaling for parameters.
The robot-duck telemetry can enter through this interface when its transport and
coordinate/timestamp conventions are known.

`open-push-3-midi!` requires explicit mappings verified for the actual device and
mode. It uses generic MIDI only. Push 3 protocol discovery, display and standalone
support are not implemented, and no Push 2 protocol is inferred.

For embedding/testing, inject transports instead of indices: MIDI/input transport
has `:open! [receive!] -> handle`, `:send! [handle messages]` and `:close! [handle]`;
display has `:open! []`, `:render! [handle view]` and `:close! [handle]`. Optional
`:schedule! [refresh!]` returns a cancellation function. Direct session/profile
construction has no default scheduler; the Push REPL facade owns one daemon
feedback worker unless `:schedule! nil` delegates cadence to the host.
