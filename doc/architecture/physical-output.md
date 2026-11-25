# Physical output and fixture management

Afterglow renders DMX buffers, schedules their delivery and speaks to the daemon or node. Each physical connection is explicitly opened by its caller. Closing it releases the socket. A REPL or another application can use the same APIs as Tolglow.

| Namespace | Entry point | Input |
| --- | --- | --- |
| `afterglow.output.artnet` | `open-artnet!` | Destination host and optional UDP port (6454) |
| `afterglow.output.ola` | `open-ola!` | Optional daemon host, TCP port (9010) and deadline settings |
| `afterglow.output.scheduler` | `create` | A sink's `:send!` function and optional monotonic clock |
| `afterglow.rdm.transport` | `open!`, `command!` | OLA or Art-Net RDM endpoint, absolute monotonic deadline and job cancellation |
| `afterglow.rdm.codec` | `typed-command`, `decode-value` | RDM parameter IDs, UID, sub-device and parameter data |

Both DMX sinks accept a map of universe ID to channel bytes via `(:send! sink)`, followed by a logical frame number. Direct Art-Net maps universes 1 through 32768 to Port-Addresses 0 through 32767 and sends every universe of a frame with the same transport sequence. OLA passes universe IDs 0 through 65535 directly to olad. The daemon determines which USB interfaces and ports receive those universes. An explicit `(:close! sink)` closes the connection.

The scheduler hands completed, detached channel buffers to a physical publication clock. Its fallback and interpolation policies come from `afterglow.render.presentation`. A host supplies epoch changes, blackout intent and fixture/channel semantics via `begin-frame!` before painting. It hands the result to `complete!`, starts the clock with `start!` or drives it explicitly with `publish!`, then releases the publisher via `close!`.

Waiting, scheduler blackout and host shutdown packets use the patch's physical
off bytes for fully inverted dimmer and emitter channels and configured fog
endpoints. Coarse/fine off bytes can span universes. Partially inverted
emission and other idle channels start at zero. Retirement preserves the
off bytes at withdrawn addresses until a new channel or reserved fixture
footprint claims the slot.

## Sample time and physical publication

At 40 Hz the wire has a nominal slot every 25 ms. Pass a render callback to
`(scheduler/start! owner 25 render!)` to run both clocks from one monotonic
origin. Each ticket carries its slot number, deadline, planned start, actual
start and reserved lead in milliseconds. Freeze external controls when the
callback acquires the show, then evaluate the *deadline's* musical position
with that snapshot. Pass the ticket to the six-argument `begin-frame!`.
Completions can arrive early. The sender first makes them visible when the
corresponding physical time arrives. Pure `afterglow.output.timeline` owns
the scheduling rules and has no device or thread dependencies.

The first render starts a period ahead. Later starts reserve the larger of the
latest cost and the 90th percentile over the last 24 observed render costs,
plus a jitter allowance of 10% or 0.4 ms, whichever is larger. It also reserves the recent upper wake
delay over the same window, capped at one period. A wake after the planned
deadline updates this estimate even though the producer skips that slot. A single outlier
can raise the cost estimate to a full period. Two successive long renders can
raise it further. For example, seven milliseconds of observed work reserves
7.7 ms. The next 50 ms output then begins sampling around 42.3 ms. An operating
system wake and the host's show lock can delay that start. The producer chooses
an achievable future slot after a slow render. The sender also skips missed
slots following a late wake or a blocked transport.

`:direct` and `:hold-fade` discard a newly completed sample that missed its
scheduled deadline. A held source may still drive the configured fallback.
`:buffered-interpolation` accepts completion within the configured presentation
latency and blends continuous channels using the delayed timeline. A fractional
latency can put that target between physical slots. A valid sample remains
available through the first slot that can present it as a lower endpoint. Function
channels retain the lower sample. If either endpoint rejected an edge-tracking
follower, strictly intermediate samples copy that fixture's dimmer and emitter
bytes from the rejected endpoint. If both rejected the fixture, the lower sample
supplies the bytes. This preserves the cut through the transition and keeps the
ordinary interpolation of movement and unrelated fixtures. Exact endpoints retain
their original bytes. A patch, blackout or epoch change fences
previously prepared packets. Supply a stable `:timeline-id` in the ticket and
change it on transport seeks or playback changes to retire old buffered output. High refresh-rate local UI animation keeps its
own presentation clock.

Inspect `(scheduler/status owner)` for the following measurements.

| Measurement | Meaning |
| --- | --- |
| `:render-timing :last` | Planned release and deadline, actual start, input capture start, ready and finish, render cost and time remaining at handoff. Hosts can supply show time and beat. |
| `:render-timing :on-time`, `:renders`, `:skipped` | Rendered samples ready by their nominal slot, attempts made and intervening slots the producer skipped. `:missed-wakes` counts releases that arrived after their deadline. |
| `:output-timing` | Most recent physical slot, nominal time, actual publisher start and completion, source sample time and frame ID. The timestamps immediately before and after the sink call distinguish transport from packing. `:source-input-age-ms` gives the age of the lower source’s input capture when sent. |
| `:missed-render-deadlines`, `:expired-at-publication`, `:skipped-output-slots` | Renders completed outside their policy window, queued samples waiting past their policy window in the current generation, and elapsed slots the sender skipped. |

RDM runs independently of DMX publication. The connection's `:request!` performs `ForceDiscovery` or `RDMCommand`; `command!` follows timed acknowledgements and reports responder NACKs. The job owner registers the provided close function before connect, closes the connection on cancellation or its deadline, and closes it in `finally`. Tolglow selects devices, associates discoveries with the fixture registry and saves that show configuration.

## Direct RDM over Art-Net

Choose `:transport :art-net` to use one known Art-Net 4 gateway. OLA remains the default and connects to olad over TCP. The direct driver sends unicast UDP to the configured IPv4 address. Both gateway and local UDP ports default to 6454. Use `:bind-host` to select an interface when multiple processes or networks share a computer. Applications can validate form or EDN options without network I/O through `afterglow.rdm.artnet/configuration`. A physical gateway normally replies on port 6454. Set `:local-port 0` only for a simulator that replies to the sender’s port.

```clojure
(require '[afterglow.rdm.transport :as rdm])

(let [config {:transport :art-net :host "192.0.2.10"
              :controller-uid controller-uid
              :bind-index 1 :physical-port 1 :timeout-ms 2000}
      deadline (+ (System/nanoTime) 30000000000)
      connection (rdm/open! config deadline register-close!)]
  (try
    ((:request! connection) "GetUIDs" {:universe 257})
    (finally ((:close! connection)))))
```

Supply the controller’s unique, assigned RDM UID for GET and SET. Discovery alone can omit it. `register-close!` is the job owner’s callback for closing the UDP socket on cancellation or deadline. Submit successive operations serially on that connection. A socket bound to the same address and UDP port requires exclusive access.

Universe 257 maps to Art-Net Net 1, Sub-Net 0, Universe 0. Discovery selects the responding gateway's ArtTodData BindIndex and Port fields. `:physical-port` is the 1–4 port index *within that bound node*, as reported by ArtPollReply. `:bind-index` and `:physical-port` both default to 1. Configure 0 explicitly for a gateway reporting a zero BindIndex. ArtRdm itself addresses the universe and responder UID.

`"GetUIDs"` and `"ForceDiscovery"` with `:full? false` request the cached table. `:full? true` sends AtcFlush once, which restarts physical RDM discovery on the selected universe. The driver accepts a complete table of up to 512 unique devices, including a confirmed empty table. Missing blocks or TodNak can trigger up to two cached reads. After a full discovery these reads allow announcements from a slow scan through the job deadline. A partial or inconsistent table fails the operation. Each new discovery discards datagrams already queued on the session. ArtTodData has no transaction number, so a delayed announcement arriving after the request cannot be distinguished from a response from the same physical port.

`rdm/command!` handles timed acknowledgements through QUEUED_MESSAGE. A GET with an overflow reply reads additional fragments up to 64 KiB. Each ArtRdm exchange checks both UIDs, transaction number, port-address and reply identity. Timeout after a SET leaves its physical outcome unknown. Read the parameter back before deciding whether to send it again.

The protocol layout follows the published Art-Net 4 specification, revision 1.4dp, pages 83–93. Packet-vector and UDP loopback tests run in `lein test-pure`. Verification on a physical gateway is still pending. [Art-Net 4 specification](https://art-net.org.uk/downloads/art-net.pdf)


A scheduled publication checks the clock again after it has packed the
transport buffers. If the next nominal deadline has passed, it leaves the
physical output on its previous sample and records `:expired-before-send`.
Hosts can supply `:prepare-safety-output` to correct the last successfully
sent channel values when a normal packet expires. It receives detached
buffers and source metadata, including any immutable `:safety-state` from
the completed source. A failed handoff marks the wire uncertain until a
complete send succeeds. If the first handoff failed, the safety hook receives
the current idle values. It also receives whether the source predates the
current publication gate and the DMX patch used for the last successful
handoff, including any successful safety handoff. Corrected buffers use
the current gate's patch. Return `nil` when no cutoff is needed.
The safety send leaves the expired frame pending for its usual admission
rules and reports `:safety-output?` and `:safety-publications`.
The next slot can still consume a newer completion that arrived during
packing. Buffered upper endpoints remain available through their own
delayed publication opportunity. An unseen expired endpoint cannot become
the new held source. An explicit blackout goes straight to the sink even
when packing its idle values took a full period.


The publisher snapshots a bounded, three-entry completion mailbox. A
successful send acknowledges only entries in its snapshot. Newer arrivals
survive. Closing the mailbox fences workers still freezing output. The
publisher also retains the original lower source from its last physical
send so three future samples cannot displace a held level, fade origin or
buffered interpolation endpoint.


Hosts can supply `:prepare-output` to apply final channel corrections before
the sender checks its deadline. This includes retired-fixture output and fog
cutoffs. A sink call may itself span a scheduling interruption. The next
publication leaves at least half a period after the preceding call returned
or threw.
A capture sink can timestamp its own entry to measure the remaining gap
between application admission and actual delivery.
