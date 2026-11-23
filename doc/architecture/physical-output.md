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

RDM runs independently of DMX publication. The connection's `:request!` performs `ForceDiscovery` or `RDMCommand`; `command!` follows timed acknowledgements and reports responder NACKs. The job owner registers the provided close function before connect, closes the connection on cancellation or its deadline, and closes it in `finally`. Tolglow selects devices, associates discoveries with the fixture registry and saves that show configuration.

## Direct RDM over Art-Net

Choose `:transport :art-net` to use one known Art-Net 4 gateway. OLA remains the default and connects to olad over TCP. The direct driver sends unicast UDP to the configured IPv4 address. Both gateway and local UDP ports default to 6454. Use `:bind-host` to select an interface when multiple processes or networks share a computer. A physical gateway normally replies on port 6454. Set `:local-port 0` only for a simulator that replies to the sender’s port.

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

`"GetUIDs"` and `"ForceDiscovery"` with `:full? false` request the cached table. `:full? true` sends AtcFlush once, which restarts physical RDM discovery on the selected universe. The driver accepts a complete table of up to 512 unique devices, including a confirmed empty table. Missing blocks or TodNak can trigger up to two cached reads. After a full discovery these reads allow announcements from a slow scan through the job deadline. A partial or inconsistent table fails the operation.

`rdm/command!` handles timed acknowledgements through QUEUED_MESSAGE. A GET with an overflow reply reads additional fragments up to 64 KiB. Each ArtRdm exchange checks both UIDs, transaction number, port-address and reply identity. Timeout after a SET leaves its physical outcome unknown. Read the parameter back before deciding whether to send it again.

The protocol layout follows the published Art-Net 4 specification, revision 1.4dp, pages 83–93. Packet-vector and UDP loopback tests run in `lein test-pure`. Verification on a physical gateway is still pending. [Art-Net 4 specification](https://art-net.org.uk/downloads/art-net.pdf)
