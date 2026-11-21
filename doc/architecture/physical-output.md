# Physical output and fixture management

Afterglow renders DMX buffers, schedules their delivery and speaks to the daemon or node. Each physical connection is explicitly opened by its caller. Closing it releases the socket. A REPL or another application can use the same APIs as Tolglow.

| Namespace | Entry point | Input |
| --- | --- | --- |
| `afterglow.output.artnet` | `open-artnet!` | Destination host and optional UDP port (6454) |
| `afterglow.output.ola` | `open-ola!` | Optional daemon host, TCP port (9010) and deadline settings |
| `afterglow.output.scheduler` | `create` | A sink's `:send!` function and optional monotonic clock |
| `afterglow.rdm.transport` | `open!`, `command!` | OLA endpoint, absolute monotonic deadline and job cancellation |
| `afterglow.rdm.codec` | `typed-command`, `decode-value` | RDM parameter IDs, UID, sub-device and parameter data |

Both DMX sinks accept a map of universe ID to channel bytes via `(:send! sink)`, followed by a logical frame number. Direct Art-Net maps universes 1 through 32768 to Port-Addresses 0 through 32767 and sends every universe of a frame with the same transport sequence. OLA passes universe IDs 0 through 65535 directly to olad. The daemon determines which USB interfaces and ports receive those universes. An explicit `(:close! sink)` closes the connection.

The scheduler hands completed, detached channel buffers to a physical publication clock. Its fallback and interpolation policies come from `afterglow.render.presentation`. A host supplies epoch changes, blackout intent and fixture/channel semantics via `begin-frame!` before painting. It hands the result to `complete!`, starts the clock with `start!` or drives it explicitly with `publish!`, then releases the publisher via `close!`.

RDM runs independently of DMX publication. The connection's `:request!` performs `ForceDiscovery` or `RDMCommand`; `command!` follows timed acknowledgements and reports responder NACKs. The job owner registers the provided close function before connect, closes the connection on cancellation or its deadline, and closes it in `finally`. Tolglow selects devices, associates discoveries with the fixture registry and saves that show configuration.
