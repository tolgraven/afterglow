# Physical DMX output

Keep socket ownership, output clock and wire formats here. Test ArtDMX on UDP loopback, OLA on TCP loopback and presentation against an injected monotonic clock. Use detached channel buffers and preserve universe numbering across clients.

Waiting, blackout and shutdown packets use the compiled physical fog-off bytes.
Keep retiring pumps off on later packets, including when other devices still
occupy their old universe. A newly claimed slot or fixture footprint takes
precedence immediately. Keep renderer buffers and cached idle templates private
to their owners.
