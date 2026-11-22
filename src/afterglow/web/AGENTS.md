# Web application boundary

Read repository and source AGENTS.md files first. See the sibling Tolglow checkout's `docs/architecture/control-and-web.md` for the target design and `docs/product/` for authoring/integration requirements.

- Existing `routes/show_control.clj` combines HTTP, client polling state and show mutations. Migrate through a compatibility adapter; do not create a second definition of cue launch/release, parameter scaling or sequence behavior in routes.
- HTTP/WebSocket/SSE handlers validate and translate commands, then publish acknowledgements and committed snapshots/deltas. Domain reducers must not depend on Ring, sockets, browser timers or mutable client atoms.
- Include schema, show epoch and revisions in new transport contracts. Deduplicate retried command IDs. Resynchronize revision gaps and reject stale epochs; reconnect must not replay past cue launches.
- Keep presentation/session selections distinct from authoritative show state. Ensure browser disconnection cannot leave held cues dependent solely on best-effort page-unload messages.
- Code evaluation and declarative commands are distinct surfaces. Preserve authentication and anti-forgery boundaries; imported fixture data and provider output are not automatically executable Clojure.
- Provider keys and private connection credentials remain in server configuration, never show snapshots or browser bundles. Slow agent calls and streaming chat must not occupy render-loop workers.
- Neovim WASM requires secure-context/shared-memory capability checks and top-level COOP/COEP isolation. Verify headers through the actual middleware stack; an isolated iframe alone is insufficient. The verified tolgrAVen reference is documented in the design.
- Test route validation, duplicate/stale commands, session cleanup and concurrent clients using headless transports. Pair user-visible changes with focused browser checks; do not claim mobile or hardware support from route tests alone.

The embedded JVM UI includes the full Clojure console. Its default address is
`127.0.0.1:16000`. For an iPad on the show LAN, set `AFTERGLOW_WEB_TOKEN` in
the server environment and start with `--web-bind <show-computer-address>` (or
`WEB_BIND`). The browser prompts for username `afterglow` and the configured
password. Use an HTTPS reverse proxy or an encrypted tunnel on shared networks.
A proxy should forward traffic only to a password-protected listener. A supplied
password also applies to local clients. nREPL listens on loopback.
