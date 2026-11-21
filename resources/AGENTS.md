# Web assets, templates and shader resources

Read repository AGENTS.md first. The proposed control/web and simulator contracts are in the sibling Tolglow checkout under `docs/architecture/`.

- Distinguish authored assets from vendored libraries. Do not patch minified dependencies as an implementation strategy. Record licenses/provenance when introducing or extracting libraries, including Neovim WASM assets.
- Existing jQuery/Bootstrap show controls use mouse events and polling. Preserve working behavior while migrating one surface at a time to the common command API; browser scripts must not become an independent show engine.
- Use per-pointer gesture ownership, explicit cancellation and responsive layouts for touch controls. Long-press actions need a discoverable button and accessible list/keyboard equivalent. Keep immediate performance holds separate from edit-mode long presses.
- Cue state needs labels/icons in addition to color. Account for safe-area insets, virtual keyboards, focus restoration and reduced motion. Verify iPad portrait/landscape and phone layouts.
- Sequence playback and authoritative fades run in the show runtime. The browser renders committed state and may preview drafts; a hidden-tab timer cannot own lighting execution.
- A new simulator consumes the shared rig and resolved fixture state. Preserve unit/coordinate conventions, RGBW/intensity/shutter/aim semantics and separation between lighting deadlines and preview quality. Shader changes require reference scenes and performance evidence.
- Lazy-load heavy preview/editor assets. Own and clean up animation frames, workers, observers and event listeners. Stale asynchronous results cannot update replacement editors or shows.
- Neovim's actual worker/SharedArrayBuffer transport requires matching top-level isolation headers. Verify the real WASM editor, unsupported state and worker cleanup; a static imitation is not equivalent.
- Test observable UI behavior with authoritative results, not only rendered markup. Keep protocol/core changes outside this folder and coordinate shared schemas before editing consumers.
