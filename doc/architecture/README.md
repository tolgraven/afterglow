# Architecture migration

The cross-repository program lives in the sibling tolglow checkout:

* [Documentation index](../../../tolglow/docs/README.md)
* [Current code survey](../../../tolglow/docs/codebase-survey.md)
* [Functional runtime](../../../tolglow/docs/architecture/functional-runtime.md)
* [Rendering and acceleration](../../../tolglow/docs/architecture/rendering.md)
* [Shared controls and web](../../../tolglow/docs/architecture/control-and-web.md)
* [Work ledger](../../../tolglow/docs/work-items.edn)

These relative links assume both repositories are siblings. If viewing this
repository alone, clone `https://github.com/tolgraven/tolglow` beside it and use
the architecture change there; the documentation may not yet be on its default branch.

This change adds characterization tests and an experimental pure runtime; it
does not replace the live engine or device drivers. The old `IEffect` API, show
atoms and render loop remain. The new kernel requires callers to supply pure
steps and any worker mapper, and returns data without publishing a frame.

Run `./bin/test pure` or `./bin/test legacy` with Clojure CLI and Java 17 or 21.
The legacy lane reads dependencies from `project.clj`, skipping build plugins,
documentation generation and app startup. It uses released Beat Link 8.0.0
because the historical 8.0.0-SNAPSHOT no longer resolves. That exception is
test-only and must be addressed separately when restoring full application builds.
