# Render error provenance

`afterglow.render.frame/resolve-contributions` accepts optional `:source` data on
each ordered contribution block. The show engine normally supplies an immutable
map identifying its instance, effect, effect revision and cue:

```clojure
{:kind :assignments
 :source {:instance-id "moving-1" :effect-id :sweep :effect-version 3 :cue-id :left}
 :assignments [{:target-id :head :attribute :aim :value [1.0 2.0 3.0]}]}
```

When block validation or assignment/batch blending fails, the renderer throws
`ExceptionInfo` whose `:effect-source` is that exact source value. The original
exception is retained as cause; its message, ex-data and `:type` remain available.
Unattributed calls preserve their existing exceptions. VM errors are not caught.
Fixture-patch, render-option and malformed movement-history errors remain global
failures and receive no effect source.

Geometry is validated after all contributions have been blended. A zero-distance
aim that is replaced later by a valid aim is therefore allowed. If the final aim
is invalid, its source is the last positive-opacity aim write. Aim takes
precedence over direction; direction supplies the source only when no aim exists.
Zero-opacity writes do not replace provenance, and an unattributed replacement
clears an earlier source. Partial-opacity cancellation is assigned to the last
contributing write that produced the final invalid geometry.

The renderer does not quarantine effects or commit output. It returns no partial
frame on failure. The host can use the source identity to reject one already
evaluated effect result, then resolve the remaining results without evaluating
healthy effects again. Unknown/global failures remain whole-frame failures.

Source tracking shares the existing validation and merge passes. Dense pixels
retain typed arrays and per-block provenance; no metadata is copied into every
pixel assignment. General target histories use private transient maps as before,
with source slots only updated for geometric attributes. Sources do not appear
in returned fixture values or compact preview fields.

The hardware-free regression suite covers dense and general failures, overflow,
exact-arithmetic exceptions, retained cause/type, ordinary and typed geometry,
opacity and replacement order, global errors and unchanged valid output. This
contract does not establish hardware recovery behavior; the host integration is
verified separately.
