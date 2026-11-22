# Gain and spatial highlight spill

Run overdrive on the blended, linear light fields while they still carry values above full output. The fixture encoder then applies master, blackout, RGBW policy, inversion and DMX quantization. Movement, shutter and other function channels retain their authored values.

```clojure
(frame/resolve-contributions patch blocks
  {:hdr {:fixture-ids [:center :left :right]
         :gain 1.5 :max-excess 1
         :spill 0.8 :radius 1.2 :falloff :smoothstep
         :white-mix 0.7 :spill-white-mix 0.4}})
```

- **Gain.** A cue can start with `:system {:gain 1.5}`. A running instance accepts `{:op :instance/gain-set :instance-id id :value 1.5}` through ordinary control dispatch. Its input parameters and opacity remain independently editable. When a cue writes both a dimmer and color on a target, its dimmer carries the gain once. The color carries gain when that cue writes only emitters. Later opaque layers can still replace these contributions.
- **Scope.** `:fixture-ids` selects sources and receivers for the global gain, per-cue and per-instance gains, whitening and spill. Omit the key to use the entire patch. `:cue-gains` and `:instance-gains` accept maps keyed by IDs. Explicit `:source-gains` multiply the final composed light of the addressed fixtures, including those outside the selected scope. This lets a performance controller independently manage its sources.
- **Excess.** An emitted red level of 1.21 becomes full red with 0.21 available for highlight effects. `:max-excess` limits each visible color component's contribution. A dark dimmer or a profiled closed shutter cannot shed visible light into its neighbors. UV has no visible spill.
- **Spatial falloff.** `:radius` is the sphere radius in metres around each head's patched world position. `:linear` fades in proportion to distance, `:quadratic` squares the remaining fraction and `:smoothstep` eases at both ends. `:spill` controls the strength of the light reaching each receiver. The renderer computes every source's excess from the same original frame, so a receiver cannot bounce received spill onward within that frame.
- **White highlights.** `:white-mix` blends saturated source highlights toward white in proportion to their excess. `:spill-white-mix` does the same on a receiving head in proportion to incoming spill. RGB heads mix their primaries. A single-color or fixed-color lamp can change only its output level. For example, a red highlight spilling onto a blue receiver can push the receiver from purple toward white while the spill is strongest.

Values for gain, radius and maximum excess must be finite and nonnegative. The mix amounts and spill strength range from zero to one. Supply new resolved values each frame to animate these controls. An empty `:hdr {}` accepts and clamps positive overrange light with unit gain and zero whitening or spill. Omitting HDR retains the ordinary unit-range contract. Setting an instance’s gain to a value other than one enables overdrive and source whitening on its rendered frame. Explicit HDR settings take precedence.

The rich preview, compact preview, movement packing and DMX buffers share this stage. Spatial spill is a show effect measured against head positions. The venue model separately handles reflected light and fog.

Run `lein run -m afterglow.bench-hdr` for owner CPU and allocation on 2,048 RGB heads along a strip. Every tenth pixel can produce excess and the spill radius reaches five pixel spacings. The benchmark measures frame resolution and packing with both rich color math and DMX output covered by independent tests. It omits packet transmission, fixture response time and venue optics.
