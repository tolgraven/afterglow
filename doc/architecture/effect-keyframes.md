# Predictive musical effect keyframes

A pure lighting effect can declare how often its full function should run. At the start of a segment Afterglow evaluates it on the instance's current clock and a private future clock. Each intervening frame interpolates the native assignments before layer composition, response, aim conversion and DMX quantization. At the boundary it reuses the preceding segment's final displayed value and computes one new future endpoint.

```clojure
{:keyframes {:interval {:beats 1/2}
             :curve {:type :cubic-bezier :points [0.25 0.1 0.25 1.0]}
             :progress {:mode :offset :variable [:audio :bass]}}}
```

Choose one interval unit from `:beats`, `:bars`, `:phrases` and `:ms`. Bars and phrases use the current meter. Both current and projected contexts carry coherent flat and nested transport clocks. A missed evaluation preserves the musical grid. Tempo, meter, parameter, definition and rig changes trigger a fresh prediction.

Progress normally advances from zero to one. An authored numeric parameter or path under show `:variables` can replace the clock fraction or add an offset. The source can increase or decrease each frame. Missing or nonfinite inputs use clock progress for replacement and zero for offsets. The easing function samples the bounded fraction. A spring or a Bézier with an elevated handle can overshoot in native coordinates or HDR emission. Normalized controls retain their physical bounds. At rollover an externally driven segment starts from its last displayed value, even if a large new audio sample just arrived. An unmodulated segment reaches its time-based target at the boundary.

## Sampling show variables

When a compiled sampler reads external show variables, declare their full paths on the compiled step. For example, a material controlling a dimmer can read the current bass level directly from the frame.

```clojure
(require '[afterglow.runtime.keyframes :as keyframes])

(def bass-path [:variables :audio :bass])

(def bass-dimmer
  (vary-meta
   (keyframes/predictable
    (fn [{:keys [frame] :as ctx}]
      (assoc ctx :assignments
             [{:target-id :wash :attribute :dimmer :value (get-in frame bass-path 0.0)}])))
   assoc ::keyframes/variable-paths #{bass-path}))
```

Supply a persistent set or vector of paths. Each path starts with `:variables` and addresses at least one key or index below it. Collect these paths once when compiling the program. The runtime combines them with direct variable keys in the definition's `:blocks` and reads the leaves from the same resolved frame the sampler sees. `keyframes/with-inputs` carries the declaration through input middleware, including when the compiled step has a separate forecast sampler.

A changed leaf resamples both endpoints immediately. Other variable updates retain the forecast and its endpoint observations. Removing a leaf and assigning it `nil` are distinguishable. Saved windows retain the sampled values. On restoration the live compiled step supplies its dependency paths again.

## Kernel and host

* A compiler marks its safe step with `afterglow.runtime.keyframes/predictable`. A separate numeric sampler may accompany a deferred GPU step. Certified callbacks must leave state, completion and intents untouched, use immutable inputs and write continuous native assignments in a stable order. Discrete functions, timed lifecycle transitions and user callbacks without that declaration execute on the live clock.
* Return the preceding committed result's `:keyframes` in the next input frame. Each instance owns its origin, target and current result. Sibling evaluations can run in parallel. Only committed outputs carry windows forward.
* The host can supply `:keyframe-intervals {instance-id {:ms 100}}`. The engine caps the adaptive request at the effect’s optional `:max-interval`, then uses the longer of the authored interval and that bounded request. An optional `:measure-effect` callback receives instance ID, eligibility and a zero-argument computation. It wraps expensive samples and ordinary effect evaluations, so interpolated frames do not bias the controller's cost estimates.
* `keyframes/inspect` with an instance window, target ID and attribute returns both clocks, eased progress and that field's origin, target and result. Omit the field to inspect timing only. Native arrays remain read-only. Use `keyframes.storage/freeze` and `restore` for portable Transit snapshots. Dense numeric endpoints use binary doubles in network order.
* A recoverable error evaluating a forecast falls back to real samples through that segment. The inspector marks the window with `:forecast-failed?`. If the error actually occurs on the live timeline the ordinary per-effect fault event and quarantine handle it. A direction chord crossing zero, or an aim chord crossing its own fixture, also uses real samples so the head can follow its curved path. Disabling HDR reevaluates the current endpoint under the new output limits. Worker cancellation and VM failures propagate to the owner.

Geometry validation runs when a predictive interval builds its two endpoints.
Aligned batch outputs retain their original arrays throughout this check. For
each three-component aim target, the check subtracts the corresponding fixture
position before comparing the two directions. A direction field already uses
the emitter as its origin. A singular chord takes the live path, including
parallel vectors of unequal length under an overshooting curve. If endpoint
target order changes, alignment first recovers a common assignment order.

All workers checking absolute aim on the same frame share one fixture-position
lookup. The first aim request builds it from that frame's frozen fixture vector.
Later intervals reuse it while the vector is identical. A replacement rig gets
a fresh lookup, including when the fixture IDs stayed the same and only
positions changed. Relative direction and color require no position index.
The committed keyframe map carries the lookup as runtime metadata. When its
last window ends the reference is released. Checkpoints contain only the
saved native values and clock data.
