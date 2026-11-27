# Reusing pure effect results

A code effect can bind its input paths and receive only the data at those paths.
Build the step once when compiling its definition. The engine can evaluate it
on an effect worker.

```clojure
(require '[afterglow.runtime.reuse :as reuse])

(def sweep
  (reuse/step
    {:pure? true
     :inputs [[:frame :beat] [:instance :params :gain]]}
    (fn [{:keys [frame instance]}]
      (let [beat (:beat frame)
            gain (get-in instance [:params :gain])]
        {:assignments [{:target-id :spot :attribute :dimmer
                        :value (* gain (/ (inc (Math/sin (double beat))) 2))}]}))))
```

Clock and subscription reads are explicit. Declare `[:frame :time-ms]` for
milliseconds, `[:frame :beat]` for a musical clock, or a path under
`[:frame :variables]` for show data. A state transition declares the
`[:state ...]` values it reads. Bind a layer transform with `reuse/evaluator`
and include each input it takes from the preceding layer, such as its color
or world-space direction. Reads of undeclared paths see absent values.
When a declared parent path contains a map the callback receives the entire map.
Results may depend on immutable data captured at compilation, such as a rig.
Rebind the calculation when its implementation, definition or captured rig changes.

An ordinary function runs each time. A declaration with `:pure? true` is the
author's assertion that the injected values determine the returned data.
Use explicit inputs for random values, sensor samples and time. Side effects
belong at the publication boundary. `:intents` returned by a pure step still
apply once per successful frame, even on a cache hit. System opacity, release
and downstream blending continue to use their current inputs.

Each binding retains the last successful calculation. `:max-values` defaults
to 65,536 nodes and primitive array elements per input or output. Missing
values differ from explicit nil. Input equality distinguishes numeric types,
decimal scale and signed zero. Bindings support plain value semantics for maps
with keyword/string keys, vectors and scalars. Mutable or opaque inputs, larger
payloads and unsupported results pass through without retention. Each caller
owns its primitive output arrays by default: a miss retains a copy and a hit
returns another copy. Exceptions leave the last successful entry intact.
Concurrent misses may evaluate independently. Workers do not wait on each
other to compute a miss.

`:shared-outputs? true` removes both copies. The calculation must return fresh
arrays, and the caller and every later reader must treat them as read-only.
The binding retains the returned value itself and returns that same value on a
hit, possibly to several effect workers in one frame. A caller that needs a
different value, such as an envelope-scaled level, writes a new array it owns.
Tolglow's typed batch compiler binds its evaluated fields this way. A stopped
transport therefore reuses one retained field per group without allocating.

The GPU session owns a separate binding for each resident numeric program. Its
inputs are the actual captured uniform values, after conversion to float32.
Equal uniforms and the same uploaded positions reuse the completed readback.
Program eviction releases its value. Submission still passes through normal
queue admission, cancellation and the frame deadline. The session's `:draws`
counter counts completed nonempty native evaluations.
