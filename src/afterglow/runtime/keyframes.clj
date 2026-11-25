(ns afterglow.runtime.keyframes
  "Predict continuous native effect outputs on their private musical clock."
  (:require [afterglow.render.easing :as easing]
            [afterglow.runtime :as runtime]
            [afterglow.runtime.faults :as faults]
            [afterglow.runtime.keyframes.observations :as observations]
            [afterglow.runtime.keyframes.values :as values]
            [afterglow.runtime.reuse :as reuse]
            [afterglow.time :as time]))

(defn predictable
  "Declare a stateless continuous sampler. No lifecycle, emitted events, external
  effects, frame-count dependence or deferred native jobs are allowed. An optional
  separate sampler can use the numeric CPU backend on a predictive evaluation."
  ([step] (predictable step step))
  ([step sampler] (vary-meta step #(assoc (dissoc % ::time-invariant) ::sampler sampler))))

(defn time-invariant
  "Certify that a predictable step and its interpolant produce identical
  native fields, including their numeric representation, for every clock
  under one input signature. Automatic keyframes can reuse one validated
  read-only sample at both endpoints. Authored windows retain normal sampling.
  The step must not expose clock-specific observations."
  [step]
  (vary-meta (predictable step) assoc ::time-invariant {:sampler step}))

(defn predictable? [step] (boolean (::sampler (meta step))))

(defn- reactive-inputs [context paths]
  (let [inputs (select-keys (get-in context [:frame :reactive-inputs]) paths)]
    (when (= (count inputs) (count paths))
      (when-not (reuse/immutable-inputs? inputs)
        (throw (ex-info "Declared reactive inputs must be bounded immutable values" {})))
      inputs)))

(defn- reactive-contributions [calculate inputs hdr?]
  (let [result (calculate inputs)]
    (when-not (and (map? result) (every? #{:assignments :contributions} (keys result))
                   (vector? (:assignments result [])))
      (throw (ex-info "A dependency-driven effect must return only native contributions" {})))
    (let [blocks (:contributions (runtime/append-contributions (merge {:assignments []} result) []))]
      (if-let [retained (reuse/retained-output blocks)]
        (values/reactive-blocks retained hdr?)
        (throw (ex-info "Dependency-driven output must fit the bounded native value schema" {}))))))

(defn dependency-driven
  "Bind a pure effect to named values in the owner's :reactive-inputs frame map.
  The calculation receives only those values, plus any immutable data captured
  at compile time, and returns :assignments and/or :contributions. Optional
  :transition {:beats n} moves from the last committed result on the private
  beat clock. Missing dependencies produce no output until they are available."
  [{:keys [inputs transition] :as options} calculate]
  (when-not (and (map? options) (every? #{:inputs :transition} (keys options))
                 (fn? calculate) (vector? inputs) (seq inputs) (every? keyword? inputs)
                 (= (count inputs) (count (distinct inputs)))
                 (or (nil? transition)
                     (and (map? transition) (= #{:beats} (set (keys transition)))
                          (time/finite-number? (:beats transition)) (pos? (:beats transition)))))
    (throw (ex-info "Dependency-driven effects require named inputs and an optional positive beat interval"
                    {:options options})))
  (with-meta
    (fn [context]
      (if-let [captured (reactive-inputs context inputs)]
        (runtime/append-contributions context (reactive-contributions calculate captured (get-in context [:frame :hdr?])))
        context))
    {::reactive {:options options :calculate calculate}}))

(defn dependency-driven? [step]
  (boolean (::reactive (meta step))))

(defn with-inputs
  "Preprocess current and projected contexts through the same input middleware.
  Preserve time-invariance only for a transform that leaves certified inputs
  untouched at current and projected clocks. Check the current input on
  every frame so a later override can restore the ordinary sampling path."
  ([step transform] (with-inputs step transform {}))
  ([step transform {:keys [preserve-time-invariance?]}]
   (let [run (comp step transform)
         info (meta step)
         sample (::sampler info)
         invariant (when preserve-time-invariance? (::time-invariant info))
         reactive (::reactive info)]
     (if info
       (with-meta run (cond-> (dissoc info ::time-invariant)
                        sample (assoc ::sampler (comp sample transform))
                        invariant (assoc ::time-invariant
                                         (update invariant :prepare #(if % (comp % transform) transform)))
                        reactive (assoc ::reactive
                                        (update reactive :prepare #(if % (comp % transform) transform)))))
       run))))

(defn- positive-duration? [duration]
  (and (empty? (time/validate-duration duration)) (pos? (val (first duration)))))

(defn validate! [{:keys [curve progress] :as options}]
  (when-not (and (map? options) (every? #{:interval :max-interval :curve :progress} (keys options))
                 (or (contains? options :interval) (contains? options :max-interval))
                 (every? positive-duration? (vals (select-keys options [:interval :max-interval]))))
    (throw (ex-info "Keyframes need a positive musical or millisecond interval" {:keyframes options})))
  (easing/sample (or curve :linear) 0.5)
  (when (and (some? progress)
             (not (and (map? progress) (#{:replace :offset} (:mode progress))
                       (or (and (= #{:mode :param} (set (keys progress))) (keyword? (:param progress)))
                           (and (= #{:mode :variable} (set (keys progress))) (vector? (:variable progress))
                                (seq (:variable progress)))))))
    (throw (ex-info "Keyframe progress needs a mode and one parameter or variable" {:progress progress})))
  options)

(defn- duration [{:keys [interval max-interval]} adaptive clock]
  (let [normalize #(time/normalize-duration % (:meter clock))
        ms #(time/estimate-ms % (:bpm clock))
        authored (when interval (normalize interval))
        requested (when adaptive (normalize adaptive))
        limit (when (and adaptive max-interval) (normalize max-interval))
        bounded (if (and limit (>= (ms requested) (ms limit))) limit requested)]
    (cond (nil? bounded) authored
          (nil? authored) bounded
          (> (ms bounded) (ms authored)) bounded
          :else authored)))

(defn- clock-at [clock unit coord]
  (let [bpm (:bpm clock) now (time/coordinate clock unit) diff (- coord now)
        ms (if (= unit :ms) diff (* diff (/ 60000.0 bpm)))
        beat (if (= unit :beats) diff (* ms (/ bpm 60000.0)))]
    (-> clock (update :time-ms + ms) (update :beat + beat))))

(defn- future-context [ctx clock]
  (let [frame (:frame ctx) delta (- (:time-ms clock) (:time-ms frame))]
    (assoc ctx :frame (cond-> (-> frame (merge clock) (assoc :delta-ms delta)
                                  (update :transport merge clock))
                        (:transport-clock frame)
                        (update :transport-clock #(-> % (update :time-ms + delta)
                                                     (update :beat + (- (:beat clock) (:beat frame)))))))))

(defn- amount [ctx progress curve-fn phase]
  (let [source (cond (:variable progress) (get-in (get-in ctx [:frame :variables]) (:variable progress))
                     (:param progress) (get (get-in ctx [:frame :keyframe-params (:effect-id ctx)]) (:param progress)
                                           (get-in ctx [:instance :params (:param progress)])))
        input (case (:mode progress)
                :replace (if (time/finite-number? source) source phase)
                :offset (+ phase (if (time/finite-number? source) source 0))
                phase)]
    (curve-fn (max 0 (min 1 input)))))

(defn- sample-window [window ctx options now]
  (let [{:keys [start end origin target]} window
        curve-fn (or (::ease (meta window)) (easing/evaluator (:curve options :linear)))
        progress (amount ctx (:progress options) curve-fn (/ (- now start) (- end start)))]
    (assoc (vary-meta window assoc ::ease curve-fn)
           :progress progress
           :result (if (and (::constant-window (meta window)) (identical? origin target)) origin
                       (values/blend origin target progress (get-in ctx [:frame :hdr?]))))))

(defn- started [prior unit now span same?]
  (if (and same? (= unit (:unit prior)) (>= now (:end prior)))
    ;; Preserve the original beat grid across a slow frame or a skipped period.
    (+ (:end prior) (* span (inc (long (Math/floor (/ (double (- now (:end prior))) span))))))
    (+ now span)))

(defn- call [ctx eligible? f]
  (if-let [measure (get-in ctx [:frame :measure-effect])]
    (measure (:effect-id ctx) eligible? f)
    (f)))

(defn- variable-path? [path]
  (and (vector? path) (< 1 (count path)) (= :variables (first path))))

(defn- variable-dependencies [declared bindings prior]
  (cond
    (and (nil? declared) (nil? bindings)) nil
    (and (identical? declared (:declared prior)) (identical? bindings (:bindings prior))) prior
    (or (nil? declared) (and (or (vector? declared) (set? declared)) (every? variable-path? declared)))
    {:declared declared :bindings bindings
     :paths (into (set declared) (filter #(= :variables (first %))) (keys bindings))}
    :else (throw (ex-info "Declare full show variable paths on a predictable step" {::variable-paths declared}))))

(def ^:private missing (Object.))

(defn- variable-entry [frame path]
  (let [value (get-in frame path missing)]
    (when-not (identical? missing value) [path value])))

(defn- input-generation [paths frame transport-basis]
  (let [generation (:keyframe-generation frame)]
    (if (or (seq paths) transport-basis)
      (cond-> {::generation generation}
        (seq paths) (assoc ::variables (into {} (keep #(variable-entry frame %)) paths))
        transport-basis (assoc ::transport-basis transport-basis))
      generation)))

(defn- declared-dependencies [signature]
  (let [generation (nth signature 8)]
    [(get generation ::variables) (get generation ::transport-basis)]))

(defn- sample-input [ctx]
  ;; An arbitrary certified reader can capture its input. Keep previous
  ;; observers, worker timers and window history outside that private scope.
  (-> ctx
      (update :frame #(-> % (dissoc :keyframes :measure-effect :keyframe-intervals)
                          (vary-meta dissoc ::positions)))
      (update :instance vary-meta dissoc ::runtime/observe)))

(defn- invariant-sampler [step ctx options]
  (when-not options
    (let [{:keys [prepare sampler]} (::time-invariant (meta step))]
      (if-not prepare sampler
        (let [input (sample-input ctx)]
          (when (identical? input (prepare input)) sampler))))))

(defn- signature [instance frame options clock paths transport-basis]
  [(:effect-version instance) (dissoc (:params instance) (get-in options [:progress :param]))
   (:phase instance) (:bpm clock) (:meter clock) (:hdr? frame)
   (:targets instance) (:started-at-beat instance) (input-generation paths frame transport-basis)])

(defn with-rig-positions
  "Give all predicting workers one lazy lookup on this frozen rig. Successful
  frames retain its immutable result in the keyframe map's private metadata."
  [{:keys [fixtures keyframes] :as frame}]
  (let [prior (meta keyframes)
        saved (when (identical? fixtures (::rig prior)) (::positions prior))]
    (vary-meta frame assoc ::positions (or saved (delay (values/fixture-positions fixtures))))))

(defn- completed-positions [lookup]
  (cond
    (map? lookup) lookup
    (and lookup (realized? lookup))
    ;; A worker may have rejected a speculative endpoint. Never publish a
    ;; failed lookup or let reading its exception abort healthy effects.
    (try @lookup
         (catch Throwable error
           (when-not (faults/recoverable? error) (throw error))))))

(defn committed-windows [frame evaluations]
  (let [windows (into {} (keep (fn [{:keys [id keyframe done?]}]
                                 (when (and keyframe (not done?)) [id keyframe]))) evaluations)]
    (if-let [positions (when (seq windows) (completed-positions (::positions (meta frame))))]
      (with-meta windows {::rig (:fixtures frame) ::positions positions})
      windows)))

(defn- fresh-window [window prior same-inputs? sample ctx]
  (let [{:keys [options origin-clock target-clock]} window
        rig (:rig window)
        positions (or (::positions (meta (:frame ctx))) (delay (values/fixture-positions rig)))
        source (delay (sample ctx))
        previous-time (when (and same-inputs? prior) (time/coordinate origin-clock (:unit prior)))
        origin (cond
                 (and same-inputs? prior)
                 (cond (:progress options) (:result prior)
                       (< previous-time (:end prior)) (:result (sample-window prior ctx options previous-time))
                       (== previous-time (:end prior)) (:target prior)
                       :else @source)

                 (and prior (= (:epoch prior) (:epoch window)) (identical? (:rig prior) (:rig window))
                      ;; An automatic prediction follows the live clock across a
                      ;; tempo/meter edit. An authored tween keeps its last result.
                      (or (:interval options)
                          (and (= (:bpm origin-clock) (get-in prior [:origin-clock :bpm]))
                               (= (:meter origin-clock) (get-in prior [:origin-clock :meter]))))
                      (= (first (:inputs prior)) (first (:inputs window)))
                      (= (nth (:inputs prior) 5) (nth (:inputs window) 5))
                      (= (declared-dependencies (:inputs prior)) (declared-dependencies (:inputs window)))
                      (<= (get-in prior [:origin-clock :time-ms]) (:time-ms origin-clock))
                      (<= (get-in prior [:origin-clock :beat]) (:beat origin-clock)))
                 (:result prior)

                 :else @source)
        forecast (try
                   (values/indexed-endpoints origin (sample (future-context ctx target-clock)) positions (:curve options))
                   (catch Throwable error
                     (when-not (faults/recoverable? error) (throw error))
                     ;; A possible future error is not a current effect fault.
                     nil))]
    (if-let [[origin target] forecast]
      (let [window (assoc window :target target :origin origin)]
        (if (and prior (not (realized? source)))
          (assoc window :progress 0.0 :result origin)
          (sample-window window ctx options (:start window))))
      (assoc window :forecast-failed? true :result @source))))

(defn- constant-window [window prior sample ctx]
  (vary-meta
   (if prior
     (let [endpoint (:origin prior)]
       (assoc window :origin endpoint :target endpoint :result endpoint :progress 0.0))
     ;; Validate the first sample as both endpoints on the frozen rig. A
     ;; geometry rejection still opens an ordinary live-sampling interval.
     (let [endpoint (delay (sample ctx))]
       (fresh-window window nil false (fn [_] @endpoint) ctx)))
   assoc ::constant-window true))

(defn- run-window [step ctx options prior adaptive paths transport-basis constant?]
  (let [{:keys [frame instance]} ctx
        prior (when (= constant? (boolean (::constant-window (meta prior)))) prior)
        clock (time/frame-clock frame)
        {:keys [unit value]} (duration options adaptive clock)
        _ (when-not (and (time/finite-number? value) (pos? value))
            (throw (ex-info "Invalid predictive cadence" {:interval value})))
        now (time/coordinate clock unit)
        inputs (signature instance frame options clock paths transport-basis)
        sample (fn [at] (call ctx true #(let [input (sample-input at)] (values/blocks input (step input)))))
        same-inputs? (and prior (= (:epoch frame) (:epoch prior)) (identical? (:rig prior) (:fixtures frame))
                          (= inputs (:inputs prior)) (= options (:options prior))
                          (<= (:start prior) (time/coordinate clock (:unit prior))))
        valid? (and same-inputs? (= unit (:unit prior)) (== value (:span prior)))]
    (if (and valid? (< now (:end prior)))
      (if (:forecast-failed? prior)
        (assoc prior :result (sample ctx))
        (sample-window prior ctx options now))
      (let [end (started prior unit now value valid?)
            window {:unit unit :span value :start now :end end :epoch (:epoch frame) :inputs inputs
                    :options options :rig (:fixtures frame) :origin-clock clock :target-clock (clock-at clock unit end)}]
        (when (and options (not= options (:options prior))) (validate! options))
        ;; At the end of a failed forecast evaluate the *real* frame before
        ;; attempting another prediction. This runs the normal fault boundary.
        (let [usable (when-not (:forecast-failed? prior) prior)]
          (if constant?
            (constant-window window (when same-inputs? usable) sample ctx)
            (fresh-window window usable same-inputs? sample ctx)))))))

(defn- settle [window]
  (-> window (dissoc ::interpolation :discrete?)
      (assoc :settled? true :progress 1.0 :result (:target window))))

(defn- reactive-sample [window now hdr?]
  (let [{:keys [start end origin target]} window]
    (cond
      (:settled? window) window
      (>= now end) (settle window)
      (<= now start) window
      :else (let [progress (/ (- (rationalize now) (rationalize start))
                              (- (rationalize end) (rationalize start)))
                  [left right] (::interpolation window)
                  result (if (:discrete? window)
                           (if (< progress 1/2) origin target)
                           (values/blend left right progress hdr? true))]
              (assoc window :progress (double progress) :result result)))))

(defn- reactive-window [base prior result clock fixtures]
  (let [span (get-in base [:options :transition :beats])
        beats (:beat clock)
        end (when (and span (time/finite-number? beats)) (+' beats span))
        origin (or (:result prior) result)
        window (assoc base :origin origin :target result :result origin :origin-clock clock)]
    (if (and prior end (time/finite-number? end) (> end beats))
      (let [aligned (try
                      (values/endpoints origin result fixtures :linear)
                      (catch clojure.lang.ExceptionInfo error
                        (when-not (= ::values/invalid-sampler (:type (ex-data error)))
                          (throw error))))]
        (assoc window :unit :beats :span span :start beats :end end
               :target-clock (clock-at clock :beats end) :progress 0.0 :settled? false
               ::interpolation aligned :discrete? (nil? aligned)))
      (settle (assoc window :origin result :target-clock clock)))))

(defn- evaluate-reactive [{:keys [options calculate prepare]} ctx]
  (let [{:keys [frame instance]} ctx
        input-context (if prepare (prepare (sample-input ctx)) ctx)]
    (when (get-in instance [:definition :keyframes])
      (throw (ex-info "Dependency-driven effects cannot also declare predictive keyframes" {})))
    (if-let [inputs (reactive-inputs input-context (:inputs options))]
      (let [clock (time/frame-clock frame)
            now (:beat clock)
            fixtures (:fixtures frame)
            hdr? (:hdr? frame)
            base {:mode :dependency-driven :epoch (:epoch frame) :rig fixtures
                  :signature [(:show-id frame) (:effect-version instance) (:started-at-ms instance) (:started-at-beat instance)
                              (:targets instance) hdr? options]
                  :options options :inputs inputs :beat now}
            prior (get-in frame [:keyframes (:id instance)])
            prior (when (and (= :dependency-driven (:mode prior)) (= (:epoch prior) (:epoch frame))
                             (identical? (:rig prior) fixtures) (= (:signature prior) (:signature base))
                             (or (nil? now) (nil? (:beat prior)) (>= now (:beat prior))))
                    prior)
            window (if (and prior (.equals ^Object inputs (:inputs prior)))
                     (assoc (if (time/finite-number? now) (reactive-sample prior now hdr?) prior) :beat now)
                     (reactive-window base prior (call ctx false #(reactive-contributions calculate inputs hdr?)) clock fixtures))]
        (assoc ctx :contributions (:result window) ::window window))
      ctx)))

(defn- evaluate-predictive [step ctx]
  (let [{:keys [frame instance]} ctx sampler (::sampler (meta step))
        options (get-in instance [:definition :keyframes])
        adaptive (get-in frame [:keyframe-intervals (:id instance)])
        eligible? (and sampler (= :running (:phase instance)) (not (get-in instance [:system :paused?]))
                       (not= false (:playing? frame)) (time/finite-number? (:beat frame))
                       (time/finite-number? (:bpm frame)) (pos? (:bpm frame)))]
    (if (and eligible? (or (:interval options) adaptive))
      (let [prior (get-in frame [:keyframes (:id instance)])
            dependencies (variable-dependencies (::variable-paths (meta step)) (get-in instance [:definition :blocks])
                                                (::dependencies prior))
            transport-basis (when (::transport-clock? (meta step))
                              [(:started-at-beat instance)
                               (get-in instance [:system :clock-offset-beats])
                               (get-in instance [:system :clock-offset-ms] 0)
                               (get-in frame [:transport-clock :meter])])
            invariant (invariant-sampler step ctx options)
            window (cond-> (run-window (or invariant sampler) ctx options prior adaptive (:paths dependencies)
                                       transport-basis (some? invariant))
                     (or dependencies (::dependencies prior)) (assoc ::dependencies dependencies))
            result (assoc ctx :contributions (:result window) ::window window)]
        (if-let [reader (observations/reader window frame)]
          (vary-meta result assoc ::runtime/observe reader)
          result))
      (call ctx (boolean eligible?) #(step ctx)))))

(defn evaluate
  "Run either a real step or a lightweight interpolation; all cached results
  travel through the committed frame, so failed or timed-out evaluations cannot
  advance any other instance. External progress comes from the live private context.
  Mark steps reading :transport-clock with ::transport-clock? metadata so a
  seek, pause offset or shared meter change refreshes their sampled endpoints."
  [step ctx]
  (if-let [reactive (::reactive (meta step))]
    (evaluate-reactive reactive ctx)
    (evaluate-predictive step ctx)))

(defn inspect
  "Inspect one head/attribute without sending the complete field to a display.
  Each endpoint is a vector of writes in the effect's native assignment order."
  [window target attribute]
  (when window
    (cond-> (select-keys window [:mode :settled? :unit :start :end :span :origin-clock :target-clock :progress :forecast-failed?])
      (and target attribute)
      (merge (update-vals (select-keys window [:origin :target :result])
                          #(values/read-values % target attribute))))))
