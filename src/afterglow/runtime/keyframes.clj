(ns afterglow.runtime.keyframes
  "Predict continuous native effect outputs on their private musical clock."
  (:require [afterglow.render.easing :as easing]
            [afterglow.runtime :as runtime]
            [afterglow.runtime.faults :as faults]
            [afterglow.runtime.keyframes.observations :as observations]
            [afterglow.runtime.keyframes.values :as values]
            [afterglow.time :as time]))

(defn predictable
  "Declare a stateless continuous sampler. No lifecycle, emitted events, external
  effects, frame-count dependence or deferred native jobs are allowed. An optional
  separate sampler can use the numeric CPU backend on a predictive evaluation."
  ([step] (predictable step step))
  ([step sampler] (with-meta step (assoc (meta step) ::sampler sampler))))

(defn predictable? [step] (boolean (::sampler (meta step))))

(defn with-inputs
  "Preprocess current and projected contexts through the same input middleware."
  [step transform]
  (let [run (comp step transform)
        info (meta step)
        sample (::sampler info)]
    (if info
      (with-meta run (cond-> info sample (assoc ::sampler (comp sample transform))))
      run)))

(defn validate! [{:keys [interval curve progress] :as options}]
  (when-not (and (map? options) (every? #{:interval :curve :progress} (keys options))
                 (empty? (time/validate-duration interval)) (pos? (val (first interval))))
    (throw (ex-info "Keyframes need a positive musical or millisecond interval" {:keyframes options})))
  (easing/sample (or curve :linear) 0.5)
  (when (and (some? progress)
             (not (and (map? progress) (#{:replace :offset} (:mode progress))
                       (or (and (= #{:mode :param} (set (keys progress))) (keyword? (:param progress)))
                           (and (= #{:mode :variable} (set (keys progress))) (vector? (:variable progress))
                                (seq (:variable progress)))))))
    (throw (ex-info "Keyframe progress needs a mode and one parameter or variable" {:progress progress})))
  options)

(defn- duration [interval adaptive clock]
  (let [normalize #(time/normalize-duration % (:meter clock))
        authored (when interval (normalize interval))
        adaptive (when adaptive (normalize adaptive))]
    (cond (nil? adaptive) authored
          (nil? authored) adaptive
          (> (time/estimate-ms adaptive (:bpm clock)) (time/estimate-ms authored (:bpm clock))) adaptive
          :else authored)))

(defn- clock-at [clock unit coord]
  (let [bpm (:bpm clock) now (time/coordinate clock unit) diff (- coord now)
        ms (if (= unit :ms) diff (* diff (/ 60000.0 bpm)))
        beat (if (= unit :beats) diff (* ms (/ bpm 60000.0)))]
    (-> clock (update :time-ms + ms) (update :beat + beat))))

(defn- future-context [ctx clock]
  (let [frame (:frame ctx) delta (- (:time-ms clock) (:time-ms frame))]
    (assoc ctx :frame (-> frame (merge clock) (assoc :delta-ms delta)
                          (update :transport merge clock)))))

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
    (assoc (with-meta window {::ease curve-fn}) :progress progress :result (values/blend origin target progress (get-in ctx [:frame :hdr?])))))

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

(defn- input-generation [paths frame]
  (let [generation (:keyframe-generation frame)]
    (if (seq paths)
      {::generation generation ::variables (into {} (keep #(variable-entry frame %)) paths)}
      generation)))

(defn- declared-variables [signature]
  (get (nth signature 8) ::variables))

(defn- sample-input [ctx]
  ;; An arbitrary certified reader can capture its input. Keep previous
  ;; observers, worker timers and window history outside that private scope.
  (-> ctx
      (update :frame #(-> % (dissoc :keyframes :measure-effect :keyframe-intervals)
                          (vary-meta dissoc ::positions)))
      (update :instance vary-meta dissoc ::runtime/observe)))

(defn- signature [instance frame options clock paths]
  [(:effect-version instance) (dissoc (:params instance) (get-in options [:progress :param]))
   (:phase instance) (:bpm clock) (:meter clock) (:hdr? frame)
   (:targets instance) (:started-at-beat instance) (input-generation paths frame)])

(defn with-rig-positions
  "Give all predicting workers one lazy lookup on this frozen rig. Successful
  frames retain the realized lookup in the keyframe map's private metadata."
  [{:keys [fixtures keyframes] :as frame}]
  (let [prior (meta keyframes)
        saved (when (identical? fixtures (::rig prior)) (::positions prior))]
    (vary-meta frame assoc ::positions (or saved (delay (values/fixture-positions fixtures))))))

(defn committed-windows [frame evaluations]
  (let [windows (into {} (keep (fn [{:keys [id keyframe done?]}]
                                 (when (and keyframe (not done?)) [id keyframe]))) evaluations)
        positions (::positions (meta frame))]
    (if (and (seq windows) positions (realized? positions))
      ;; A lookup may also have failed inside a speculative sample. Keep forcing
      ;; it inside the worker fault boundary, never while committing healthy cues.
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
                      (= (first (:inputs prior)) (first (:inputs window)))
                      (= (nth (:inputs prior) 5) (nth (:inputs window) 5))
                      (= (declared-variables (:inputs prior)) (declared-variables (:inputs window)))
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

(defn- run-window [step ctx options prior adaptive paths]
  (let [{:keys [frame instance]} ctx
        clock (time/frame-clock frame)
        {:keys [unit value]} (duration (:interval options) adaptive clock)
        _ (when-not (and (time/finite-number? value) (pos? value))
            (throw (ex-info "Invalid predictive cadence" {:interval value})))
        now (time/coordinate clock unit)
        inputs (signature instance frame options clock paths)
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
        (fresh-window window (when-not (:forecast-failed? prior) prior) same-inputs? sample ctx)))))

(defn evaluate
  "Run either a real step or a lightweight interpolation; all cached results
  travel through the committed frame, so failed or timed-out evaluations cannot
  advance any other instance. External progress comes from the live private context."
  [step ctx]
  (let [{:keys [frame instance]} ctx sampler (::sampler (meta step))
        options (get-in instance [:definition :keyframes])
        adaptive (get-in frame [:keyframe-intervals (:id instance)])
        eligible? (and sampler (= :running (:phase instance)) (not (get-in instance [:system :paused?]))
                       (not= false (:playing? frame)) (time/finite-number? (:beat frame))
                       (time/finite-number? (:bpm frame)) (pos? (:bpm frame)))]
    (if (and eligible? (or options adaptive))
      (let [prior (get-in frame [:keyframes (:id instance)])
            dependencies (variable-dependencies (::variable-paths (meta step)) (get-in instance [:definition :blocks])
                                                (::dependencies prior))
            window (cond-> (run-window sampler ctx options prior adaptive (:paths dependencies))
                     (or dependencies (::dependencies prior)) (assoc ::dependencies dependencies))
            result (assoc ctx :contributions (:result window) ::window window)]
        (if-let [reader (observations/reader window frame)]
          (vary-meta result assoc ::runtime/observe reader)
          result))
      (call ctx (boolean eligible?) #(step ctx)))))

(defn inspect
  "Inspect one head/attribute without sending the complete field to a display.
  Each endpoint is a vector of writes in the effect's native assignment order."
  [window target attribute]
  (when window
    (cond-> (select-keys window [:unit :start :end :span :origin-clock :target-clock :progress :forecast-failed?])
      (and target attribute)
      (merge (update-vals (select-keys window [:origin :target :result])
                          #(values/read-values % target attribute))))))
