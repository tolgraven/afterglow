(ns afterglow.runtime.keyframes
  "Predict continuous native effect outputs on their private musical clock."
  (:require [afterglow.render.easing :as easing]
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
  (let [run (comp step transform)]
    (if-let [sample (::sampler (meta step))]
      (predictable run (comp sample transform))
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

(defn- run-window [step ctx options prior adaptive]
  (let [{:keys [frame instance]} ctx
        clock (time/frame-clock frame)
        {:keys [unit value]} (duration (:interval options) adaptive clock)
        _ (when-not (and (time/finite-number? value) (pos? value))
            (throw (ex-info "Invalid predictive cadence" {:interval value})))
        now (time/coordinate clock unit)
        data (dissoc (:params instance) (get-in options [:progress :param]))
        inputs [(:effect-version instance) data (:phase instance) (:bpm clock) (:meter clock) (:hdr? frame)
                (:targets instance) (:started-at-beat instance) (:keyframe-generation frame)]
        same-rig? (and (= (:epoch frame) (:epoch prior)) (identical? (:rig prior) (:fixtures frame)))
        valid? (and prior same-rig? (= inputs (:inputs prior)) (= options (:options prior))
                    (= [unit value] [(:unit prior) (:span prior)]) (<= (:start prior) now))
        sample #(call ctx true (fn [] (values/blocks % (step %))))]
    (if (and valid? (< now (:end prior)))
      (sample-window prior ctx options now)
      (let [end (started prior unit now value valid?)
            origin (if (and valid? (<= (:end prior) now))
                     (:result (sample-window prior ctx options now))
                     (if (and prior same-rig? (= (first inputs) (first (:inputs prior))))
                       (:result prior) (sample ctx)))
            target-clock (clock-at clock unit end)
            [origin target] (values/endpoints origin (sample (future-context ctx target-clock)))
            window {:unit unit :span value :start now :end end :epoch (:epoch frame) :inputs inputs
                    :options options :rig (:fixtures frame) :origin-clock clock :target-clock target-clock
                    :origin origin :target target}]
        ;; The new segment starts at the displayed value even when an external
        ;; progress signal carries a nonzero value across this boundary.
        (if (and prior same-rig?)
          (assoc window :progress 0.0 :result origin)
          (sample-window window ctx options now))))))

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
      (let [window (run-window sampler ctx options (get-in frame [:keyframes (:id instance)]) adaptive)]
        (assoc ctx :contributions (:result window) ::window window))
      (call ctx (boolean eligible?) #(step ctx)))))

(defn inspect
  "Inspect one head/attribute without sending the complete field to a display.
  Each endpoint is a vector of writes in the effect's native assignment order."
  [window target attribute]
  (when window
    (cond-> (select-keys window [:unit :start :end :span :origin-clock :target-clock :progress])
      (and target attribute)
      (merge (update-vals (select-keys window [:origin :target :result])
                          #(values/read-values % target attribute))))))
