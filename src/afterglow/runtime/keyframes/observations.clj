(ns afterglow.runtime.keyframes.observations
  "Demand-driven evidence from sampled programs and the committed native tween."
  (:require [afterglow.runtime :as runtime]
            [afterglow.runtime.keyframes.values :as values]))

(defn- output-attribute [[path target] sample]
  (when (and target (vector? path) (= :outputs (first path)))
    (or (:attribute sample) (when (keyword? (second path)) (second path)))))

(defn- native [window target attribute]
  (update-vals (select-keys window [:origin :target :result])
               #(values/read-values % target attribute)))

(defn- origin-kind [origin]
  (let [m (meta origin)]
    (cond (::values/restored m) :restored
          (::values/sample-clock m) :sampled
          :else :interpolated)))

(defn reader [{:keys [origin target result forecast-failed?] :as window} frame]
  (let [origin-reader (::runtime/observe (meta origin))
        target-reader (::runtime/observe (meta target))
        result-reader (::runtime/observe (meta result))
        source (cond (and forecast-failed? result-reader) :live
                     (and (identical? origin result) origin-reader) :origin
                     target-reader :target)]
    (when source
      (let [[sampled read-sample] (case source
                                    :live [result result-reader]
                                    :origin [origin origin-reader]
                                    :target [target target-reader])
            timing (cond-> (assoc (select-keys window [:origin-clock :target-clock :progress])
                                  :trace-source source :sample-clock (::values/sample-clock (meta sampled)))
                     origin (assoc :origin-kind (origin-kind origin)))
            fields (select-keys window [:origin :target :result])
            now (:time-ms frame)
            number (:number frame)]
        ;; Only actual sampled endpoints carry readers. Interpolating native
        ;; blocks never captures a reader from an earlier interpolated origin.
        (fn [[_ target-id :as query]]
          (when-let [sample (read-sample query)]
            (let [attribute (output-attribute query sample)
                  detail (cond-> timing
                           (and (= source :target) origin-reader) (assoc :origin-trace (origin-reader query))
                           (and (= source :origin) target-reader) (assoc :target-trace (target-reader query))
                           attribute (assoc :native (native fields target-id attribute)))]
              (assoc (if (map? sample) sample {:result sample})
                     :time-ms now :frame-number number :keyframe detail))))))))
