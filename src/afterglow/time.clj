(ns afterglow.time
  "Pure musical durations and explicit clocks. Musical timers compare beats;
  tempo is used only when estimating milliseconds at a presentation boundary.")

(def default-meter {:beats-per-bar 4 :bars-per-phrase 4})
(def units #{:beats :bars :phrases :ms})

(defn finite-number? [x]
  (and (number? x) (Double/isFinite (double x))))

(defn normalize-meter
  "Capture beats per bar and whole bars per phrase. Beats use the transport's
  quarter-note unit: a 7/8 bar contains 7/2 beats, not seven quarter notes."
  [meter]
  (let [meter (merge default-meter meter)
        beats-per-bar (:beats-per-bar meter)
        bars-per-phrase (:bars-per-phrase meter)]
    (when-not (and (finite-number? beats-per-bar) (pos? beats-per-bar)
                   (integer? bars-per-phrase) (pos? bars-per-phrase))
      (throw (ex-info "Meter needs positive finite quarter-note beats per bar and positive integer bars per phrase"
                      {:meter meter})))
    (select-keys meter [:beats-per-bar :bars-per-phrase])))

(defn validate-duration
  "A duration has exactly one of :beats/:bars/:phrases/:ms, with a finite
  nonnegative value. Zero is useful for envelope stages; lifecycle callers may
  additionally require a positive value. Ratios and JSON decimals are accepted."
  [duration]
  (cond
    (not (and (map? duration) (= 1 (count duration))
              (contains? units (ffirst duration))))
    [{:path [] :message "Duration needs exactly one unit: beats, bars, phrases or ms"}]
    (not (and (finite-number? (val (first duration)))
              (not (neg? (val (first duration))))))
    [{:path [(ffirst duration)] :message "Duration must be finite and nonnegative"}]
    :else []))

(defn normalize-duration
  "Resolve bars/phrases with a captured meter, preserving exact ratios. The
  resulting :unit is :beats or :ms; :source retains authoring intent."
  ([duration] (normalize-duration duration default-meter))
  ([duration meter]
   (let [errors (validate-duration duration)]
     (when (seq errors) (throw (ex-info "Invalid duration" {:errors errors :duration duration}))))
   (let [meter (normalize-meter meter)
         [unit value] (first duration)
         value (* value (case unit :bars (:beats-per-bar meter)
                             :phrases (* (:beats-per-bar meter) (:bars-per-phrase meter)) 1))]
     (when-not (finite-number? value)
       (throw (ex-info "Duration exceeds finite range" {:duration duration :meter meter})))
     {:unit (if (= unit :ms) :ms :beats) :value value :source duration :meter meter})))

(defn duration->beats
  ([duration] (duration->beats duration default-meter))
  ([duration meter]
   (let [{:keys [unit value]} (normalize-duration duration meter)]
     (when-not (= unit :beats)
       (throw (ex-info "Milliseconds have no fixed beat duration across tempo changes" {:duration duration})))
     value)))

(defn frame-clock
  "Flatten explicit frame/transport data. Also accepts an already flat clock,
  or numeric millisecond time for compatibility. Does not synthesize beats."
  [frame]
  (cond
    (number? frame) {:time-ms frame}
    (map? frame) (merge (select-keys (:transport frame) [:beat :bpm :playing? :meter])
                        (select-keys frame [:time-ms :beat :bpm :playing? :meter]))
    :else (throw (ex-info "Clock must be a frame, clock map or millisecond value" {:clock frame}))))

(defn coordinate [clock unit]
  (let [clock (frame-clock clock)
        key (case unit :beats :beat :ms :time-ms
                  (throw (ex-info "Clock unit must be beats or ms" {:unit unit})))
        value (get clock key)]
    (when-not (finite-number? value)
      (throw (ex-info "Clock is missing a finite coordinate" {:unit unit :key key :clock clock})))
    value))

(defn start [duration clock]
  (let [clock (frame-clock clock)
        normalized (normalize-duration duration (:meter clock))]
    {:duration normalized :started-at (coordinate clock (:unit normalized))}))

(defn sample
  "Sample a timer without reading or advancing any clock. A constant transport
  beat freezes musical progress, regardless of wall time or current tempo."
  [{:keys [duration started-at] :as timer} clock]
  (let [{:keys [unit value]} duration
        now (coordinate clock unit)]
    (when-not (and (finite-number? started-at) (finite-number? value) (not (neg? value)))
      (throw (ex-info "Invalid timer" {:timer timer})))
    (let [elapsed (max 0 (- now started-at))]
      {:unit unit :elapsed elapsed :remaining (max 0 (- value elapsed))
       :progress (if (zero? value) 1.0 (double (min 1 (/ elapsed value))))
       :done? (>= (- now started-at) value)})))

(defn estimate-ms
  "Current-tempo estimate for display/output planning, never a musical deadline."
  [{:keys [unit value] :as duration} bpm]
  (when-not (and (#{:beats :ms} unit) (finite-number? value) (not (neg? value)))
    (throw (ex-info "Expected a normalized duration" {:duration duration})))
  (if (= unit :ms) value
      (do (when-not (and (finite-number? bpm) (pos? bpm))
            (throw (ex-info "Tempo must be finite and positive" {:bpm bpm})))
          (* value (/ 60000.0 bpm)))))
