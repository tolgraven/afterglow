(ns afterglow.control.system
  "Pure per-instance performance controls. No output buffers or runtime handles
  belong here. Private clocks keep explicit musical and millisecond coordinates."
  (:require [afterglow.time :as time]))

(defn- invalid! [message & [details]]
  (throw (ex-info message {:control/error :invalid-system :details details})))

(defn- unit? [x] (and (time/finite-number? x) (<= 0 x 1)))

(defn validate-options [options]
  (when-not (and (map? options) (every? #{:opacity :gain :attack :release} (keys options)))
    (invalid! "System options accept opacity, gain, attack and release"))
  (when (and (contains? options :opacity) (not (unit? (:opacity options))))
    (invalid! "Opacity must be in [0,1]"))
  (when (and (contains? options :gain) (not (and (time/finite-number? (:gain options)) (<= 0 (:gain options)))))
    (invalid! "Emission gain must be finite and nonnegative"))
  (doseq [key [:attack :release] :when (contains? options key)]
    (when (seq (time/validate-duration (get options key)))
      (invalid! "Attack/release need a musical or explicit ms duration" {:field key})))
  options)

(defn private-clock [instance clock]
  (let [clock (time/frame-clock clock), system (:system instance)]
    (if (:paused? system)
      (merge clock (:paused-clock system))
      (cond-> (update clock :time-ms - (:clock-offset-ms system 0))
        (contains? clock :beat) (update :beat - (:clock-offset-beats system 0))))))

(defn gain
  "Independent AR compositing gate, sampled without changing authored parameters."
  [instance clock]
  (if-let [{:keys [kind timer from]} (get-in instance [:system :gate])]
    (let [progress (:progress (time/sample timer clock))]
      (+ from (* (- (if (= kind :release) 0.0 1.0) from) progress)))
    1.0))

(defn- gate [instance kind duration clock from]
  (assoc-in instance [:system :gate]
            {:kind kind
             :timer (try (time/start duration (assoc clock :meter (:timing-meter instance)))
                         (catch clojure.lang.ExceptionInfo cause
                           (invalid! "Invalid system envelope clock/duration" (ex-data cause))))
             :from from}))

(defn initialize [instance options clock]
  (validate-options options)
  (let [opacity (:opacity options 1.0)
        instance (assoc instance :system
                        (merge {:opacity opacity :restore-opacity (if (pos? opacity) opacity 1.0)
                                :paused? false :clock-offset-ms 0 :clock-offset-beats 0}
                               options))]
    (cond-> instance
      (:attack options) (gate :attack (:attack options) clock 0.0))))

(defn release-instance
  "Begin release once, using an already private clock. An explicit system release
  overrides the authored release lifecycle; otherwise preserve authored behavior."
  [instance clock]
  (if (= :releasing (:phase instance)) instance
      (let [next (assoc instance :phase :releasing :release-at-ms (:time-ms clock)
                                :release-at-beat (:beat clock))]
        (if-let [duration (get-in instance [:system :release])]
          (gate next :release duration clock (gain instance clock))
          (cond-> next
            (:release-duration instance)
            (assoc :release-timer (time/start (:release-duration instance)
                                             (assoc clock :meter (:timing-meter instance)))))))))

(defn system-release? [instance] (= :release (get-in instance [:system :gate :kind])))

(defn validate-control [command]
  (case (:op command)
    :instance/gain-set (validate-options {:gain (:value command)})
    :instance/opacity-set (when-not (unit? (:value command)) (invalid! "Opacity must be in [0,1]"))
    :instance/envelope-set (let [envelope (:envelope command)]
                             (when-not (and (map? envelope) (seq envelope)
                                            (every? #{:attack :release} (keys envelope)))
                               (invalid! "Envelope needs attack and/or release durations"))
                             (validate-options envelope))
    (:instance/pause :instance/resume :instance/opacity-toggle) nil
    (invalid! "Unknown system operation" {:op (:op command)}))
  command)

(defn apply-control [instance command global-clock]
  (validate-control command)
  (let [clock (private-clock instance global-clock)]
    (case (:op command)
      :instance/pause
      (if (get-in instance [:system :paused?]) instance
          (-> instance
              (assoc-in [:system :paused?] true)
              (assoc-in [:system :paused-clock] (or (get-in instance [:system :last-clock]) clock))))
      :instance/resume
      (if-not (get-in instance [:system :paused?]) instance
          (-> instance
              (assoc-in [:system :paused?] false)
              (assoc-in [:system :clock-offset-ms] (- (:time-ms global-clock) (:time-ms clock)))
              (assoc-in [:system :clock-offset-beats] (- (:beat global-clock 0) (:beat clock 0)))
              (update :system dissoc :paused-clock)))
      :instance/gain-set (assoc-in instance [:system :gain] (:value command))
      :instance/opacity-set
      (let [value (:value command)]
        (when-not (unit? value) (invalid! "Opacity must be in [0,1]"))
        (cond-> (assoc-in instance [:system :opacity] value)
          (pos? value) (assoc-in [:system :restore-opacity] value)))
      :instance/opacity-toggle
      (let [current (get-in instance [:system :opacity] 1.0)]
        (-> instance
            (assoc-in [:system :restore-opacity] (if (pos? current) current
                                                      (get-in instance [:system :restore-opacity] 1.0)))
            (assoc-in [:system :opacity] (if (pos? current) 0.0
                                              (get-in instance [:system :restore-opacity] 1.0)))))
      :instance/envelope-set
      (let [envelope (:envelope command)
            _ (when-not (and (map? envelope) (seq envelope)
                             (every? #{:attack :release} (keys envelope)))
                (invalid! "Envelope needs attack and/or release durations"))
            _ (validate-options envelope)
            level (gain instance clock)
            changed (update instance :system merge envelope)
            stage (get-in instance [:system :gate :kind])]
        (cond
          (and (= stage :release) (contains? envelope :release))
          (gate changed :release (:release envelope) clock level)
          (and (not= :releasing (:phase instance)) (contains? envelope :attack))
          (gate changed :attack (:attack envelope) clock level)
          :else changed))
      (invalid! "Unknown system operation" {:op (:op command)}))))

(defn validate-state [instance]
  (let [system (:system instance)]
    (when system
      (when-not (and (map? system) (unit? (:opacity system 1.0))
                     (unit? (:restore-opacity system 1.0))
                     (instance? Boolean (:paused? system false))
                     (every? #(time/finite-number? (get system % 0)) [:clock-offset-ms :clock-offset-beats]))
        (invalid! "Invalid instance system controls"))
      (validate-options (select-keys system [:opacity :gain :attack :release]))
      (doseq [k [:last-clock :paused-clock] :when (contains? system k)]
        (let [clock (get system k)]
          (when-not (and (map? clock) (time/finite-number? (:time-ms clock))
                         (or (not (contains? clock :beat)) (time/finite-number? (:beat clock))))
            (invalid! "Invalid private clock" {:field k}))))
      (when (or (and (contains? system :last-delta-ms)
                     (not (and (time/finite-number? (:last-delta-ms system)) (<= 0 (:last-delta-ms system)))))
                (and (contains? system :last-frame-number)
                     (not (and (integer? (:last-frame-number system)) (<= 0 (:last-frame-number system))))))
        (invalid! "Invalid paused-frame bookkeeping"))
      (when (and (:paused? system) (not (:paused-clock system)))
        (invalid! "Paused instance needs a frozen clock"))
      (when-let [{:keys [kind timer from]} (:gate system)]
        (when-not (and (#{:attack :release} kind) (unit? from)
                       (#{:ms :beats} (get-in timer [:duration :unit]))
                       (time/finite-number? (:started-at timer))
                       (time/finite-number? (get-in timer [:duration :value]))
                       (<= 0 (get-in timer [:duration :value])))
          (invalid! "Invalid system envelope gate")))))
  instance)
