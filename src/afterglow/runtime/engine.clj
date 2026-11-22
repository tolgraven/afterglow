(ns afterglow.runtime.engine
  "Pure show-model coordinator for the declarative runtime.

  This is a working runtime for the new control model, separate from the legacy
  afterglow.show scheduler. The shell captures time, owns the executor/compiler
  cache and commits a successful result before performing returned intents."
  (:require [afterglow.runtime :as runtime]
            [afterglow.runtime.faults :as faults]
            [afterglow.time :as musical-time]
            [afterglow.control.params :as params]
            [afterglow.control.system :as system]))

(defn- fail!
  [type message data]
  (throw (ex-info message (assoc data :type type))))

(defn- finite-number?
  [value]
  (and (number? value) (Double/isFinite (double value))))

(defn- nonnegative-number?
  [value]
  (and (finite-number? value) (not (neg? value))))

(defn- validate-instance!
  [id instance]
  (system/validate-state instance)
  (when-not (and (map? instance) (string? id) (= id (:id instance))
                 (map? (:definition instance))
                 (= (:effect-id instance) (get-in instance [:definition :id]))
                 (= (:effect-version instance) (get-in instance [:definition :version]))
                 (integer? (:effect-version instance)) (pos? (:effect-version instance))
                 (map? (:params instance)) (contains? instance :state)
                 (finite-number? (:priority instance))
                 (integer? (:order instance)) (not (neg? (:order instance)))
                 (nonnegative-number? (:started-at-ms instance))
                 (#{:running :releasing} (:phase instance)))
    (fail! ::invalid-instance "Invalid runtime instance" {:instance-id id}))
  (when (and (some? (:duration-ms instance))
             (not (and (finite-number? (:duration-ms instance))
                       (pos? (:duration-ms instance)))))
    (fail! ::invalid-duration "Instance duration must be finite and positive"
           {:instance-id id}))
  (when-not (nonnegative-number? (get instance :release-duration-ms 0))
    (fail! ::invalid-release-duration "Release duration must be finite and nonnegative"
           {:instance-id id}))
  (when (and (= :releasing (:phase instance))
             (not (nonnegative-number? (:release-at-ms instance))))
    (fail! ::invalid-release-time "Releasing instances require an explicit release time"
           {:instance-id id}))
  (when (or (and (:duration-ms instance)
                 (not (finite-number? (+ (:started-at-ms instance) (:duration-ms instance)))))
            (and (= :releasing (:phase instance))
                 (not (finite-number? (+ (:release-at-ms instance)
                                         (get instance :release-duration-ms 0))))))
    (fail! ::invalid-duration "Instance deadline exceeds finite logical time"
           {:instance-id id}))
  (when-not (#{:pinned :restart :preserve-state} (get instance :reload-policy :pinned))
    (fail! ::invalid-reload-policy "Unknown instance reload policy" {:instance-id id}))
  (doseq [field [:duration :release-duration] :when (contains? instance field)]
    (when (seq (musical-time/validate-duration (get instance field)))
      (fail! ::invalid-duration "Invalid musical duration" {:instance-id id :field field}))))

(defn- validate-input!
  [model frame compile-effect]
  (when-not (and (map? model) (map? (:instances model))
                 (map? (:registry model)) (integer? (:epoch model))
                 (integer? (:revision model))
                 (nonnegative-number? (:time-ms model))
                 (map? frame) (nonnegative-number? (:time-ms frame))
                 (ifn? compile-effect))
    (fail! ::invalid-input "Expected a show model, explicit frame time and compiler" {}))
  (when-not (and (integer? (get model :frame-number 0))
                 (not (neg? (get model :frame-number 0)))
                 (nonnegative-number? (get model :last-frame-time-ms (:time-ms model))))
    (fail! ::invalid-input "Invalid rendered-frame bookkeeping" {}))
  (when (and (contains? frame :epoch) (not= (:epoch model) (:epoch frame)))
    (fail! ::stale-epoch "Frame belongs to a different show epoch"
           {:expected (:epoch model) :received (:epoch frame)}))
  (when (and (contains? frame :show-id) (not= (:show-id model) (:show-id frame)))
    (fail! ::wrong-show "Frame belongs to another show" {}))
  (when (< (:time-ms frame) (:time-ms model))
    (fail! ::stale-time "Frame time cannot precede the model's logical time"
           {:model-time-ms (:time-ms model) :frame-time-ms (:time-ms frame)}))
  (when (and (contains? frame :delta-ms) (not (nonnegative-number? (:delta-ms frame))))
    (fail! ::invalid-delta "Frame delta must be finite and nonnegative" {}))
  (doseq [[id instance] (:instances model)]
    (validate-instance! id instance)))

(defn- reload-instance
  [registry clock instance]
  (let [policy (get instance :reload-policy :pinned)
        current (get-in registry [:effects (:effect-id instance)])]
    (if (and (not= :pinned policy) current
             (not= (:version current) (get-in instance [:reload-fault :effect-version]))
             (not= (:effect-version instance) (:version current)))
      (do
        (when-not (and (map? current) (= (:id current) (:effect-id instance))
                       (integer? (:version current))
                       (> (:version current) (:effect-version instance)))
          (fail! ::invalid-reload "Hot reload requires a newer definition version"
                 {:instance-id (:id instance)}))
        (let [params (params/resolve-values (:params current {})
                                           (select-keys (:params instance) (keys (:params current))))
              next-instance (assoc instance :definition current :effect-version (:version current)
                                   :params params)
              next-instance (if (= :restart policy)
                              (-> next-instance
                                  (assoc :state (get current :initial-state {})
                                         :started-at-ms (:time-ms clock) :started-at-beat (:beat clock) :phase :running)
                                  (dissoc :release-at-ms :release-at-beat :release-timer)
                                  (update :system dissoc :last-input-state :last-clock :last-delta-ms :last-frame-number :gate)
                                  (cond-> (get-in instance [:system :attack])
                                    (assoc-in [:system :gate]
                                              {:kind :attack :from 0.0
                                               :timer (musical-time/start (get-in instance [:system :attack])
                                                                          (assoc clock :meter (:timing-meter instance)))}))
                                  (cond-> (:duration instance)
                                    (assoc :duration-timer
                                           (musical-time/start (:duration instance)
                                                               (assoc clock :meter (:timing-meter instance))))))
                              next-instance)]
          [next-instance [{:type :effect/reloaded :instance-id (:id instance)
                           :from-version (:effect-version instance) :to-version (:version current)
                           :policy policy}]]))
      [instance []])))

(defn- boundary-clock
  "Interpolate within the last explicit clock interval, used only when a
  deadline crosses from beats to a millisecond release (or vice versa)."
  [model clock instance unit deadline]
  (let [last-clock (get-in instance [:system :last-clock])
        a-ms (max (:started-at-ms instance) (or (:time-ms last-clock) (get model :last-frame-time-ms (:started-at-ms instance))))
        a-beat (if (= a-ms (:started-at-ms instance)) (:started-at-beat instance)
                   (or (:beat last-clock) (get model :last-frame-beat (:started-at-beat instance))))
        b-ms (:time-ms clock) b-beat (:beat clock)
        interpolate (fn [a b c d x fallback]
                      (if (and (every? finite-number? [a b c d x]) (< a b) (<= a x b))
                        (+ c (* (/ (- x a) (- b a)) (- d c))) fallback))]
    (case unit
      :beats (assoc clock :beat deadline :time-ms (interpolate a-beat b-beat a-ms b-ms deadline b-ms))
      :ms (assoc clock :time-ms deadline :beat (interpolate a-ms b-ms a-beat b-beat deadline b-beat)))))

(defn- release-if-expired
  [model clock instance]
  (let [timer (or (:duration-timer instance)
                  (when-let [duration (:duration-ms instance)]
                    {:duration {:unit :ms :value duration} :started-at (:started-at-ms instance)}))]
    (if (and (= :running (:phase instance)) timer (:done? (musical-time/sample timer clock)))
      (let [unit (get-in timer [:duration :unit])
            deadline (+ (:started-at timer) (get-in timer [:duration :value]))
            release-clock (assoc (boundary-clock model clock instance unit deadline) :meter (:timing-meter instance))]
        (system/release-instance instance release-clock))
      instance)))

(defn- release-finished?
  [clock instance]
  (and (= :releasing (:phase instance))
       (if-let [timer (if (system/system-release? instance)
                        (get-in instance [:system :gate :timer]) (:release-timer instance))]
         (:done? (musical-time/sample timer clock))
         (>= (:time-ms clock) (+ (:release-at-ms instance) (get instance :release-duration-ms 0))))))

(defn- prepare-instance
  [model global-clock snapshot instance]
  (let [paused? (true? (get-in instance [:system :paused?]))
        clock (system/private-clock instance global-clock)
        [reloaded intents] (if paused? [instance []] (reload-instance (:registry model) clock instance))
        prepared (if paused? reloaded (release-if-expired model clock reloaded))
        input-state (if paused? (get-in prepared [:system :last-input-state] (:state prepared)) (:state prepared))
        delta (if paused? (get-in prepared [:system :last-delta-ms] 0)
                  (max 0 (- (:time-ms clock) (get-in prepared [:system :last-clock :time-ms]
                                                   (- (:time-ms clock) (:delta-ms snapshot))))))
        number (if paused? (get-in prepared [:system :last-frame-number] (:number snapshot))
                   (if-let [previous (get-in prepared [:system :last-frame-number])] (inc previous) (:number snapshot)))
        prepared (-> prepared
                     (assoc-in [:system :last-input-state] input-state)
                     (assoc-in [:system :last-clock] clock)
                     (assoc-in [:system :last-delta-ms] delta)
                     (assoc-in [:system :last-frame-number] number))]
    (validate-instance! (:id prepared) prepared)
    {:instance prepared :intents intents :clock clock :paused? paused?
     :input-state input-state :delta-ms delta :number number
     :expired? (and (not paused?) (release-finished? clock prepared))}))

(defn- with-opacity [result opacity]
  (cond
    (== 1 opacity) result
    (zero? opacity) (assoc result :assignments [] :contributions [])
    :else
    (let [weight (fn [value] (update value :opacity (fnil * 1.0) opacity))]
      (-> result
          (update :assignments #(mapv weight %))
          (update :contributions
                  #(mapv (fn [block]
                           (case (:kind block)
                             :assignments (update block :assignments (fn [values] (mapv weight values)))
                             :batch (update block :batch weight)
                             block)) %))))))

(defn- valid-step-shape? [result]
  (and (map? result) (contains? result :state) (vector? (:assignments result))
       (vector? (:intents result)) (instance? Boolean (:done? result))
       (or (not (contains? result :contributions)) (vector? (:contributions result)))))

(defn- native-layer [instance]
  (let [program (get-in instance [:definition :layer])
        slot (get-in instance [:source :native-layer])]
    (when (or program slot)
      (cond-> (or slot {:id [::standalone (:id instance)] :member 0})
        (seq (:transforms program))
        (update :transforms #(into (vec (:transforms program)) %))
        (= :previous (:targets program))
        (assoc :targets :previous)
        (and program (seq (get-in instance [:definition :targets])))
        (assoc :target-ids (get-in instance [:definition :targets]))
        (and program (nil? slot) (= :previous (:targets program))
             (empty? (get-in instance [:definition :targets])))
        (assoc :inherit-backdrop? true)))))

(defn- descriptor
  [compiled {:keys [instance intents expired? clock paused? input-state delta-ms number]}]
  (let [step (get compiled (:definition instance))]
    {:id (:id instance) :priority (:priority instance) :order (:order instance)
     :state (:state instance) :instance instance
     :step (fn [context]
             (let [private-frame (-> (:frame context)
                                     (merge (select-keys clock [:time-ms :beat :bpm :meter :playing?]))
                                     (assoc :delta-ms delta-ms :number number)
                                     (update :transport merge (select-keys clock [:beat :bpm :meter :playing?])))
                   step-instance (cond-> instance
                                   (system/system-release? instance) (assoc :phase :running))
                   result (if expired?
                            (assoc context :done? true)
                            (step (assoc context :frame private-frame :instance step-instance :state input-state)))
                   valid? (valid-step-shape? result)
                   ;; Validate block shapes before opacity can discard a hidden
                   ;; contribution, preserving the kernel failure contract.
                   _ (when valid? (runtime/append-contributions result []))
                   result (if valid?
                            (let [gain (* (get-in instance [:system :opacity] 1.0) (system/gain instance clock))]
                              (if-let [layer (native-layer instance)]
                                (let [tag (assoc layer :member-opacity gain)
                                      flushed (runtime/append-contributions result [])
                                      blocks (cond-> (:contributions flushed)
                                               (and (or (= :previous (:targets layer)) (seq (:target-ids layer)))
                                                    (not expired?)
                                                    (not (:done? result)) (empty? (:contributions flushed)))
                                               (conj {:kind :assignments :assignments []}))]
                                  (assoc flushed :contributions (mapv #(assoc % :native-layer tag) blocks)))
                                (with-opacity result gain)))
                            result)
                   ;; Paused steps regenerate owned output buffers at the frozen
                   ;; input, but cannot advance state, fire intents or finish.
                   result (if (and paused? valid?)
                            (assoc result :state (:state instance) :done? false :intents []) result)
                   result (if (and (system/system-release? instance) (not expired?) valid?)
                            (assoc result :done? false) result)]
               (if (and (map? result) (vector? (:intents result)))
                 (update result :intents
                         (fn [effect-intents]
                           (cond-> (into (vec intents) effect-intents)
                             (true? (:done? result))
                             (conj {:type :instance/finished :instance-id (:id instance)
                                    :reason (if expired? :release-complete :effect-complete)}))))
                 result)))}))

(defn- prepare-isolated [model clock snapshot instance]
  (let [current (get-in model [:registry :effects (:effect-id instance)])
        candidate? (and (not (get-in instance [:system :paused?]))
                        (not= :pinned (:reload-policy instance :pinned)) current
                        (not= (:version current) (:effect-version instance))
                        (not= (:version current) (get-in instance [:reload-fault :effect-version])))
        fallback-model (if candidate? (update-in model [:registry :effects] dissoc (:effect-id instance)) model)
        fallback (prepare-instance fallback-model clock snapshot instance)]
    (try
      (let [candidate (if candidate? (prepare-instance model clock snapshot instance) fallback)]
        (assoc candidate :before instance :fallback fallback
               :candidate? (not= (:effect-version instance) (get-in candidate [:instance :effect-version]))))
      (catch Throwable error
        (let [fault (faults/diagnostic snapshot instance
                                       (get-in model [:registry :effects (:effect-id instance) :version]) :reload error)]
          (-> fallback
              (assoc :before instance :fallback fallback :candidate? false)
              (assoc-in [:instance :reload-fault] fault)
              (update :intents conj (faults/event :effect/reload-failed fault))))))))

(defn- compile-isolated [compile-effect definition]
  (try
    (let [step (compile-effect definition)]
      (when-not (ifn? step)
        (fail! ::invalid-compiler-result "Compiler must return a callable step" {:effect-id (:id definition)}))
      {:step step})
    (catch Throwable error
      (when-not (faults/recoverable? error) (throw error))
      {:error error})))

(defn- silent-result [prepared]
  {:id (get-in prepared [:instance :id]) :instance (:instance prepared)
   :state (get-in prepared [:instance :state]) :assignments [] :contributions []
   :intents (:intents prepared) :done? false})

(defn- attempt [snapshot compiled prepared]
  (let [instance (:instance prepared) {:keys [step error]} (get compiled (:definition instance))]
    (cond
      (and (not (:expired? prepared))
           (= (:effect-version instance) (get-in instance [:fault :effect-version])))
      (assoc (silent-result prepared) :skipped? true)

      (and error (not (:expired? prepared)))
      {:failure (faults/diagnostic snapshot instance (:effect-version instance) :compile error)}

      :else
      (try
        (let [value (runtime/evaluate-instance snapshot (descriptor {(:definition instance) step} prepared))
              source (assoc (select-keys instance [:effect-id :effect-version :cue-id]) :instance-id (:id instance))]
          (-> value
              (assoc :instance instance)
              (update :contributions #(mapv (fn [block] (cond-> (assoc block :source source)
                                                       (not (== 1.0 (get-in instance [:system :gain] 1.0)))
                                                       (assoc :emission-gain (get-in instance [:system :gain])))) %))))
        (catch Throwable error
          {:failure (faults/diagnostic snapshot instance (:effect-version instance)
                                       (if (some #(#{:afterglow.runtime/invalid-result :afterglow.runtime/invalid-contributions}
                                                   (:type (ex-data %)))
                                                 (take 4 (take-while some? (iterate #(.getCause ^Throwable %) error))))
                                         :result :evaluate) error)})))))

(defn- evaluate-isolated [snapshot compiled prepared]
  (let [result (attempt snapshot compiled prepared)
        candidate? (:candidate? prepared)
        before (:before prepared)
        fault (:failure result)
        [result prepared]
        (if (and fault candidate?)
          (let [fallback (-> (:fallback prepared)
                             (assoc :before before :candidate? false)
                             (assoc-in [:instance :reload-fault] fault)
                             (update :intents conj (faults/event :effect/reload-failed fault)))]
            [(attempt snapshot compiled fallback) fallback])
          [result prepared])
        succeeded? (and (nil? (:failure result)) (not (:skipped? result)))
        result (if-let [failure (:failure result)]
                 (-> (silent-result prepared)
                     (assoc-in [:instance :fault] failure)
                     (update :intents conj (faults/event :effect/failed failure)))
                 result)
        recovered? (and (nil? fault) succeeded? (not (:expired? prepared))
                        (or (and candidate? (or (:fault before) (:reload-fault before)))
                            (:retry-fault before)))
        result (cond-> (update result :instance dissoc :retry-fault)
                 (and candidate? (nil? fault)) (update :instance dissoc :fault :reload-fault))
        result (cond-> result recovered?
                 (update :intents conj
                         (merge (select-keys snapshot [:show-id :epoch :time-ms :number])
                                {:type :effect/recovered :instance-id (:id before) :cue-id (:cue-id before)
                                 :effect-id (:effect-id before) :effect-version (get-in result [:instance :effect-version])})))]
    (assoc result :before before :prepared prepared)))

(defn- assemble [model snapshot descriptors evaluations]
  (let [evaluated (runtime/merge-results {:frame snapshot :effects descriptors} evaluations)
        instances (into {} (keep (fn [result]
                                  (when-not (:done? result)
                                    [(:id result) (assoc (:instance result) :state (:state result))]))) evaluations)
        events (filterv #(#{:effect/failed :effect/reload-failed :effect/recovered} (:type %)) (:intents evaluated))]
    {:model (faults/record-events (assoc model :instances instances) events)
     :assignments (:assignments evaluated) :contributions (:contributions evaluated) :intents (:intents evaluated)
     :fault-events events
     ;; Private evaluation records never enter the model or a saved show. A
     ;; renderer can reject one malformed output without running healthy code twice.
     ::evaluation {:model model :snapshot snapshot :descriptors descriptors :results evaluations}}))

(defn reject-output
  "Reject one renderer-attributed output, preserving all other evaluated results.
  Unknown/global errors and a repeated rejection remain whole-frame failures."
  [result error]
  (let [{:keys [model snapshot descriptors results]} (::evaluation result)
        source (:effect-source (ex-data error))
        index (first (keep-indexed #(when (= (:instance-id source) (:id %2)) %1) results))
        evaluated (when (some? index) (nth results index))]
    (when-not (and evaluated (not (:output-rejected? evaluated))
                   (= (:effect-version source) (get-in evaluated [:instance :effect-version])))
      (throw error))
    (let [prepared (:prepared evaluated) before (:before evaluated)
          failed (:instance evaluated)
          diagnostic (faults/diagnostic snapshot failed (:effect-version failed) :output error)
          candidate? (not= (:effect-version before) (:effect-version failed))
          prepared (if candidate? (:fallback prepared) prepared)
          next (-> (silent-result prepared)
                   (update :instance dissoc :retry-fault)
                   (assoc :before before :prepared prepared :output-rejected? true)
                   (assoc-in [:instance (if candidate? :reload-fault :fault)] diagnostic)
                   (update :intents conj (faults/event (if candidate? :effect/reload-failed :effect/failed) diagnostic)))]
      (assemble model snapshot descriptors (assoc results index next)))))

(defn advance
  "Advance the new control model by one fully evaluated frame.

  frame requires nonnegative :time-ms. Optional :epoch and :show-id reject stale
  work; the shell should always provide them. :delta-ms defaults to elapsed time
  since the prior rendered frame. Registry definitions are captured at launch;
  default :reload-policy :pinned keeps them. :preserve-state adopts a newer
  definition while retaining state/time; :restart resets state and start time.
  Both opt-in policies retain common parameter values and add new defaults.
  Retained parameters must validate against new schemas; a rejected candidate
  retains and evaluates the captured last-good revision.
  Captured authored durations remain fixed until relaunch. Explicit system AR
  controls are independent and can be edited through the command reducer.
  System pause freezes private time/beat/frame number and effect state, then
  regenerates output from the last input state without repeating intents. Manual
  parameters and other frame inputs remain live. Resume advances private clocks
  without consuming the paused interval. No typed result buffers enter the model.
  System opacity weights the blend result, never authored parameter values.
  A removed registry definition leaves captured running instances valid.

  Duration expiry enters release at the exact logical deadline. During a positive
  :release-duration-ms the compiled step sees the releasing instance and owns its
  envelope. At the release deadline the instance contributes nothing and is
  removed. A step can finish earlier with :done? true, retaining that final frame.
  Finite one-shot launch validation belongs to the command reducer.

  compile-effect is called once per distinct definition needed by this frame.
  Supply an explicitly owned bounded compiler cache at the shell if desired.
  Optional map-work follows afterglow.runtime/render-frame's blocking contract.
  Recoverable effect failures quarantine that revision without publishing its
  attempted state/output/intents. Healthy effects continue. A newer revision or
  explicit :instance/retry permits another attempt. Global model/executor errors
  and cancellation still fail the frame. :contributions retains ordered typed and
  ordinary blocks; :assignments is nil if any batch is present. Consumers of a
  batch compiler must resolve the contribution stream, never just assignments.
  No hardware output or external work happens here.

  Command :revision is preserved; :frame-number advances. Asynchronous shells
  must compare [epoch revision frame-number] before committing a frame, or use a
  single owner that drains commands and evaluates frames sequentially."
  ([model frame compile-effect]
   (advance model frame compile-effect mapv))
  ([model frame compile-effect map-work]
   (validate-input! model frame compile-effect)
   (let [time-ms (:time-ms frame)
         frame-number (inc (get model :frame-number 0))
         delta-ms (get frame :delta-ms (- time-ms (get model :last-frame-time-ms (:time-ms model))))
         _ (when-not (nonnegative-number? delta-ms)
             (fail! ::invalid-delta "Computed frame delta must be nonnegative" {}))
         snapshot (merge {:fixtures []} frame
                         {:show-id (:show-id model) :epoch (:epoch model)
                          :revision (:revision model) :number frame-number
                          :time-ms time-ms :delta-ms delta-ms
                          :variables (:variables model) :master (:master model)
                          :blackout? (:blackout? model) :transport (:transport model)})
         clock (musical-time/frame-clock snapshot)
         _ (when (and (some? (:last-frame-beat model)) (some? (:beat clock))
                      (< (:beat clock) (:last-frame-beat model)))
             (fail! ::stale-beat "Transport beat cannot move backwards within a show epoch" {}))
         prepared (mapv (partial prepare-isolated model clock snapshot)
                        (sort-by (juxt :priority :order :id) (vals (:instances model))))
         definitions (distinct (map (comp :definition :instance)
                                    (remove #(or (:expired? %) (= (get-in % [:instance :effect-version])
                                                                  (get-in % [:instance :fault :effect-version])))
                                            (mapcat #(cond-> [%] (:candidate? %) (conj (:fallback %))) prepared))))
         compiled (into {} (map (fn [definition] [definition (compile-isolated compile-effect definition)])) definitions)
         descriptors (mapv #(assoc (select-keys (:instance %) [:id :priority :order :state]) :step identity) prepared)
         evaluations (vec (map-work (partial evaluate-isolated snapshot compiled) prepared))
         ;; Worker completion order is deliberately discarded before the model,
         ;; fault journal and result records are assembled.
         evaluations (vec (sort-by (juxt #(get-in % [:instance :priority])
                                         #(get-in % [:instance :order]) :id) evaluations))]
     (assemble (assoc model :time-ms time-ms :last-frame-time-ms time-ms
                            :last-frame-beat (:beat clock) :frame-number frame-number)
               snapshot descriptors evaluations))))
