(ns afterglow.runtime.engine
  "Pure show-model coordinator for the declarative runtime.

  This is a working runtime for the new control model, separate from the legacy
  afterglow.show scheduler. The shell captures time, owns the executor/compiler
  cache and commits a successful result before performing returned intents."
  (:require [afterglow.runtime :as runtime]
            [afterglow.control.params :as params]))

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
    (fail! ::invalid-reload-policy "Unknown instance reload policy" {:instance-id id})))

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
  [registry time-ms instance]
  (let [policy (get instance :reload-policy :pinned)
        current (get-in registry [:effects (:effect-id instance)])]
    (if (and (not= :pinned policy) current
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
                                         :started-at-ms time-ms :phase :running)
                                  (dissoc :release-at-ms))
                              next-instance)]
          [next-instance [{:type :effect/reloaded :instance-id (:id instance)
                           :from-version (:effect-version instance) :to-version (:version current)
                           :policy policy}]]))
      [instance []])))

(defn- release-if-expired
  [time-ms instance]
  (if (and (= :running (:phase instance)) (:duration-ms instance)
           (>= time-ms (+ (:started-at-ms instance) (:duration-ms instance))))
    (assoc instance :phase :releasing
           :release-at-ms (+ (:started-at-ms instance) (:duration-ms instance)))
    instance))

(defn- release-finished?
  [time-ms instance]
  (and (= :releasing (:phase instance))
       (>= time-ms (+ (:release-at-ms instance) (get instance :release-duration-ms 0)))))

(defn- prepare-instance
  [model time-ms instance]
  (let [[reloaded intents] (reload-instance (:registry model) time-ms instance)
        prepared (release-if-expired time-ms reloaded)]
    (validate-instance! (:id prepared) prepared)
    {:instance prepared :intents intents :expired? (release-finished? time-ms prepared)}))

(defn- descriptor
  [compiled {:keys [instance intents expired?]}]
  (let [step (get compiled (:definition instance))]
    {:id (:id instance) :priority (:priority instance) :order (:order instance)
     :state (:state instance) :instance instance
     :step (fn [context]
             (let [result (if expired?
                            (assoc context :done? true)
                            (step context))]
               ;; The kernel validates the step output. Do not repair malformed
               ;; vectors here, since that would turn an effect failure into success.
               (if (and (map? result) (vector? (:intents result)))
                 (update result :intents
                         (fn [effect-intents]
                           (cond-> (into (vec intents) effect-intents)
                             (true? (:done? result))
                             (conj {:type :instance/finished :instance-id (:id instance)
                                    :reason (if expired? :release-complete :effect-complete)}))))
                 result)))}))

(defn advance
  "Advance the new control model by one fully evaluated frame.

  frame requires nonnegative :time-ms. Optional :epoch and :show-id reject stale
  work; the shell should always provide them. :delta-ms defaults to elapsed time
  since the prior rendered frame. Registry definitions are captured at launch;
  default :reload-policy :pinned keeps them. :preserve-state adopts a newer
  definition while retaining state/time; :restart resets state and start time.
  Both opt-in policies retain common parameter values and add new defaults.
  Retained parameters must validate against the new schemas or the frame fails.
  Launch duration and release duration remain fixed for an existing instance;
  relaunch to adopt changed timing defaults.
  A removed registry definition leaves captured running instances valid.

  Duration expiry enters release at the exact logical deadline. During a positive
  :release-duration-ms the compiled step sees the releasing instance and owns its
  envelope. At the release deadline the instance contributes nothing and is
  removed. A step can finish earlier with :done? true, retaining that final frame.
  Finite one-shot launch validation belongs to the command reducer.

  compile-effect is called once per distinct definition needed by this frame.
  Supply an explicitly owned bounded compiler cache at the shell if desired.
  Optional map-work follows afterglow.runtime/render-frame's blocking contract.
  Compilation, evaluation or validation failure throws without returning any new
  model, assignments or intents. No hardware output or external work happens here.

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
         prepared (mapv (partial prepare-instance model time-ms)
                        (sort-by (juxt :priority :order :id) (vals (:instances model))))
         definitions (distinct (map (comp :definition :instance) (remove :expired? prepared)))
         compiled (into {} (map (fn [definition]
                                 (let [step (compile-effect definition)]
                                   (when-not (ifn? step)
                                     (fail! ::invalid-compiler-result "Compiler must return a callable step"
                                            {:effect-id (:id definition)}))
                                   [definition step]))) definitions)
         evaluated (runtime/render-frame {:frame snapshot :effects (mapv (partial descriptor compiled) prepared)}
                                         map-work)
         instances (into {} (map (fn [result]
                                   [(:id result) (assoc (:instance result) :state (:state result))]))
                         (:effects evaluated))]
     {:model (assoc model :instances instances :time-ms time-ms
                    :last-frame-time-ms time-ms :frame-number frame-number)
      :assignments (:assignments evaluated) :intents (:intents evaluated)})))
