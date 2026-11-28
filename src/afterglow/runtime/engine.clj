(ns afterglow.runtime.engine
  "Pure show-model coordinator for the declarative runtime.

  This is a working runtime for the new control model, separate from the legacy
  afterglow.show scheduler. The shell captures time, owns the executor/compiler
  cache and commits a successful result before performing returned intents."
  (:require [afterglow.runtime :as runtime]
            [afterglow.runtime.faults :as faults]
            [afterglow.runtime.keyframes :as keyframes]
            [afterglow.time :as musical-time]
            [afterglow.control.effect-selection :as effect-selection]
            [afterglow.control.model :as control]
            [afterglow.control.instance-order :as instance-order]
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

(defn- unit-opacity? [value]
  (and (finite-number? value) (<= 0 value 1)))

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
                 (instance-order/valid-render-position? instance)
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
  (when-not (control/reload-policies (or (:reload-policy instance) :pinned))
    (fail! ::invalid-reload-policy "Unknown instance reload policy" {:instance-id id}))
  (doseq [field [:duration :release-duration] :when (contains? instance field)]
    (when (seq (musical-time/validate-duration (get instance field)))
      (fail! ::invalid-duration "Invalid musical duration" {:instance-id id :field field}))))

(defn- validate-render-inputs!
  "Check the frame-local render inputs of a frame or of its reload fallback."
  [model frame]
  (let [factors (get frame ::opacity-factors {})]
    (when-not (map? factors)
      (fail! ::invalid-opacity-factors "Expected an instance ID to opacity factor map" {}))
    (doseq [[id factor] factors]
      (when-not (and (contains? (:instances model) id)
                     (if (map? factor)
                       (every? (fn [[version value]]
                                 (and (integer? version) (pos? version) (unit-opacity? value))) factor)
                       (unit-opacity? factor)))
        (fail! ::invalid-opacity-factors "Active instance opacity factors must be in [0,1], optionally by definition version"
               {:instance-id id :factor factor}))))
  (when-let [errors (seq (instance-order/priority-override-errors
                           (:instances model) (get frame ::priority-overrides {})))]
    (fail! ::invalid-priority-overrides "Frame priority overrides must be finite and agree within native layers"
           {:errors (vec errors)})))

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
  (validate-render-inputs! model frame)
  (when (contains? frame ::reload-fallback)
    (let [fallback (::reload-fallback frame)]
      (when-not (and (map? fallback)
                     (not-any? #(contains? fallback %) [:time-ms :delta-ms :epoch :show-id ::reload-fallback]))
        (fail! ::invalid-reload-fallback
               "Reload fallback inputs must be a map without frame time or show identity" {}))
      (validate-render-inputs! model fallback)))
  (doseq [[id instance] (:instances model)]
    (validate-instance! id instance)))

(deftype MigratingStep [step meta-map]
  ;; Delegates the one-argument step call directly. Plain vary-meta on a fn
  ;; returns a variadic RestFn that goes through applyTo on every frame.
  clojure.lang.IFn
  (invoke [_ context] (step context))
  (applyTo [_ args] (.applyTo ^clojure.lang.IFn step args))
  clojure.lang.IMeta
  (meta [_] meta-map)
  clojure.lang.IObj
  (withMeta [_ m] (MigratingStep. step m)))

(defn with-state-migration
  "Attach a pure state migration to a compiled step. A :migrate reload calls
  (migrate old-state old-version new-version context) once, at the frame where
  the newer definition takes over, before that step first runs. context holds
  portable data: instance/cue/effect identity, both captured definitions, the
  retained parameters and the frame/clock. The function must not perform IO,
  read clocks or own RNG; it runs on a frame worker outside any CAS retry."
  [step migrate]
  (when-not (or (fn? migrate) (var? migrate))
    (fail! ::invalid-state-migration "A state migration must be a function" {}))
  (let [inner (if (instance? MigratingStep step) (.-step ^MigratingStep step) step)]
    (MigratingStep. inner (assoc (meta step) ::state-migration migrate))))

(defn state-migration
  "Return the state migration attached to a compiled step, or nil."
  [step]
  (::state-migration (meta step)))

(defn opacity-factor
  "Read the frame opacity factor for an instance and its evaluated definition version."
  [factors id version]
  (let [factor (get factors id 1)]
    (if (map? factor) (get factor version 1) factor)))

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

(defn launch-program
  "The program `advance` compiles for a launch of `definition` with launch
  `targets`: the definition narrowed to those targets. This value is the
  compile key, so hosts that compile ahead of the frame must key their
  programs with it rather than repeat the rule.

  - nil `targets` (an untargeted launch) leaves the definition unchanged;
  - with authored `:targets`, the launch keeps the authored targets it
    names, in launch order; targets the definition does not author are
    dropped, so a disjoint set narrows to `[]`;
  - without authored `:targets`, the launch targets are used as given.

  The captured registry definition stays on the instance verbatim for reload,
  validation and persistence."
  [definition targets]
  (if (nil? targets) definition
      (assoc definition :targets (if-let [authored (:targets definition)]
                                   (filterv (set authored) targets)
                                   targets))))

(defn- render-definition
  "Narrow a compiled program for one launch (see `launch-program`)."
  [{:keys [definition targets]}]
  (launch-program definition targets))

(defn instance-lifecycle
  "Read a live instance at this frame's private clock, before running its step.
  Includes compatible reloads, the exact release boundary and positive envelope
  tails. Hosts can scope owned resources to precisely the frames that render."
  [model global-clock instance]
  (let [paused? (true? (get-in instance [:system :paused?]))
        clock (system/private-clock instance global-clock)
        [reloaded intents] (if paused? [instance []] (reload-instance (:registry model) clock instance))
        prepared (if paused? reloaded (release-if-expired model clock reloaded))]
    {:instance prepared :intents intents :clock clock :paused? paused?
     :expired? (and (not paused?) (release-finished? clock prepared))}))

(defn- prepare-instance
  [model global-clock snapshot instance]
  (let [{prepared :instance :keys [clock paused?] :as lifecycle} (instance-lifecycle model global-clock instance)
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
    (assoc lifecycle :instance prepared :program (render-definition prepared)
           :input-state input-state :delta-ms delta :number number)))

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

(defn- native-layer [instance program-definition]
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
        (assoc :inherit-backdrop? true)
        (contains? instance :targets)
        (-> (dissoc :targets :inherit-backdrop?)
            (assoc :target-ids (:targets program-definition)))))))

(defn- descriptor
  [step opacity-factor {:keys [instance program intents expired? clock paused? input-state delta-ms number]}]
  (let [instance (assoc instance :definition program)]
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
                            (let [ctx (assoc context :frame private-frame :instance step-instance :state input-state)]
                              (if (or (:keyframes program) (keyframes/dependency-driven? step)
                                      (:measure-effect private-frame) (seq (:keyframe-intervals private-frame)))
                                (keyframes/evaluate step ctx) (step ctx))))
                   valid? (valid-step-shape? result)
                   ;; Validate block shapes before opacity can discard a hidden
                   ;; contribution, preserving the kernel failure contract.
                   _ (when valid? (runtime/append-contributions result []))
                   result (if valid?
                            (let [gain (* (get-in instance [:system :opacity] 1.0) (system/gain instance clock))
                                  gain (if (== 1 opacity-factor) gain (* gain opacity-factor))]
                              (if-let [layer (native-layer instance program)]
                                (let [tag (assoc layer :member-opacity gain)
                                      flushed (runtime/append-contributions result [])
                                      blocks (cond-> (:contributions flushed)
                                               (and (or (= :previous (:targets layer)) (seq (:target-ids layer)))
                                                    (not expired?)
                                                    (not (::keyframes/inputs-unavailable? result))
                                                    (empty? (:contributions flushed)))
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
      (let [candidate (if candidate? (prepare-instance model clock snapshot instance) fallback)
            adopted? (not= (:effect-version instance) (get-in candidate [:instance :effect-version]))]
        (cond-> (assoc candidate :before instance :fallback fallback :candidate? adopted?)
          ;; The candidate keeps the old state until its step's migration runs.
          (and adopted? (= :migrate (:reload-policy instance)))
          (assoc :migration {:state (:state instance) :from-version (:effect-version instance)
                             :from-definition (:definition instance) :clock (:clock candidate)})))
      (catch Throwable error
        (let [fault (faults/diagnostic snapshot instance
                                       (get-in model [:registry :effects (:effect-id instance) :version]) :reload error)]
          (-> fallback
              (assoc :before instance :fallback fallback :candidate? false :prepare-failed? true)
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

(defn- portable-state?
  "Plain EDN only: no functions, records, mutable/host objects, lazy or
  unbounded sequences, or non-finite floating-point numbers."
  [value]
  (cond
    (or (nil? value) (boolean? value) (string? value) (char? value)
        (keyword? value) (symbol? value) (uuid? value) (inst? value)) true
    (or (integer? value) (ratio? value) (decimal? value)) true
    (float? value) (Double/isFinite (double value))
    (record? value) false
    (map? value) (every? (fn [[k v]] (and (portable-state? k) (portable-state? v))) value)
    (or (vector? value) (set? value) (list? value)) (every? portable-state? value)
    :else false))

(defn- migrate-prepared
  "Run a pending :migrate transform for the candidate definition. Returns the
  prepared lifecycle with migrated state, or a :migrate fault diagnostic."
  [snapshot step prepared]
  (let [{:keys [state from-version from-definition clock]} (:migration prepared)
        instance (:instance prepared)
        to-version (:effect-version instance)
        migrate (state-migration step)
        context {:instance-id (:id instance) :cue-id (:cue-id instance) :effect-id (:effect-id instance)
                 :from-definition from-definition :to-definition (:definition instance)
                 :params (:params instance)
                 :frame (select-keys snapshot [:show-id :epoch :revision :number :time-ms])
                 :clock (select-keys clock [:time-ms :beat :bpm :meter :playing?])}]
    (try
      (when-not (ifn? migrate)
        (fail! ::missing-state-migration "The new definition declares no state migration"
               {:path [:state-migration] :from-version from-version :to-version to-version}))
      (let [migrated (try (migrate state from-version to-version context)
                          (catch Throwable error
                            (when-not (faults/recoverable? error) (throw error))
                            (throw (ex-info "State migration failed"
                                            {:type ::state-migration-failed :path [:state-migration]
                                             :from-version from-version :to-version to-version} error))))]
        (when-not (portable-state? migrated)
          (fail! ::invalid-migrated-state "A state migration must return plain EDN state data"
                 {:path [:state-migration] :from-version from-version :to-version to-version}))
        {:prepared (-> prepared
                       (dissoc :migration)
                       (assoc :input-state migrated)
                       (assoc-in [:instance :state] migrated)
                       (assoc-in [:instance :system :last-input-state] migrated))})
      (catch Throwable error
        {:failure (assoc (faults/diagnostic snapshot instance to-version :migrate error)
                         :from-version from-version)}))))

(defn- silent-result [prepared]
  {:id (get-in prepared [:instance :id]) :instance (:instance prepared)
   :state (get-in prepared [:instance :state]) :assignments [] :contributions []
   :intents (:intents prepared) :done? false})

(defn- attempt [snapshot compiled factors prepared]
  (let [instance (:instance prepared) {:keys [step error]} (get compiled (:program prepared))]
    (cond
      (and (not (:expired? prepared))
           (= (:effect-version instance) (get-in instance [:fault :effect-version])))
      (assoc (silent-result prepared) :skipped? true)

      (and error (not (:expired? prepared)))
      {:failure (faults/diagnostic snapshot instance (:effect-version instance) :compile error)}

      (and (:migration prepared) (not (:expired? prepared)))
      (let [{migrated :prepared :keys [failure]} (migrate-prepared snapshot step prepared)]
        (if failure {:failure failure} (attempt snapshot compiled factors migrated)))

      :else
      (try
        (let [factor (opacity-factor factors (:id instance) (:effect-version instance))
              value (runtime/evaluate-instance snapshot (descriptor step factor prepared))
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

(defn- rejected-fallback
  "The captured last-good revision of a rejected reload candidate, carrying the fault."
  [prepared fault]
  (-> (:fallback prepared)
      (assoc :before (:before prepared) :candidate? false)
      (assoc-in [:instance :reload-fault] fault)
      (update :intents conj (faults/event :effect/reload-failed fault))))

(defn- deferred-fallback
  "The captured revision of a healthy reload candidate that waits for a later frame."
  [prepared]
  (assoc (:fallback prepared) :before (:before prepared) :candidate? false))

(defn- settle
  "Complete one instance from its first attempt. A rejected reload candidate
  evaluates the captured last-good revision in its place."
  [snapshot compiled factors prepared result]
  (let [candidate? (:candidate? prepared)
        before (:before prepared)
        fault (:failure result)
        [result prepared]
        (if (and fault candidate?)
          (let [fallback (rejected-fallback prepared fault)]
            [(attempt snapshot compiled factors fallback) fallback])
          [result prepared])
        succeeded? (and (nil? (:failure result)) (not (:skipped? result)))
        result (if-let [failure (:failure result)]
                 (-> (silent-result prepared)
                     (assoc-in [:instance :fault] failure)
                     (update :intents conj (faults/event :effect/failed failure)))
                 result)
        recovered? (and (not (:prepare-failed? prepared)) (nil? fault) succeeded? (not (:expired? prepared))
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

(defn- evaluate-isolated [snapshot compiled factors prepared]
  (settle snapshot compiled factors prepared (attempt snapshot compiled factors prepared)))

(defn- assemble
  ([model snapshot descriptors evaluations] (assemble model snapshot descriptors evaluations nil))
  ([model snapshot descriptors evaluations {:keys [reload-inputs fallback]}]
   (let [live-instances (eduction (remove #(get-in % [:prepared :expired?])) (map :instance) evaluations)
         suppressed (effect-selection/suppressed-instance-ids live-instances)
         evaluated (runtime/merge-results {:frame snapshot :effects descriptors ::runtime/suppressed-instance-ids suppressed}
                                          evaluations)
         instances (into {} (keep (fn [result]
                                   (when-not (:done? result)
                                     [(:id result) (runtime/observable-instance result)]))) evaluations)
         next-model (control/track-parameter-generations model (assoc model :instances instances))
         events (filterv #(#{:effect/failed :effect/reload-failed :effect/recovered} (:type %)) (:intents evaluated))]
     (cond-> {:model (faults/record-events next-model events)
              :assignments (:assignments evaluated) :contributions (:contributions evaluated) :intents (:intents evaluated)
              :keyframes (keyframes/committed-windows snapshot evaluations)
              :fault-events events
              ;; Private evaluation records never enter the model or a saved show. A
              ;; renderer can reject one malformed output without running healthy code twice.
              ;; :fallback re-evaluates a frame that supplied ::reload-fallback when the
              ;; renderer rejects a reload candidate it had accepted.
              ::evaluation (cond-> {:model model :snapshot snapshot :descriptors descriptors :results evaluations}
                             reload-inputs (assoc :reload-inputs reload-inputs)
                             fallback (assoc :fallback fallback))}
       reload-inputs (assoc :reload-inputs reload-inputs)
       (seq (:intent-emissions evaluated)) (assoc :intent-emissions (:intent-emissions evaluated))))))

(defn reject-output
  "Reject one renderer-attributed output, preserving all other evaluated results.
  Unknown/global errors and a repeated rejection remain whole-frame failures.
  A rejected reload candidate in a frame that supplied ::reload-fallback is the
  one exception to keeping the other results: that frame is evaluated again on
  its fallback inputs, as it is for every earlier rejection stage."
  [result error]
  (let [{:keys [model snapshot descriptors results reload-inputs fallback]} (::evaluation result)
        source (:effect-source (ex-data error))
        index (first (keep-indexed #(when (= (:instance-id source) (:id %2)) %1) results))
        evaluated (when (some? index) (nth results index))]
    (when-not (and evaluated (not (:output-rejected? evaluated))
                   (= (:effect-version source) (get-in evaluated [:instance :effect-version])))
      (throw error))
    (let [prepared (:prepared evaluated) before (:before evaluated)
          failed (:instance evaluated)
          diagnostic (faults/diagnostic snapshot failed (:effect-version failed) :output error)
          candidate? (not= (:effect-version before) (:effect-version failed))]
      (if (and candidate? fallback)
        (fallback {(:id failed) diagnostic})
        (let [prepared (if candidate? (:fallback prepared) prepared)
              next (-> (silent-result prepared)
                       (update :instance dissoc :retry-fault)
                       (assoc :before before :prepared prepared :output-rejected? true)
                       (assoc-in [:instance (if candidate? :reload-fault :fault)] diagnostic)
                       (update :intents conj (faults/event (if candidate? :effect/reload-failed :effect/failed) diagnostic)))]
          (assemble model snapshot descriptors (assoc results index next)
                    {:reload-inputs reload-inputs :fallback fallback}))))))

(defn- frame-inputs
  "Freeze the inputs one evaluation pass reads from a frame: the shared snapshot,
  the frame-local opacity factors and the render positions."
  [model frame time-ms delta-ms frame-number]
  (let [snapshot (merge {:fixtures []} (dissoc frame ::opacity-factors ::priority-overrides ::reload-fallback)
                        {:show-id (:show-id model) :epoch (:epoch model)
                         :revision (:revision model) :number frame-number
                         :time-ms time-ms :delta-ms delta-ms
                         :variables (get frame :resolved-variables (:variables model)) :master (:master model)
                         :blackout? (:blackout? model) :transport (:transport model)})]
    {:snapshot (assoc snapshot :transport-clock (musical-time/frame-clock snapshot))
     :factors (::opacity-factors frame)
     ;; Resolve modulated layer priority once from this frozen frame input.
     :positions (instance-order/with-priority-overrides (:instances model) (::priority-overrides frame))}))

(defn advance
  "Advance the new control model by one fully evaluated frame.

  frame requires nonnegative :time-ms. Optional :epoch and :show-id reject stale
  work; the shell should always provide them. :delta-ms defaults to elapsed time
  since the prior rendered frame. Registry definitions are captured at launch;
  default :reload-policy :pinned keeps them. :preserve-state adopts a newer
  definition while retaining state/time; :restart resets state and start time.
  :migrate retains time and transforms state once through the pure function
  attached to the new compiled step (with-state-migration); a missing or failing
  migration is a :migrate reload fault that keeps the last good revision/state.
  The opt-in policies retain common parameter values and add new defaults.
  Retained parameters must validate against new schemas; a rejected candidate
  retains and evaluates the captured last-good revision.
  Captured authored durations remain fixed until relaunch. Explicit system AR
  controls are independent and can be edited through the command reducer.
  System pause freezes private time/beat/frame number and effect state, then
  regenerates output from the last input state without repeating intents. Manual
  parameters and other frame inputs remain live. Resume advances private clocks
  without consuming the paused interval. :frame :transport-clock is the shared
  time, beat and meter captured before any private offsets. No typed result
  buffers enter the model.
  System opacity weights the blend result, never authored parameter values.
  The optional ::opacity-factors frame input maps active instance IDs to a unit
  factor or a sparse map from definition version to unit factor. Unspecified
  factors default to unity. Reloads and their fallbacks each use the factor for
  the definition being evaluated. The factor multiplies the instance's system
  opacity and AR level at the contribution boundary, including native member
  opacity. Factors stay outside the effect context and committed instance.
  A removed registry definition leaves captured running instances valid.

  Solo and Mute filter contributions without interrupting private clocks, effect
  state or intents. An expired instance leaves the selection before the frame
  is composed. A step that finishes during evaluation is still eligible to
  contribute to that frame.

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
  Nonempty :intents have a same-order :intent-emissions companion containing
  their source instance, definition identity and launch adapter when present.
  No hardware output or external work happens here.

  Optional ::priority-overrides maps instance IDs to finite priorities for this
  frame only, such as a modulated layer priority sampled by the show owner. It
  reorders evaluation and contribution merging without changing the model. An
  overriding value places the instance (or its whole native layer) in that tier,
  tied with equal priorities by launch order. Unknown IDs are ignored.

  Optional ::reload-fallback is a map of frame inputs that replace the frame's
  own whenever this frame rejects a hot reload. A host supplies it when inputs
  it computed before the frame, such as modulated parameters, already follow a
  newer definition and would be wrong for the captured last-good revision. With
  it the frame reads one input set throughout. Reload candidates are attempted
  first on the frame's own inputs. If every candidate is accepted, the other
  instances evaluate on those inputs too. If any candidate is rejected at
  preparation, compilation, migration or evaluation, every instance evaluates
  its captured revision on the merged fallback inputs: the rejected candidates
  record their reload fault as usual, and the accepted ones stay candidates,
  without a fault, for the next frame. The fallback may carry any frame input,
  including ::opacity-factors and ::priority-overrides, but not :time-ms,
  :delta-ms, :epoch or :show-id. The result's :reload-inputs is :frame or
  :fallback and names the set that was read; it is absent when no fallback was
  supplied. The host commits whatever state produced that set. A frame with
  candidates makes two mapping calls, each with its own executor deadline.

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
         inputs (fn [frame] (frame-inputs model frame time-ms delta-ms frame-number))
         {:keys [snapshot] :as own} (inputs frame)
         clock (:transport-clock snapshot)
         _ (when (and (some? (:last-frame-beat model)) (some? (:beat clock))
                      (< (:beat clock) (:last-frame-beat model)))
             (fail! ::stale-beat "Transport beat cannot move backwards within a show epoch" {}))
         prepared (mapv (fn [positioned] (prepare-isolated model clock snapshot (get-in model [:instances (:id positioned)])))
                        (sort instance-order/render-instance-comparator (vals (:positions own))))
         definitions (distinct (map :program
                                    (remove #(or (:expired? %) (= (get-in % [:instance :effect-version])
                                                                  (get-in % [:instance :fault :effect-version])))
                                            (mapcat #(cond-> [%] (:candidate? %) (conj (:fallback %))) prepared))))
         with-rig (fn [inputs frame]
                    (cond-> inputs
                      (or (seq (:keyframes frame)) (seq (:keyframe-intervals frame)) (some :keyframes definitions))
                      (update :snapshot keyframes/with-rig-positions)))
         own (with-rig own frame)
         compiled (into {} (map (fn [definition] [definition (compile-isolated compile-effect definition)])) definitions)
         next-model (assoc model :time-ms time-ms :last-frame-time-ms time-ms
                                 :last-frame-beat (:beat clock) :frame-number frame-number)
         render-keys [:priority :order :render-priority :render-order]
         ;; Worker completion order is deliberately discarded before the model,
         ;; fault journal and result records are assembled.
         finish (fn [{:keys [snapshot positions]} entries evaluations reload]
                  (let [position-of (fn [instance] (get positions (:id instance) instance))]
                    (assemble next-model snapshot
                              (mapv #(let [instance (:instance %)]
                                       (assoc (merge (select-keys instance [:id :state])
                                                     (select-keys (position-of instance) render-keys))
                                              :step identity)) entries)
                              (vec (sort-by (comp position-of :instance) instance-order/render-instance-comparator evaluations))
                              reload)))
         evaluate (fn [{:keys [snapshot factors]} entries]
                    (vec (map-work (partial evaluate-isolated snapshot compiled factors) entries)))
         fallback-frame (when (contains? frame ::reload-fallback) (merge frame (::reload-fallback frame)))
         candidates (when fallback-frame (filterv :candidate? prepared))]
     (if-not (or (seq candidates) (and fallback-frame (some :prepare-failed? prepared)))
       (finish own prepared (evaluate own prepared) (when fallback-frame {:reload-inputs :frame}))
       ;; Reload candidates decide which inputs this whole frame reads, so they
       ;; are attempted first and nothing else has evaluated when one is rejected.
       (let [instance-id (fn [entry] (get-in entry [:instance :id]))
             trials (if (seq candidates)
                      (into {} (map-work (fn [entry] [(instance-id entry) (attempt (:snapshot own) compiled (:factors own) entry)])
                                         candidates))
                      {})
             rejected (into {} (keep (fn [[id result]] (when-let [failure (:failure result)] [id failure]))) trials)
             fallback-inputs (delay (with-rig (inputs fallback-frame) fallback-frame))
             evaluate-fallback
             (fn [rejected]
               (let [{:keys [snapshot factors] :as fallback} @fallback-inputs
                     evaluate-entry (fn [entry]
                                      (if-let [fault (get rejected (instance-id entry))]
                                        (settle snapshot compiled factors entry {:failure fault})
                                        (evaluate-isolated snapshot compiled factors
                                                           (cond-> entry (:candidate? entry) deferred-fallback))))]
                 (finish fallback prepared (vec (map-work evaluate-entry prepared)) {:reload-inputs :fallback})))]
         (if (or (seq rejected) (some :prepare-failed? prepared))
           (evaluate-fallback rejected)
           (finish own prepared
                   (into (mapv #(settle (:snapshot own) compiled (:factors own) % (get trials (instance-id %))) candidates)
                         (evaluate own (filterv (complement :candidate?) prepared)))
                   {:reload-inputs :frame :fallback evaluate-fallback})))))))
