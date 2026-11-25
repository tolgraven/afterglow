(ns afterglow.control.model
  "Immutable show commands. Time and identity enter through the command envelope;
  accepted commands return event data, never start hardware or invoke user code."
  (:require [afterglow.runtime.events :as events]
            [afterglow.control.pages :as pages]
            [afterglow.control.params :as params]
            [afterglow.control.targets :as targets]
            [afterglow.time :as musical-time]
            [afterglow.control.categories :as categories]
            [afterglow.control.system :as system]))

(defn- reject! [code message & [details]]
  (throw (ex-info message {:control/error code :details details})))

(defn- require! [condition code message & [details]]
  (when-not condition (reject! code message details)))

(defn- identifier? [x] (or (keyword? x) (and (string? x) (not (empty? x)))))
(defn- duration? [x] (and (params/finite-number? x) (pos? x)))
(defn- nonnegative? [x] (and (params/finite-number? x) (<= 0 x)))

(defn- timing-option [sources field legacy-field]
  (some (fn [source]
          (cond (contains? source field) {:duration (get source field)}
                (contains? source legacy-field) {:legacy (get source legacy-field)})) sources))

(defn- check-duration! [duration positive?]
  (require! (and (empty? (musical-time/validate-duration duration))
                 (or (not positive?) (pos? (val (first duration)))))
            :invalid-duration "Duration must contain one valid beat, bar, phrase or ms value"))

(defn- clock [model time-ms]
  (musical-time/frame-clock {:time-ms time-ms :transport (:transport model)}))

(defn new-show
  "Create an inert model. Optional :history-limit bounds accepted-command retry
  receipts (default 1024). Initial registry/maps may be supplied by trusted code."
  ([] (new-show {}))
  ([initial]
   (require! (map? initial) :invalid-model "Initial show must be a map")
   (let [limit (get initial :history-limit 1024)
         model (merge {:show-id :main :epoch 0 :revision 0 :time-ms 0
                       :registry {:effects {} :cues {} :fixtures {} :versions {}}
                       :instances {} :pages {} :variables {}
                       :master 1.0 :blackout? false
                       :transport {:bpm 120 :playing? true :beat 0.0
                                   :meter {:beats-per-bar 4 :bars-per-phrase 4}}}
                      (dissoc initial :history-limit :control))]
     (require! (and (integer? limit) (pos? limit)) :invalid-model "History limit must be positive")
     (require! (identifier? (:show-id model)) :invalid-model "Show ID must be a keyword or nonempty string")
     (doseq [k [:epoch :revision]]
       (require! (and (integer? (get model k)) (<= 0 (get model k)))
                 :invalid-model "Epoch and revision must be nonnegative integers" {:field k}))
     (require! (nonnegative? (:time-ms model)) :invalid-model "Time must be finite and nonnegative")
     (require! (and (params/finite-number? (:master model)) (<= 0 (:master model) 1))
               :invalid-model "Master must be in [0,1]")
     (require! (instance? Boolean (:blackout? model)) :invalid-model "Blackout must be boolean")
     (doseq [k [:registry :instances :pages :variables :transport]]
       (require! (map? (get model k)) :invalid-model "Expected map" {:field k}))
     (require! (not-any? (fn [[id page]]
                          (or (= id pages/recent-page-id) (= (:id page) pages/recent-page-id)))
                        (:pages model))
               :invalid-model "The generated recent page ID cannot be authored")
     (assoc model
            :registry (merge {:effects {} :cues {} :fixtures {} :versions {}} (:registry model))
            :transport (merge {:bpm 120 :playing? true :beat 0.0
                               :meter {:beats-per-bar 4 :bars-per-phrase 4}} (:transport model))
            :control {:next-instance 0
                      :next-order (if (seq (:instances model))
                                    (inc (apply max (map #(get % :order 0) (vals (:instances model))))) 0)
                      :history-limit limit
                      :history {} :history-order []}))))

(defn- effect-definition [model cue]
  (if-let [version (:effect-version cue)]
    (or (get-in model [:registry :versions [:effects (:effect-id cue) version]])
        (let [current (get-in model [:registry :effects (:effect-id cue)])]
          (when (= version (:version current)) current)))
    (get-in model [:registry :effects (:effect-id cue)])))

(defn- latest-version [model kind id]
  (reduce max (get-in model [:registry kind id :version] 0)
          (keep (fn [[[entry-kind entry-id version] _]]
                  (when (and (= kind entry-kind) (= id entry-id)) version))
                (get-in model [:registry :versions]))))

(defn- check-params! [schemas values]
  (let [errors (params/validate-values schemas values)]
    (require! (empty? errors) :invalid-params "Invalid parameters" {:errors errors})))

(defn- validate-definition! [model kind definition]
  (require! (#{:effects :cues :fixtures} kind) :invalid-kind "Unknown registry kind")
  (require! (map? definition) :invalid-definition "Definition must be a map")
  (require! (identifier? (:id definition)) :invalid-definition "Definition needs an ID")
  (require! (and (integer? (:version definition)) (pos? (:version definition)))
            :invalid-definition "Definition version must be a positive integer")
  (when (contains? definition :duration-ms)
    (require! (duration? (:duration-ms definition)) :invalid-duration "Duration must be positive"))
  (when (contains? definition :release-duration-ms)
    (require! (nonnegative? (:release-duration-ms definition)) :invalid-duration "Release duration must be nonnegative"))
  (when (contains? definition :duration) (check-duration! (:duration definition) true))
  (when (contains? definition :release-duration) (check-duration! (:release-duration definition) false))
  (when (contains? definition :system) (system/validate-options (:system definition)))
  (when (contains? definition :categories)
    (require! (and (vector? (:categories definition)) (every? keyword? (:categories definition)))
              :invalid-definition "Categories must be a vector of keyword tags"))
  (case kind
    :effects
    (let [schemas (get definition :params {})]
      (require! (map? schemas) :invalid-definition "Effect params must be a map")
      (doseq [[k schema] schemas]
        (require! (and (keyword? k) (params/valid-schema? schema))
                  :invalid-definition "Invalid parameter schema/default" {:param k})))
    :cues
    (let [effect (effect-definition model definition)]
      (when (contains? definition :selector)
        (require! (targets/selector? (:selector definition)) :invalid-targets "Invalid cue target selector"))
      (require! effect :unknown-effect "Cue refers to an unknown effect or version")
      (require! (params/finite-number? (get definition :priority 0))
                :invalid-definition "Priority must be finite")
      (check-params! (get effect :params {}) (get definition :params {}))
      (check-params! (get effect :params {}) (get definition :saved-params {})))
    :fixtures nil)
  definition)

(defn- publish-definition [model kind definition]
  (validate-definition! model kind definition)
  (let [id (:id definition)
        previous (get-in model [:registry kind id])]
    (require! (or (= definition previous)
                   (> (:version definition) (latest-version model kind id)))
              :stale-definition-version "Publication must advance the definition version")
    (when (and (= :effects kind) (not= (:params previous) (:params definition)))
      (let [errors (params/dependent-cue-errors (get-in model [:registry :cues]) definition)]
        (require! (empty? errors) :incompatible-cue-presets
                  "Effect edit invalidates cue parameters" {:errors errors})))
    {:model (cond-> (-> model
                       (assoc-in [:registry kind id] definition)
                       (assoc-in [:registry :versions [kind id (:version definition)]] definition))
              (not= definition previous) (update-in [:registry :revision] (fnil inc 0))
              (and (= :cues kind) (nil? previous)) (pages/forget-cue id))
     :events [{:type :registry/published :kind kind :id id :version (:version definition)}]
     :result {:id id :version (:version definition)}}))

(defn- instance! [model id]
  (or (get-in model [:instances id])
      (reject! :unknown-instance "No active instance has that ID" {:instance-id id})))

(defn- time! [model command]
  (let [time (:time-ms command)]
    (require! (and (nonnegative? time) (>= time (:time-ms model)))
              :invalid-time "An explicit nondecreasing time-ms is required")
    time))

(defn- launch-instance [model command cue effect]
  (let [time (time! model command)
        launch (get command :launch {})
        _ (require! (map? launch) :invalid-launch "Launch options must be a map")
        targets (:targets launch)
        _ (when (contains? launch :targets)
            (require! (and (vector? targets) (every? identifier? targets)
                           (= (count targets) (count (distinct targets))))
                      :invalid-targets "Launch targets must be distinct fixture IDs"))
        _ (when (or (contains? launch :selector) (contains? cue :selector))
            (require! (contains? launch :targets) :invalid-targets "Resolve the selector to fixture IDs before launch"))
        priority (get launch :priority (get cue :priority 0))
        _ (require! (params/finite-number? priority) :invalid-launch "Launch priority must be finite")
        mode (get launch :mode :persistent)
        _ (require! (#{:persistent :held :timed :one-shot} mode) :invalid-launch "Unknown launch mode")
        duration-option (timing-option [launch cue effect] :duration :duration-ms)
        duration (:legacy duration-option)
        musical-duration (:duration duration-option)
        _ (when (#{:timed :one-shot} mode)
            (if (contains? duration-option :duration) (check-duration! musical-duration true)
                (require! (duration? duration) :invalid-duration "Timed/one-shot cues need a positive duration")))
        _ (require! (map? (get launch :params {})) :invalid-params "Launch params must be a map")
        overrides (merge (get cue :params {}) (get cue :saved-params {}) (get launch :params {}))
        _ (check-params! (get effect :params {}) overrides)
        values (try (params/resolve-values (get effect :params {}) overrides)
                    (catch clojure.lang.ExceptionInfo e
                      (reject! :invalid-params "Invalid parameter defaults" (ex-data e))))
        release-option (or (timing-option [launch cue effect] :release-duration :release-duration-ms)
                           (timing-option [(:envelope effect)] :release :release-ms))
        musical-release (:duration release-option)
        release (if (contains? release-option :duration) 0 (get release-option :legacy 0))
        _ (when (contains? release-option :duration) (check-duration! musical-release false))
        _ (require! (nonnegative? release) :invalid-duration "Release duration must be nonnegative")
        clock (clock model time)
        reload-policy (or (:reload-policy launch) (:reload-policy cue) :pinned)
        _ (require! (#{:pinned :restart :preserve-state} reload-policy) :invalid-launch "Unknown reload policy")
        next-id (loop [candidate (inc (get-in model [:control :next-instance]))]
                  (if (contains? (:instances model) (str (:epoch model) ":" candidate))
                    (recur (inc candidate)) candidate))
        order (get-in model [:control :next-order])
        id (str (:epoch model) ":" next-id)
        instance (cond-> {:id id :cue-id (:id cue) :effect-id (:id effect)
                          :effect-version (:version effect) :definition effect
                          :source (:source command)
                          :params values :started-at-ms time :started-at-beat (:beat clock)
                          :timing-meter (musical-time/normalize-meter (:meter clock)) :state {}
                          :priority priority :order order :phase :running
                          :launch-mode mode :release-duration-ms release
                          :reload-policy reload-policy}
                   (and (#{:timed :one-shot} mode) (not musical-duration)) (assoc :duration-ms duration)
                   (and (#{:timed :one-shot} mode) musical-duration)
                   (assoc :duration musical-duration :duration-timer (musical-time/start musical-duration clock))
                   (contains? launch :targets) (assoc :targets targets)
                   musical-release (assoc :release-duration musical-release)
                   (:gesture-id command) (assoc :gesture-id (:gesture-id command)))
        _ (doseq [source [effect cue launch] :when (contains? source :system)]
            (system/validate-options (:system source)))
        instance (system/initialize instance
                                    (merge {} (:system effect) (:system cue) (:system launch)) clock)]
    {:model (-> model (assoc-in [:instances id] instance)
                (assoc-in [:control :next-instance] next-id)
                (update-in [:control :next-order] inc))
     :events [{:type :instance/launched :instance instance}]
     :result {:instance-id id}}))

(defn- apply-operation [model {:keys [op] :as command}]
  (case op
    :registry/publish (publish-definition model (:kind command) (:definition command))
    :cue/put
    (let [cue (:cue command)
          old (get-in model [:registry :cues (:id cue)])]
      (when (contains? command :expected-version)
        (require! (= (:expected-version command) (:version old))
                  :stale-definition-version "Cue version changed"))
      (require! (map? cue) :invalid-definition "Cue must be a map")
      (publish-definition model :cues (assoc cue :version
                                            (or (:version cue)
                                                (inc (latest-version model :cues (:id cue)))))))
    (:cue/save-params :cue/clear-saved-params)
    (let [cue-id (:cue-id command)
          cue (get-in model [:registry :cues cue-id])
          _ (require! cue :unknown-cue "Cue does not exist")
          _ (when (contains? command :expected-version)
              (require! (= (:expected-version command) (:version cue))
                        :stale-definition-version "Cue version changed"))
          save? (= op :cue/save-params)
          instance (when save? (instance! model (:instance-id command)))
          _ (when save?
              (require! (and (= cue-id (:cue-id instance)) (= (:effect-id cue) (:effect-id instance)))
                        :wrong-cue-instance "Only this cue's active instance can supply saved parameters"))
          next-cue (-> (if save? (assoc cue :saved-params (:params instance)) (dissoc cue :saved-params))
                       (assoc :version (inc (latest-version model :cues cue-id))))
          result (publish-definition model :cues next-cue)]
      (update result :events conj {:type (if save? :cue/params-saved :cue/saved-params-cleared)
                                  :cue-id cue-id :version (:version next-cue)}))
    :cue/delete
    (let [id (:cue-id command)]
      (require! (get-in model [:registry :cues id]) :unknown-cue "Cue does not exist")
      {:model (-> model
                  (update-in [:registry :cues] dissoc id)
                  (update-in [:registry :revision] (fnil inc 0))
                  (pages/forget-cue id)
                  (update :pages (fn [pages]
                                   (into {} (map (fn [[k page]]
                                                   [k (update page :cells
                                                              #(into {} (remove (fn [[_ v]] (= id v))) %))])) pages))))
       :events [{:type :cue/deleted :cue-id id}]})
    (:cue/launch :effect/launch)
    (let [cue (when (= op :cue/launch)
                (or (get-in model [:registry :cues (:cue-id command)])
                    (reject! :unknown-cue "Cue does not exist" {:cue-id (:cue-id command)})))
          effect (if cue (effect-definition model cue) (get-in model [:registry :effects (:effect-id command)]))]
      (require! effect :unknown-effect "Effect is not published")
      (cond-> (launch-instance model command cue effect)
        cue (update :model pages/record-launch (:cue-id command))))
    :instance/end
    (let [id (:instance-id command)
          instance (instance! model id)
          time (time! model command)
          force? (get command :force? false)
          global-clock (clock model time)]
      (require! (instance? Boolean force?) :invalid-value "Force must be boolean")
      {:model (if force? (update model :instances dissoc id)
                  (let [resumed (system/apply-control instance {:op :instance/resume} global-clock)]
                    (assoc-in model [:instances id]
                              (system/release-instance resumed (system/private-clock resumed global-clock)))))
       :events [{:type (if force? :instance/removed :instance/released) :instance-id id :time-ms time}]
       :result {:instance-id id}})
    :instance/retry
    (let [id (:instance-id command) instance (instance! model id)]
      {:model (assoc-in model [:instances id]
                        (cond-> (dissoc instance :fault :reload-fault)
                          (or (:fault instance) (:reload-fault instance))
                          (assoc :retry-fault (or (:fault instance) (:reload-fault instance)))))
       :events [{:type :effect/retry-requested :instance-id id}]
       :result {:instance-id id}})
    :instance/remove
    (do (instance! model (:instance-id command))
        {:model (update model :instances dissoc (:instance-id command))
         :events [{:type :instance/removed :instance-id (:instance-id command)}]
         :result {:instance-id (:instance-id command)}})
    (:instance/pause :instance/resume :instance/opacity-set :instance/gain-set :instance/opacity-toggle :instance/envelope-set)
    (let [id (:instance-id command), instance (instance! model id)
          changed (system/apply-control instance command (clock model (time! model command)))]
      {:model (assoc-in model [:instances id] changed)
       :events [{:type :instance/system-changed :instance-id id :system (:system changed)}]
       :result {:instance-id id}})
    :group/apply
    (let [action (:action command)
          _ (require! (and (map? action)
                           (#{:instance/pause :instance/resume :instance/remove :instance/end
                              :instance/opacity-set :instance/gain-set :instance/opacity-toggle :instance/envelope-set} (:op action))
                           (every? #{:op :value :envelope :force?} (keys action)))
                      :invalid-action "Group actions accept only instance system/lifecycle operations")
          _ (time! model command)
          _ (case (:op action)
              :instance/end (require! (instance? Boolean (:force? action false)) :invalid-value "Force must be boolean")
              :instance/remove nil
              (system/validate-control action))
          members (categories/select-instances model (:selector command))
          results (reduce (fn [{:keys [model events]} instance]
                            (let [result (apply-operation model (merge command action {:instance-id (:id instance)}))]
                              {:model (:model result) :events (into events (:events result))}))
                          {:model model :events []} members)]
      (assoc results :result {:instance-ids (mapv :id members)}))
    :param/set
    (let [id (:instance-id command)
          instance (instance! model id)
          k (:param command)
          value (:value command)]
      (check-params! (get-in instance [:definition :params] {}) {k value})
      {:model (assoc-in model [:instances id :params k] value)
       :events [{:type :param/changed :instance-id id :param k :value value}]})
    :master/set
    (do (require! (and (params/finite-number? (:value command)) (<= 0 (:value command) 1))
                  :invalid-value "Master must be in [0,1]")
        {:model (assoc model :master (:value command)) :events [{:type :master/changed :value (:value command)}]})
    :blackout/set
    (do (require! (instance? Boolean (:value command)) :invalid-value "Blackout must be boolean")
        {:model (assoc model :blackout? (:value command)) :events [{:type :blackout/changed :value (:value command)}]})
    :transport/set
    (let [changes (:transport command)]
      (require! (and (map? changes) (every? #{:bpm :playing? :meter} (keys changes)))
                :invalid-value "Transport accepts bpm, playing? and meter")
      (when (contains? changes :bpm)
        (require! (and (params/finite-number? (:bpm changes)) (<= 1 (:bpm changes) 1000))
                  :invalid-value "BPM must be in [1,1000]"))
      (when (contains? changes :playing?)
        (require! (instance? Boolean (:playing? changes)) :invalid-value "Playing must be boolean"))
      (when (contains? changes :meter) (musical-time/normalize-meter (:meter changes)))
      {:model (update model :transport merge changes) :events [{:type :transport/changed :transport changes}]})
    :page/put
    (let [page (:page command)]
      (require! (and (map? page) (identifier? (:id page)) (map? (get page :cells {})))
                :invalid-page "Page needs an ID and cells map")
      (doseq [[coordinate cue-id] (:cells page)]
        (require! (and (vector? coordinate) (= 2 (count coordinate))
                       (every? #(and (integer? %) (<= 0 %)) coordinate))
                  :invalid-page "Cell coordinates must be two nonnegative integers")
        (require! (get-in model [:registry :cues cue-id]) :unknown-cue "Page references unknown cue"))
      {:model (assoc-in model [:pages (:id page)] (assoc page :cells (get page :cells {})))
       :events [{:type :page/changed :page-id (:id page)}]})
    :page/delete
    (let [id (:page-id command)]
      (require! (and (not= id pages/recent-page-id) (get-in model [:pages id]))
                :unknown-page "Page does not exist")
      {:model (update model :pages dissoc id)
       :events [{:type :page/deleted :page-id id}]})
    :show/restart
    (let [time (time! model command)]
      {:model (-> model (update :epoch inc) (assoc :instances {} :time-ms time)
                  (assoc-in [:control :next-instance] 0)
                  (assoc-in [:control :next-order] 0)
                  (assoc-in [:control :history] {})
                  (assoc-in [:control :history-order] []))
       :events [{:type :show/restarted :epoch (inc (:epoch model))}]})
    (reject! :unknown-operation "Unknown command operation" {:op op})))

(defn- receipt [model command status]
  {:command-id (:command-id command) :show-id (:show-id model)
   :epoch (:epoch model) :revision (:revision model) :status status})

(defn- remember [model command ack]
  (let [id (:command-id command)
        order (conj (get-in model [:control :history-order]) id)
        limit (get-in model [:control :history-limit])
        remove-count (max 0 (- (count order) limit))
        evicted (take remove-count order)]
    (-> model
        (assoc-in [:control :history-order] (vec (drop remove-count order)))
        (update-in [:control :history]
                   #(apply dissoc (assoc % id {:command command :ack ack}) evicted)))))

(defn apply-domain-command
  "Apply a pure [model command] operation inside the shared command envelope.
  Hosts select the operation before calling. It returns :model, :events and
  optional :result, or throws an ExceptionInfo with :control/error.

  Rejected commands return the identical model and a structured ack. Duplicate
  accepted IDs return their original ack and no events; a reused ID with changed
  payload is rejected. Retry history is bounded, so callers must expire sessions
  rather than replay commands after receipts have been evicted. Restart changes
  epoch and drops active instances; old epoch requests cannot alter the new show."
  [model command operation]
  (try
    (require! (map? command) :invalid-command "Command must be a map")
    (require! (identifier? (:command-id command)) :invalid-command "Command needs a stable ID")
    (require! (= (:show-id model) (:show-id command)) :wrong-show "Command targets a different show")
    (require! (= (:epoch model) (:epoch command)) :stale-epoch "Show epoch changed")
    (require! (some? (:source command)) :invalid-command "Command needs a source")
    (if-let [cached (get-in model [:control :history (:command-id command)])]
      (do (require! (= command (:command cached)) :command-id-conflict "Command ID reused with different data")
          {:model model :events [] :ack (:ack cached)})
      (do
        (when (contains? command :expected-revision)
          (require! (= (:revision model) (:expected-revision command))
                    :stale-revision "Show revision changed"))
        (when (contains? command :time-ms) (time! model command))
        (let [{next-model :model events :events result :result} (operation model command)
              updated (cond-> (update next-model :revision inc)
                        (contains? command :time-ms) (assoc :time-ms (:time-ms command)))
              ack (merge (receipt updated command :accepted) result)
              remembered (remember updated command ack)
              remembered (if (contains? model ::events/pending)
                           (events/collect remembered :control
                             {:kind :command :id (or (get-in command [:source :adapter])
                                                     (get-in command [:source :type]) (:source command))}
                             events)
                           remembered)]
          {:model remembered :events (vec events) :ack ack})))
    (catch clojure.lang.ExceptionInfo e
      (if-let [code (:control/error (ex-data e))]
        {:model model :events []
         :ack (assoc (receipt model command :rejected) :code code :message (.getMessage e)
                     :details (:details (ex-data e)))}
        (throw e)))))

(defn apply-command
  "Apply an Afterglow command atomically. Accepted commands increment revision."
  [model command]
  (apply-domain-command model command apply-operation))
