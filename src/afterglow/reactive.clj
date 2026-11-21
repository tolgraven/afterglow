(ns afterglow.reactive
  "Owned JVM reactive boundary, separate from pure effect/render workers.

  Source ratoms implement normal deref/reset!/swap! semantics. publish! freezes
  every source once, propagates value changes through tracked reactions and
  queues semantic actions. No user function runs inside an atom CAS loop."
  (:require [afterglow.reactive.registry :as registry]))

(def validate-registry registry/validate-registry)
(def ^:dynamic ^:private *transaction* nil)
(def ^:dynamic ^:private *dependencies* nil)
(def ^:dynamic ^:private *stack* [])
(defrecord ReactiveSystem [lock state sources])
(defprotocol Handle
  (-system [handle]) (-id [handle]) (-kind [handle]))
(declare read-cell read-reaction change-cell! compare-cell! option! options subscribe queue-action!)

(deftype Cell [system id]
  Handle (-system [_] system) (-id [_] id) (-kind [_] :source)
  clojure.lang.IDeref (deref [this] (read-cell this))
  clojure.lang.IAtom2
  (reset [this value] (second (change-cell! this (constantly value))))
  (resetVals [this value] (change-cell! this (constantly value)))
  (compareAndSet [this old value] (compare-cell! this old value))
  (swap [this f] (second (change-cell! this f)))
  (swap [this f a] (second (change-cell! this #(f % a))))
  (swap [this f a b] (second (change-cell! this #(f % a b))))
  (swap [this f a b args] (second (change-cell! this #(apply f % a b args))))
  (swapVals [this f] (change-cell! this f))
  (swapVals [this f a] (change-cell! this #(f % a)))
  (swapVals [this f a b] (change-cell! this #(f % a b)))
  (swapVals [this f a b args] (change-cell! this #(apply f % a b args)))
  clojure.lang.IRef
  (getValidator [this] (:validator (options this)))
  (setValidator [this f] (option! this :validator f))
  (getWatches [this] (:watches (options this) {}))
  (addWatch [this key f] (option! this [:watch key] f) this)
  (removeWatch [this key] (option! this [:watch key] nil) this)
  Object (toString [_] (str "#<reactive-cell " id ">")))

(deftype Reaction [system id]
  Handle (-system [_] system) (-id [_] id) (-kind [_] :node)
  clojure.lang.IDeref (deref [this] (read-reaction this))
  clojure.lang.IRef
  (getValidator [this] (:validator (options this)))
  (setValidator [this f] (option! this :validator f))
  (getWatches [this] (:watches (options this) {}))
  (addWatch [this key f] (option! this [:watch key] f) this)
  (removeWatch [this key] (option! this [:watch key] nil) this)
  Object (toString [_] (str "#<reaction " id ">")))

(defn- fail! [message data] (throw (ex-info message data)))
(defn- same-transaction? [system] (identical? system (:system *transaction*)))
(defn- ensure-open! [system]
  (when (:closed? @(:state system)) (fail! "Reactive system is closed" {:type ::closed})))
(defn- state-of [system]
  (if (same-transaction? system) @(:working *transaction*) @(:state system)))
(defn- ensure-handle! [handle]
  (let [system (-system handle)
        path (if (= :source (-kind handle)) :cell-handles :handles)]
    (ensure-open! system)
    (when-not (identical? handle (get-in (state-of system) [path (-id handle)]))
      (fail! "Reactive handle was disposed or replaced" {:type ::disposed :id (-id handle)}))))
(defn- outside-evaluation! []
  (when *transaction* (fail! "Change reactive graph structure only between owner batches" {:type ::mutation-during-evaluation})))
(defn- write-state! [system state]
  (if (same-transaction? system) (vreset! (:working *transaction*) state) (reset! (:state system) state)))
(defn- dependency! [system dependency]
  (when *transaction*
    (when-not (same-transaction? system)
      (fail! "A reaction cannot read a different reactive system" {:type ::cross-system}))
    (when *dependencies* (vswap! *dependencies* conj dependency))))
(defn- transact! [system f]
  (locking (:lock system)
    (ensure-open! system)
    (if (same-transaction? system)
      (f)
      (do
        (when *transaction* (fail! "Cannot nest different reactive systems" {:type ::cross-system}))
        (let [working (volatile! @(:state system))
              captured @(:sources system)
              result (binding [*transaction* {:system system :working working :sources captured}
                               *stack* [] *dependencies* nil]
                       (f))]
          (reset! (:state system) @working)
          result)))))

(defn create-system
  "Create an explicit owner. Requiring this namespace starts no workers or IO."
  [db]
  (let [system (->ReactiveSystem (Object.)
                                (atom {:nodes {} :handles {} :cell-handles {} :options {}
                                       :dependents {} :source-snapshot {:db db} :registrations {}
                                       :watchers {} :actions [] :generation 0 :next-order 0})
                                (atom {:db db}))]
    (reset! (:state system) (assoc-in @(:state system) [:cell-handles :db] (Cell. system :db)))
    system))

(defn ratom
  "Create/cache a named source ratom. Values change synchronously; reactions
  observe the frozen source set of their current publish! batch."
  [system id initial]
  (when-not (keyword? id) (fail! "Source IDs must be keywords" {:id id :type ::invalid-id}))
  (locking (:lock system)
    (ensure-open! system)
    (when *transaction* (fail! "Create source cells outside reactive evaluation" {:type ::mutation-during-evaluation}))
    (or (get-in @(:state system) [:cell-handles id])
        (let [cell (Cell. system id)]
          (when-not (contains? @(:sources system) id)
            (reset! (:sources system) (assoc @(:sources system) id initial)))
          (reset! (:state system)
                  (-> @(:state system) (assoc-in [:cell-handles id] cell)
                      (assoc-in [:source-snapshot id] (get @(:sources system) id))))
          cell))))

(defn db-signal [system]
  (or (get-in (state-of system) [:cell-handles :db])
      (ratom system :db (get @(:sources system) :db))))

(defn source
  "Look up an existing named cell, including inside a durable handler. Tracking
  begins when the returned cell is dereferenced. This never creates a cell."
  [system id]
  (locking (:lock system)
    (ensure-open! system)
    (or (get-in (state-of system) [:cell-handles id])
        (fail! "Unknown reactive source" {:type ::unknown-source :id id}))))

(defn read-cell [cell]
  (let [system (-system cell) id (-id cell)]
    (locking (:lock system)
      (ensure-handle! cell)
      (dependency! system [:source id])
      (let [sources (if (same-transaction? system) (:sources *transaction*) @(:sources system))]
        (when-not (contains? sources id) (fail! "Source cell was disposed" {:type ::disposed :id id}))
        (get sources id)))))

(defn options [handle]
  (locking (:lock (-system handle))
    (ensure-handle! handle)
    (get-in (state-of (-system handle)) [:options [(-kind handle) (-id handle)]] {})))
(defn option! [handle option value]
  (let [system (-system handle) key [(-kind handle) (-id handle)]]
    (locking (:lock system)
      (ensure-handle! handle)
      (outside-evaluation!)
      (when (and (= option :validator) value (not (value @handle)))
        (fail! "Validator rejects current reactive value" {:type ::invalid-value :id (-id handle)}))
      (write-state! system
                    (if (vector? option)
                      (update-in (state-of system) [:options key :watches]
                                 (fn [watches] (if value (assoc (or watches {}) (second option) value)
                                                   (dissoc watches (second option)))))
                      (assoc-in (state-of system) [:options key option] value))))))

(defn- check-value! [handle value]
  (when-let [validator (:validator (options handle))]
    (when-not (validator value) (fail! "Validator rejects reactive value" {:type ::invalid-value :id (-id handle)}))))
(defn- notify-watches! [handle old new]
  (doseq [[key f] (sort-by (comp pr-str key) (:watches (options handle)))] (f key handle old new)))

(defn change-cell! [cell f]
  (let [system (-system cell) id (-id cell)]
    (locking (:lock system)
      (ensure-handle! cell)
      (when (:restoring? *transaction*)
        (fail! "Source writes are not allowed while reconstructing a saved graph" {:type ::restore-mutation}))
      (when-not (contains? @(:sources system) id) (fail! "Source cell was disposed" {:type ::disposed :id id}))
      (let [old (get @(:sources system) id) new (f old)]
        (check-value! cell new)
        ;; f runs once under the owner lock, never in swap!/CAS retry code.
        (reset! (:sources system) (assoc @(:sources system) id new))
        (notify-watches! cell old new)
        [old new]))))
(defn compare-cell! [cell old value]
  (locking (:lock (-system cell))
    (ensure-handle! cell)
    (when (:restoring? *transaction*)
      (fail! "Source writes are not allowed while reconstructing a saved graph" {:type ::restore-mutation}))
    (if (identical? old (get @(:sources (-system cell)) (-id cell)))
      (do (change-cell! cell (constantly value)) true) false)))
(defn reset-cell! [cell value] (reset! cell value))
(defn swap-cell! [cell f & args] (apply swap! cell f args))

(defn- mark-dependents [state dependency]
  (reduce (fn [s id] (if (contains? (:nodes s) id) (assoc-in s [:nodes id :dirty?] true) s))
          state (get-in state [:dependents dependency])))
(defn- replace-dependencies [state id old new]
  (let [state (reduce #(update-in %1 [:dependents %2] disj id) state old)]
    (reduce #(update-in %1 [:dependents %2] (fnil conj #{}) id) state new)))

(defn- evaluate-node! [system id]
  (when (some #{id} *stack*) (fail! "Reactive dependency cycle" {:type ::cycle :path (conj *stack* id)}))
  (when (> (count *stack*) 255) (fail! "Reactive dependency depth exceeded" {:type ::depth :path *stack*}))
  (let [node (get-in (state-of system) [:nodes id])]
    (when-not node (fail! "Reaction was disposed" {:type ::disposed :id id}))
    (if (and (:initialized? node) (not (:dirty? node)))
      (:value node)
      (let [dependencies (volatile! #{})
            [value compute] (binding [*stack* (conj *stack* id) *dependencies* dependencies]
                              (if-let [compute (:compute node)]
                                [(compute) compute]
                                (let [initial ((:factory node))]
                                  (if (fn? initial) [(initial) initial] [initial (:factory node)]))))
            handle (get-in (state-of system) [:handles id])]
        (check-value! handle value)
        (let [state (state-of system)
              changed? (or (not (:initialized? node)) (not= (:value node) value))
              updated (-> state
                          (replace-dependencies id (:deps node) @dependencies)
                          (assoc-in [:nodes id] (assoc node :compute compute :value value :deps @dependencies
                                                     :initialized? true :dirty? false)))
              updated (if changed? (mark-dependents updated [:node id]) updated)]
          (write-state! system updated)
          value)))))

(defn read-reaction [reaction]
  (let [system (-system reaction) id (-id reaction)]
    (transact! system #(do (ensure-handle! reaction)
                          (dependency! system [:node id])
                          (evaluate-node! system id)))))

(defn- add-node! [system id factory]
  (let [state (state-of system) handle (Reaction. system id) order (:next-order state)]
    (when (contains? (:nodes state) id) (fail! "Duplicate reaction ID" {:type ::duplicate-id :id id}))
    (write-state! system (-> state (assoc-in [:nodes id] {:factory factory :deps #{} :dirty? true :order order})
                             (assoc-in [:handles id] handle) (update :next-order inc)))
    handle))

(defn reaction [system id f]
  (when-not (and (keyword? id) (fn? f)) (fail! "Reaction needs a keyword ID and function" {:type ::invalid-reaction}))
  (transact! system #(add-node! system [:reaction id] f)))

(defn queue-action!
  "Queue semantic data for the owner to apply next cycle. No command executes
  here. Actions emitted by a failed reactive batch are not published."
  [system action]
  (when-not (registry/semantic-action? action)
    (fail! "Reactive actions need an :op and portable payload; the owner supplies epoch, time, source and command ID"
           {:type ::invalid-action}))
  (locking (:lock system)
    (ensure-open! system)
    (write-state! system (update (state-of system) :actions conj action)))
  action)

(defn drain-actions! [system]
  (locking (:lock system)
    (ensure-open! system)
    (when *transaction* (fail! "Only the owner can drain reactive actions between batches" {:type ::drain-during-evaluation}))
    (let [actions (:actions @(:state system))]
      (reset! (:state system) (assoc @(:state system) :actions [])) actions)))

(defn- context [system]
  {:db (db-signal system) :source #(source system %) :subscribe #(subscribe system %) :queue-action! #(queue-action! system %)})

(defn- register! [system kind id handler descriptor]
  (when-not (and (keyword? id) (fn? handler)) (fail! "Registration needs a keyword ID and function" {:type ::invalid-registration}))
  (when descriptor
    (registry/validate-definition descriptor)
    (when-not (= [kind id] [(:kind descriptor) (:id descriptor)])
      (fail! "Registration descriptor does not match its handler" {:type ::invalid-registration :id id})))
  (locking (:lock system)
    (ensure-open! system)
    (when *transaction* (fail! "Register handlers outside reactive evaluation" {:type ::mutation-during-evaluation}))
    (reset! (:state system)
            (-> @(:state system)
                (assoc-in [:registrations [kind id]] {:handler handler :descriptor descriptor})
                (update :nodes (fn [nodes]
                                 (into {} (map (fn [[node-id node]]
                                                [node-id (if (and (= :sub kind) (= :subscription (first node-id))
                                                                                 (= id (first (second node-id))))
                                                           (assoc node :compute nil :dirty? true) node)]) nodes)))))))
  id)

(defn reg-sub!
  ([system id handler] (reg-sub! system id handler nil))
  ([system id handler descriptor] (register! system :sub id handler descriptor)))
(defn reg-fx!
  ([system id handler] (reg-fx! system id handler nil))
  ([system id handler descriptor] (register! system :fx id handler descriptor)))

(defn subscribe
  "Return a cached signal for a portable query vector. A normal handler returns
  its value. A form-2 handler returns a zero-arg computation; its outer function
  runs once per cached query/registration, with inner derefs tracked thereafter."
  [system query]
  (when-not (and (vector? query) (keyword? (first query)) (registry/portable? query))
    (fail! "Subscription query must be a portable vector beginning with a keyword" {:type ::invalid-query :query query}))
  ;; Ensure the db handle exists before entering the evaluation transaction.
  (when-not (get-in (state-of system) [:cell-handles :db]) (db-signal system))
  (transact! system
             (fn []
               (when-not (get-in (state-of system) [:registrations [:sub (first query)]])
                 (fail! "Unknown subscription" {:type ::unknown-subscription :query query}))
               (let [id [:subscription query]
                     handle (or (get-in (state-of system) [:handles id])
                                (add-node! system id
                                           (fn []
                                             (let [handler (get-in (state-of system) [:registrations [:sub (first query)] :handler])]
                                               (handler (context system) query)))))]
                 (evaluate-node! system id)
                 handle))))

(defn watch!
  "Invoke a registered effect handler when the selected subscription changes.
  Handler receives [context new-value old-value] and may return one action map,
  a vector of action maps, or nil. Initial values fire on the next publish!."
  [system id query effect-id]
  (when-not (and (keyword? id) (keyword? effect-id)) (fail! "Watcher IDs must be keywords" {:type ::invalid-watcher}))
  (when-not (:restoring? *transaction*) (outside-evaluation!))
  (transact! system
             (fn []
               (when-not (get-in (state-of system) [:registrations [:fx effect-id]])
                 (fail! "Unknown effect handler" {:type ::unknown-effect :effect-id effect-id}))
               (subscribe system query)
               (let [state (state-of system)]
                 (when (contains? (:watchers state) id) (fail! "Duplicate watcher ID" {:type ::duplicate-id :id id}))
                 (write-state! system (assoc-in state [:watchers id] {:id id :query query :effect-id effect-id
                                                                     :initialized? false :value nil :order (:next-order state)}))
                 (write-state! system (update (state-of system) :next-order inc))
                 id))))

(defn unwatch! [system id]
  (locking (:lock system) (ensure-open! system)
           (outside-evaluation!)
           (write-state! system (update (state-of system) :watchers dissoc id))))

(defn- run-watchers! [system]
  (doseq [{:keys [id query effect-id initialized? value]} (sort-by :order (vals (:watchers (state-of system))))]
    (let [new (evaluate-node! system [:subscription query])]
      (when (or (not initialized?) (not= value new))
        (let [handler (get-in (state-of system) [:registrations [:fx effect-id] :handler])
              actions (handler (context system) new (when initialized? value))]
          (cond
            (nil? actions) nil
            (map? actions) (queue-action! system actions)
            (vector? actions) (doseq [action actions] (queue-action! system action))
            :else (fail! "Reactive effect handler must return action data or nil" {:type ::invalid-action :effect-id effect-id}))
          (write-state! system (update-in (state-of system) [:watchers id] assoc :initialized? true :value new)))))))

(defn publish!
  "Freeze source values and commit a complete derived/action batch. With db,
  update the canonical db source first. Changes enqueued by handlers are for the
  owner's next cycle; source writes during evaluation are seen next publish!."
  ([system]
   (locking (:lock system)
    (let [before @(:state system)
         result (transact! system
                           (fn []
                             (let [captured (:sources *transaction*)
                                   state (state-of system)
                                   changed (for [[id value] captured
                                                 :when (not= (get (:source-snapshot state) id ::absent) value)] id)]
                               (write-state! system
                                             (-> (reduce #(mark-dependents %1 [:source %2]) state changed)
                                                 (assoc :source-snapshot captured) (update :generation inc)))
                               (loop []
                                 (when-let [[id _] (first (sort-by (comp :order val) (filter (comp :dirty? val) (:nodes (state-of system)))))]
                                   (evaluate-node! system id) (recur)))
                               (run-watchers! system)
                               {:generation (:generation (state-of system)) :changed-sources (vec (sort-by str changed))
                                :values (into {} (map (fn [[id node]] [id (:value node)]) (:nodes (state-of system))))})))]
     ;; Watch callbacks observe an already committed batch, never a partial DAG.
     (doseq [[id node] (:nodes @(:state system))
             :let [old (get-in before [:nodes id :value])]
             :when (not= old (:value node))]
       (notify-watches! (get-in @(:state system) [:handles id]) old (:value node)))
     result)))
  ([system db] (locking (:lock system) (reset! (db-signal system) db) (publish! system))))

(defn dispose!
  "Dispose a shared cached reaction. Existing holders become invalid; a future
  subscribe creates a new handle. Disposing a source invalidates its readers."
  [handle]
  (let [system (-system handle) id (-id handle) kind (-kind handle)]
    (locking (:lock system)
      (ensure-handle! handle)
      (outside-evaluation!)
      (let [state (state-of system) dependency [kind id]
            state (mark-dependents state dependency)
            state (if (= kind :node)
                    (-> state (replace-dependencies id (get-in state [:nodes id :deps]) #{})
                        (update :nodes dissoc id) (update :handles dissoc id))
                    (do
                      (when (= id :db) (fail! "The canonical db source cannot be disposed" {:type ::canonical-source}))
                      (reset! (:sources system) (dissoc @(:sources system) id))
                      (-> state (update :cell-handles dissoc id) (update :source-snapshot dissoc id))))]
        (write-state! system (update state :options dissoc dependency))))
    nil))

(defn export-registry
  "Save portable registrations, custom source values, queued actions and watcher
  comparisons. Opaque functions must be registered through source/var descriptors
  before saving; the canonical db is persisted by the owning show document."
  [system]
  (locking (:lock system)
    (ensure-open! system)
    (outside-evaluation!)
    (let [state @(:state system)
          _ (when (some #(= :reaction (first %)) (keys (:nodes state)))
              (fail! "Cannot persist an anonymous reaction; register its source with reg-sub or a named var first"
                     {:type ::unpersistable-reaction}))
          definitions (map (fn [[[kind id] registration]]
                             (or (:descriptor registration)
                                 (fail! "Cannot persist an opaque reactive handler; use reg-sub/reg-fx macros or a var descriptor"
                                        {:type ::unpersistable-handler :kind kind :id id})))
                           (sort-by (comp pr-str key) (:registrations state)))
          result {:registrations (vec definitions)
                  :state {:cells (dissoc @(:sources system) :db) :pending-actions (:actions state)
                          :watchers (mapv #(dissoc % :order) (sort-by :order (vals (:watchers state))))}}]
      (registry/validate-registry result))))

(defn restore!
  "Replace registrations/caches from validated data, retaining the owner's db.
  Source code compilation requires {:trusted-source? true}. Validation and
  compilation finish before graph replacement. Restore watcher last-values so
  loading at the same beat does not trigger the same action again."
  ([system data] (restore! system data {}))
  ([system data options]
   (registry/validate-registry data)
   (let [resolved (mapv (fn [definition] [definition (registry/resolve-handler definition options)]) (:registrations data))]
     (locking (:lock system)
       (ensure-open! system)
       (when *transaction* (fail! "Restore only between owner batches" {:type ::mutation-during-evaluation}))
       (let [db (get @(:sources system) :db)
             sources (assoc (get-in data [:state :cells] {}) :db db)
             initial (-> @(:state (create-system db))
                         (assoc :source-snapshot sources
                                :cell-handles (into {} (map (fn [id] [id (Cell. system id)]) (keys sources)))
                                :registrations (into {} (map (fn [[{:keys [id kind] :as descriptor} handler]]
                                                              [[kind id] {:handler handler :descriptor descriptor}]) resolved))))
             working (volatile! initial)]
         ;; One staged graph, with handles pointing at the real owner. Factories
         ;; are constructed once, and no graph is visible until all succeed.
         (binding [*transaction* {:system system :working working :sources sources :restoring? true}
                   *stack* [] *dependencies* nil]
           (doseq [{:keys [id query effect-id] :as watcher} (get-in data [:state :watchers])]
             (watch! system id query effect-id)
             (write-state! system (update-in (state-of system) [:watchers id] merge watcher)))
           (write-state! system (assoc (state-of system) :actions (get-in data [:state :pending-actions] []))))
         (reset! (:sources system) sources)
         (reset! (:state system) @working))))
   system))

(defn close! [system]
  (locking (:lock system)
    (outside-evaluation!)
    (reset! (:state system) {:closed? true}) (reset! (:sources system) {}))
  nil)

(defmacro reg-sub
  "Register trusted REPL source with explicit captured locals, e.g.
  (reg-sub system ::scaled {gain gain} (fn [{:keys [db]} _] (* gain (:x @db))))."
  [system id bindings handler-form]
  (when-not (and (map? bindings) (every? symbol? (keys bindings)))
    (throw (IllegalArgumentException. "Captured bindings must be a map of local symbols to expressions")))
  (registry/read-function (pr-str handler-form))
  (let [locals (vec (mapcat identity bindings))
        data (into {} (map (fn [[name _]] [(str name) name]) bindings))]
    `(let [~@locals
           descriptor# {:id ~id :kind :sub :implementation {:type :source :namespace ~(str (ns-name *ns*))
                                                            :form ~(pr-str handler-form) :bindings ~data}}]
       (reg-sub! ~system ~id ~handler-form descriptor#))))

(defmacro reg-fx [system id bindings handler-form]
  (when-not (and (map? bindings) (every? symbol? (keys bindings)))
    (throw (IllegalArgumentException. "Captured bindings must be a map of local symbols to expressions")))
  (registry/read-function (pr-str handler-form))
  (let [locals (vec (mapcat identity bindings))
        data (into {} (map (fn [[name _]] [(str name) name]) bindings))]
    `(let [~@locals
           descriptor# {:id ~id :kind :fx :implementation {:type :source :namespace ~(str (ns-name *ns*))
                                                           :form ~(pr-str handler-form) :bindings ~data}}]
       (reg-fx! ~system ~id ~handler-form descriptor#))))
