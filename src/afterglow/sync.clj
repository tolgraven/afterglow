(ns afterglow.sync
  "Per-show synchronization lifecycle. Create inert resources and explicitly start or stop the session."
  (:require [afterglow.control.clock :as clock]
            [afterglow.sync.config :as config :refer [validate-config validate-state source-id]]
            [afterglow.sync.midi :as midi]
            [afterglow.sync.beat-link :as dj]
            [afterglow.sync.ableton-link :as link]
            [afterglow.sync.session :as session :refer [apply-clock! emit! queue! clock-at fail! now-ms error-data]])
  (:import [java.util UUID]
           [java.util.concurrent ArrayBlockingQueue ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy
            ThreadFactory TimeUnit]))

(defn- prepare-state [state adapters phase]
  (reduce (fn [s adapter] (if-let [prepare (:prepare-state adapter)] (prepare s phase) s))
          state (vals adapters)))

(defn- lifecycle! [manager run phase]
  (doseq [adapter (vals (:adapters manager))]
    (when-let [on-lifecycle! (:lifecycle! adapter)]
      (on-lifecycle! manager run phase))))

(defn create-manager
  "Construct an inert per-show clock. :adapters is a map keyed by additional
  source names. Each adapter supplies :defaults and :transport (called with
  settings, now-ms and run-id). Optional handlers subscribe through :events.
  MIDI, Beat Link and Ableton Link factories take settings and now-ms."
  ([] (create-manager {}))
  ([options]
   (let [options (merge {:now-ms now-ms :midi-factory midi/transport :beat-link-factory dj/transport
                         :link-factory link/transport :queue-capacity 256 :adapters {}} options)
         adapters (:adapters options)]
     (when-not (and (map? adapters)
                    (every? (fn [[k a]] (and (keyword? k) (not (contains? config/defaults k))
                                              (map? (:defaults a)) (ifn? (:transport a)))) adapters)
                    (every? ifn? ((juxt :now-ms :midi-factory :beat-link-factory :link-factory) options))
                    (integer? (:queue-capacity options)) (<= 8 (:queue-capacity options) 4096))
       (fail! :invalid-options "Invalid synchronization options or adapter"))
     (let [config (validate-config adapters (get options :config {}))
           state {:closed? false :active nil :config config :peers {} :status :stopped :metrics {}
                  :clock (clock/new-state (assoc (:clock config) :selected-source (:selected-source config)))}]
       {:lock (Object.) :options options :adapters adapters :state (atom (prepare-state state adapters :configure))}))))

(defn export-state [manager] {:version 1 :config (:config @(:state manager)) :wanted? false})

(defn active-run-id [manager] (get-in @(:state manager) [:active :id]))

(defn invalidate-inputs!
  "Invalidate queued input/IO tokens for one captured run immediately. Pure
  ownership mutation only: no locks, callbacks, transport work or waits. Host
  publication uses this before rebind! installs the next callback boundary."
  [manager expected-run-id]
  (when-let [run (:active @(:state manager))]
    (when (= expected-run-id (:id run))
      (swap! (:binding-generation run) inc))))

(defn status [manager]
  (let [{:keys [closed? config status peers metrics last-error active] :as state} @(:state manager)]
    (reduce (fn [result adapter]
              (if-let [project (:status adapter)] (merge result (project state)) result))
            {:closed? closed? :state status :running? (= :running status) :active? (boolean active)
             :config config :peers (vec (sort-by (juxt :device-number :address) (vals peers)))
             :metrics metrics :last-error last-error}
            (vals (:adapters manager)))))

(defn configure! [manager config]
  (let [config (validate-config (:adapters manager) config)]
    (locking (:lock manager)
      (when (:closed? @(:state manager)) (fail! :closed "Synchronization manager is closed"))
      (when (:active @(:state manager)) (fail! :busy "Stop synchronization before changing resource pairings"))
      (swap! (:state manager)
             #(prepare-state (assoc % :config config :peers {} :status :stopped :last-error nil
                                     :clock (clock/new-state (assoc (:clock config) :selected-source (:selected-source config))))
                             (:adapters manager) :configure))))
  (status manager))

(defn restore! [manager data] (configure! manager (:config (validate-state (:adapters manager) data))))

(defn select-source! [manager id]
  (let [id (source-id id)]
    (locking (:lock manager)
      (let [config (validate-config (:adapters manager) (assoc (:config @(:state manager)) :selected-source id))]
        (swap! (:state manager) #(-> % (assoc :config config) (update :clock clock/select-source id))))))
  (clock-at manager ((get-in manager [:options :now-ms]))))

(defn- rebind-input! [manager run event]
  (locking (:lock manager)
    (when (and (identical? run (:active @(:state manager))) (not @(:cancelled? run)))
      (reset! (:callbacks run) (:callbacks event))
      (swap! (:state manager) prepare-state (:adapters manager) :rebind)
      (lifecycle! manager run :rebind))))

(defn- notify-adapters! [manager run event at]
  (let [subscribers (filter #(contains? (:events %) (:type event)) (vals (:adapters manager)))]
    (doseq [adapter subscribers] ((:receive! adapter) manager run event at))
    (boolean (seq subscribers))))

(defn- process! [manager run event]
  (let [at ((get-in manager [:options :now-ms]))]
    (case (:type event)
      ::rebind (rebind-input! manager run event)
      :barrier (deliver (:promise event) true)
      :midi/message (midi/receive! manager run event at
                                   (fn [manager run message]
                                     (notify-adapters! manager run {:type :midi/control :event message} (:time-ms message))))
      (:peer/found :peer/lost :beat-link/beat :beat-link/status) (dj/receive! manager run event at)
      (:link/lost :link/status) (link/receive! manager run event)
      (when-not (notify-adapters! manager run event at)
        (fail! :invalid-event "Unknown synchronization event")))))

(defn- close-resources! [run]
  (doseq [[_ {:keys [transport handle closed?]}] (reverse (seq @(:resources run)))]
    (when (compare-and-set! closed? false true) (try ((:close! transport) handle) (catch Exception _)))))

(defn- validate-callbacks! [callbacks]
  (when-not (and (ifn? (:events! callbacks))
                 (every? #(or (nil? %) (ifn? %)) ((juxt :commands! :envelope! :resolve-instance!) callbacks)))
    (fail! :invalid-callbacks "Synchronization needs event delivery and optional callable control callbacks")))

(defn rebind!
  "Queue a new host callback boundary without reopening any transport. Old
  queued input and pending IO work are invalidated immediately; the event owner
  restores adapter callback boundaries before admitting subsequent input.
  No joins, transport calls, callbacks or waits run in this function."
  [manager callbacks]
  (validate-callbacks! callbacks)
  (locking (:lock manager)
    (when (:closed? @(:state manager)) (fail! :closed "Synchronization manager is closed"))
    (if-let [run (:active @(:state manager))]
      (locking (:binding-lock run)
        (if @(:cancelled? run) {:rebound? false :reason :stopping}
          (let [generation (swap! (:binding-generation run) inc)]
            (reset! (:overflow-sources run) #{})
            (.clear ^ArrayBlockingQueue (:queue run))
            (.offer ^ArrayBlockingQueue (:queue run) {:type ::rebind :callbacks callbacks ::session/generation generation})
            {:rebound? true :pending? true :run-id (:id run)})))
      {:rebound? false :reason :inactive})))

(defn- new-run [manager callbacks]
  {:id (str (UUID/randomUUID)) :cancelled? (atom false) :resources (atom {})
   :queue (ArrayBlockingQueue. (int (get-in manager [:options :queue-capacity])))
   :overflow-sources (atom #{}) :event-sequence (atom 0)
   :callbacks (atom callbacks) :binding-lock (Object.) :binding-generation (atom 0)
   :thread (atom nil) :result (promise)
   :io (ThreadPoolExecutor. 1 1 30 TimeUnit/SECONDS (ArrayBlockingQueue. 32)
                            (reify ThreadFactory
                              (newThread [_ task] (doto (Thread. task "afterglow-sync-io") (.setDaemon true))))
                            (ThreadPoolExecutor$AbortPolicy.))})

(defn- begin-run! [manager callbacks]
  (locking (:lock manager)
    (let [{:keys [closed? active]} @(:state manager)]
      (when closed? (fail! :closed "Synchronization manager is closed"))
      (when active (fail! :busy "Synchronization resources are already active"))
      (let [run (reduce (fn [r adapter] (if-let [initialize (:run-state adapter)] (merge r (initialize)) r))
                        (new-run manager callbacks) (vals (:adapters manager)))]
        (swap! (:state manager)
               #(prepare-state (assoc % :active run :status :starting :metrics {} :last-error nil) (:adapters manager) :start))
        run))))

(defn- open-resources! [manager run config]
  (let [{:keys [adapters options]} manager
        now! (:now-ms options)]
    (doseq [kind (concat [:beat-link :link :midi] (keys adapters))
            :when (and (get-in config [kind :enabled?]) (not @(:cancelled? run)))]
      (let [settings (get config kind)
            transport (if-let [adapter (get adapters kind)]
                        ((:transport adapter) settings now! (:id run))
                        ((get options (keyword (str (name kind) "-factory"))) settings now!))
            handle ((:open! transport) #(queue! manager run %))]
        (swap! (:resources run) assoc kind {:transport transport :handle handle :closed? (atom false)})))))

(defn- drain-overflow! [manager run now]
  (let [[lost _] (swap-vals! (:overflow-sources run) (constantly #{}))]
    (doseq [source lost]
      (apply-clock! manager run {:type :source/lost :source-id source :time-ms now})
      (emit! manager run {:type :sync/input-overflow :source-id source :requires-resync? true}))))

(defn- dispatch-next! [manager run periodic?]
  (let [queue ^ArrayBlockingQueue (:queue run)]
    (when-let [event (if periodic? (.poll queue 20 TimeUnit/MILLISECONDS) (.take queue))]
      (when (= (::session/generation event) @(:binding-generation run))
        (try
          (binding [session/*input-generation* (::session/generation event)] (process! manager run event))
          (catch Exception error
            (let [details (error-data error)]
              (swap! (:state manager) assoc :last-error details)
              (emit! manager run {:type :sync/error :error details}))))))))

(defn- pump! [manager run]
  (swap! (:state manager) assoc :status :running)
  (lifecycle! manager run :opened)
  (let [connected (select-keys (:adapters manager) (keys @(:resources run)))
        ticks (keep :tick! (vals connected))]
    (while (not @(:cancelled? run))
      (let [now ((get-in manager [:options :now-ms]))]
        (doseq [tick! ticks] (tick! manager run now))
        (drain-overflow! manager run now)
        (dispatch-next! manager run (seq ticks))))))

(defn- finish-run! [manager run outcome]
  (try
    (lifecycle! manager run :stopping)
    (catch Exception error (emit! manager run {:type :sync/error :error (error-data error)})))
  (reset! (:cancelled? run) true)
  (close-resources! run)
  (let [^ThreadPoolExecutor io (:io run)]
    (.shutdownNow io)
    ;; stop! may interrupt acquisition or event delivery. A late interrupt is
    ;; not evidence that an IO task exited. Retain the run until it actually has.
    (loop []
      (when-not (try (.awaitTermination io 1 TimeUnit/SECONDS) (catch InterruptedException _ false))
        (recur)))
    (locking (:lock manager)
      (when (identical? run (:active @(:state manager)))
        (swap! (:state manager) assoc :active nil :status (:status outcome) :last-error (:error outcome))))
    (deliver (:result run) (assoc outcome :terminated? true))))

(defn- run-session! [manager run]
  (let [config (:config @(:state manager))
        outcome (try
                  (open-resources! manager run config)
                  (when-not @(:cancelled? run) (pump! manager run))
                  {:status :stopped}
                  (catch Throwable error
                    (if @(:cancelled? run) {:status :stopped} {:status :error :error (error-data error)})))]
    (finish-run! manager run outcome)))

(defn start!
  "Open configured sources asynchronously. Callbacks receive bounded event and command deliveries."
  [manager callbacks]
  (validate-callbacks! callbacks)
  (let [run (begin-run! manager callbacks)
        worker (doto (Thread. #(run-session! manager run) "afterglow-sync-owner") (.setDaemon true))]
    (reset! (:thread run) worker)
    (.start worker)
    {:run-id (:id run) :result (:result run)}))

(defn- cancel-run! [manager expected-run-id]
  (locking (:lock manager)
    (let [{:keys [active clock]} @(:state manager)]
      (when (and active (or (= ::any expected-run-id) (= expected-run-id (:id active))))
        (when (compare-and-set! (:cancelled? active) false true)
          (let [at ((get-in manager [:options :now-ms]))
                freeze (fn [state [id source]]
                         (if (= id :manual)
                           state
                           (:state (clock/apply-event state {:type :source/lost :source-id id
                                                             :time-ms (max at (:last-event-ms source))}))))]
            (swap! (:state manager) assoc :clock (reduce freeze clock (:sources clock)) :status :stopping))
          (.shutdownNow ^ThreadPoolExecutor (:io active))
          (when-let [thread @(:thread active)] (.interrupt ^Thread thread)))
        active))))

(defn stop!
  "Cancel the captured run and wait up to timeout-ms. The owner closes its
  acquired resources, and admits a new run only after outstanding IO has exited."
  ([manager] (stop! manager 1500))
  ([manager timeout-ms] (stop! manager timeout-ms ::any))
  ([manager timeout-ms expected-run-id]
   (when-not (and (integer? timeout-ms) (<= 0 timeout-ms 10000))
     (fail! :invalid-timeout "Stop timeout must be 0..10000 ms"))
   (if-let [run (cancel-run! manager expected-run-id)]
     (let [result (try (deref (:result run) timeout-ms nil)
                       (catch InterruptedException _ (.interrupt (Thread/currentThread)) nil))]
       {:stopped? (boolean result) :run-id (:id run)})
     {:stopped? true})))

(defn close! [manager]
  (locking (:lock manager) (swap! (:state manager) assoc :closed? true))
  (assoc (stop! manager) :closed? true))
