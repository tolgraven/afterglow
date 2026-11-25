(ns afterglow.control.devices.session
  "Explicit device I/O shell. Each session serializes its own resource lifecycle;
  show dispatch remains the host coordinator's responsibility. No work starts at
  namespace load. Profiles are pure transitions; transports are injected maps.")

(declare receive! refresh! close! suspend! resume!)

(defn create
  "Create an inert session. Required options: :session-id, :profile, :model!
  (snapshot fn), :dispatch! (command -> result/ack synchronously), :now-ms!.
  Grid cue launch/release and opted-in operator gestures may return queue
  receipts. Gesture commands carry the captured :show-id and :epoch. A pending
  gesture carries its final :completion promise. Profiles
  reconcile receipts before input and feedback. A reconciliation that observes
  a newer owner commit can request a fresh snapshot with :refresh-model? true.
  Optional :midi transport {:open! (fn [receive!] handle), :send! (fn [handle
  messages]), :close! (fn [handle])}; :display uses :open! [] and :render! [handle
  view]. Optional :schedule! takes a refresh callback and returns cancellation.
  A :feedback-source may supply :open! [], :project! [handle local model] and
  :close! [handle]. Only feedback sees its projection; input always receives
  the committed model. Its handle belongs to the active session.
  Hosts should durably queue operator gesture ends, including teardown ends.
  A host without durable admission can retain the session and call refresh!
  until :pending-gesture-ends is empty, even after the transports close.
  Call open! explicitly; without schedule! the host owns the refresh cadence."
  [{:keys [session-id profile model! dispatch! now-ms!] :as options}]
  (when-not (and (or (keyword? session-id) (and (string? session-id) (seq session-id)))
                 (map? profile) (every? ifn? [model! dispatch! now-ms!]))
    (throw (ex-info "Session needs ID, profile, model!, dispatch! and now-ms!" {})))
  {:options options :lock (Object.) :resources (atom {}) :gesture-ends (atom {})
   :command-prefix (if (:grid-launches? profile) (str (java.util.UUID/randomUUID)) session-id)
   :state (atom {:status :closed :generation 0 :counter 0
                 :local (:initial-state profile {}) :errors []})})

(defn snapshot [session]
  (let [pending (seq @(:gesture-ends session))]
    (cond-> @(:state session)
      pending (assoc :pending-gesture-ends (mapv key (sort-by (comp pr-str key) pending))))))

(defn- update-state! [session f & args]
  ;; Callers hold the session lock. No user functions run in a CAS retry loop.
  (reset! (:state session) (apply f @(:state session) args)))

(defn- record-error! [session error]
  (update-state! session update :errors #(vec (take-last 32 (conj % (.getMessage ^Throwable error))))))

(defn- envelope!
  ([session] (envelope! session ((get-in session [:options :model!]))))
  ([session model]
   (let [{:keys [session-id profile now-ms!]} (:options session)
         state (update-state! session update :counter inc)
         now (now-ms!)]
     (when-not (and (number? now) (Double/isFinite (double now)) (<= 0 now))
       (throw (ex-info "Device logical clock must return finite nonnegative milliseconds" {})))
     {:command-id (str (:command-prefix session) ":" (:generation state) ":" (:counter state))
      :show-id (:show-id model) :epoch (:epoch model)
      :source {:adapter (:id profile) :session-id session-id}
      :time-ms (max (:time-ms model 0) now)})))

(defn- show-identity [model]
  [(:show-id model) (:epoch model)])

(defn- adopt-epoch! [session model]
  (let [epoch (:epoch model) state @(:state session)]
    (when-not (= (show-identity model) (show-identity state))
      (update-state! session assoc :show-id (:show-id model) :epoch epoch
                     :local (if-let [reset-model (:reset-model (:profile (:options session)))]
                              (reset-model (:local state))
                              (:initial-state (:profile (:options session)) {}))))))

(defn- grid-launch? [template]
  (and (= :cue/launch (:op template)) (contains? template :grid)))

(defn- dispatch-command! [session template]
  (let [{:keys [dispatch! profile]} (:options session)
        ;; Admission time and show identity are assigned here, including delayed releases.
        envelope (envelope! session)
        scheduled-launch? (grid-launch? template)
        timed-cue? (or scheduled-launch? (= :cue/cancel-launch (:op template)))
        gesture? (and (:operator-gestures? profile)
                      (#{:gesture/begin :gesture/sample :gesture/end} (:op template)))
        stale? (or (and gesture? (not= (show-identity template) (show-identity envelope)))
                   (and timed-cue? (some #(and (contains? template %)
                                               (not= (get template %) (get envelope %)))
                                         [:show-id :epoch])))
        command (cond-> (merge template envelope)
                  (and scheduled-launch? (:command-id template)) (assoc :command-id (:command-id template)))
        response (cond
                   stale? {:status :rejected :reason :stale-epoch}
                   (and gesture? (= :gesture/begin (:op command))
                        (contains? @(:gesture-ends session) (:control-id command)))
                   {:status :rejected :reason :dispatch-busy}
                   (and gesture? (= :gesture/end (:op command)))
                   ;; Preserve feedback and continue releasing other controls.
                   (try (dispatch! command)
                        (catch Exception error
                          (record-error! session error)
                          {:status :rejected :reason :dispatch-error}))
                   :else (dispatch! command))
        ack (or (:ack response) response)
        pending-gesture? (and gesture? (= :pending (:status ack))
                              (instance? clojure.lang.IPending (:completion ack)))]
    (when-not (or (#{:accepted :rejected} (:status ack))
                  (and timed-cue? (#{:pending :fired :cancelled :missed} (:status ack)))
                  pending-gesture?)
      (throw (ex-info "dispatch! must return a synchronous command acknowledgement" {})))
    (update-state! session assoc :last-ack (cond-> ack pending-gesture? (dissoc :completion)))
    [command ack]))

(defn- dispatch-commands! [session commands]
  (let [acknowledge (get-in session [:options :profile :ack])]
    (loop [remaining (seq commands) count 0]
      (when-let [template (first remaining)]
        ;; Push 2 can release 64 held pads and close eight encoder edits at once.
        (when (>= count 72)
          (throw (ex-info "Device transition emitted too many commands" {})))
        (let [[command ack] (dispatch-command! session template)
              result (when acknowledge (acknowledge (:local @(:state session)) command ack))]
          (when result (update-state! session assoc :local (:state result)))
          (recur (concat (next remaining) (:commands result)) (inc count)))))))

(def ^:private gesture-end-retry-ms 100)
(def ^:private gesture-end-limit 8)

(defn- settle-gesture-end! [{:keys [gesture-ends]} command time-ms {:keys [status code reason completion]}]
  (let [control-id (:control-id command)]
    (cond
      (= :pending status) (swap! gesture-ends assoc control-id {:command command :completion completion})
      (#{:dispatch-busy :dispatch-error :queue-full} (or code reason))
      (swap! gesture-ends assoc control-id {:command command :retry-at (+ time-ms gesture-end-retry-ms)})
      ;; :gesture-end-queued means the host already owns the exact same end.
      :else (swap! gesture-ends dissoc control-id))))

(defn- retry-gesture-ends! [{:keys [gesture-ends] :as session}]
  (when (seq @gesture-ends)
    (let [envelope (envelope! session) time-ms (:time-ms envelope)]
      (doseq [[control-id {:keys [command completion retry-at]}] (sort-by (comp pr-str key) @gesture-ends)]
        (cond
          (not= (show-identity command) (show-identity envelope))
          (swap! gesture-ends dissoc control-id)

          completion
          (when (realized? completion)
            (let [ack @completion]
              (update-state! session assoc :last-ack (dissoc ack :completion))
              (settle-gesture-end! session command time-ms ack)))

          (or (nil? retry-at) (>= time-ms retry-at))
          (let [[command ack] (dispatch-command! session command)]
            (settle-gesture-end! session command (:time-ms command) ack)))))))

(defn- send-midi! [session messages]
  (when (seq messages)
    (when-let [handle (:midi @(:resources session))]
      (try ((get-in session [:options :midi :send!]) handle (vec messages))
           (catch Exception error
             (throw (ex-info "Device MIDI/input transport failed" {:device/transport-failed :midi} error)))))))

(defn- render-display! [session view]
  (when (some? view)
    (when-let [handle (:display @(:resources session))]
      (try ((get-in session [:options :display :render!]) handle view)
           (catch Exception error
             (throw (ex-info "Device display transport failed" {:device/transport-failed :display} error)))))))

(defn- enact! [session result]
  (when result
    (when (contains? result :state) (update-state! session assoc :local (:state result)))
    (when (seq (:gesture-ends result))
      ;; At most one detached end per control. A new begin waits for that end.
      (let [ends (:gesture-ends session)
            pending (into @ends (map (juxt (comp :control-id :command) identity)) (:gesture-ends result))]
        (when (> (count pending) gesture-end-limit)
          (throw (ex-info "Device teardown emitted too many gesture ends" {})))
        (reset! ends pending)
        (retry-gesture-ends! session)))
    (dispatch-commands! session (:commands result))
    (send-midi! session (:midi result))
    (render-display! session (:display result))
    (case (:lifecycle result)
      :suspend (suspend! session)
      :resume (resume! session)
      :disconnect (do (update-state! session assoc :failure {:code (get-in result [:state :fault])})
                      (close! session true)
                      (update-state! session assoc :status :failed))
      nil)))

(defn- reconcile! [session model]
  (if-let [reconcile (get-in session [:options :profile :reconcile])]
    (let [result (reconcile (:local @(:state session)) model)]
      (enact! session result)
      (if (or (:refresh-model? result) (seq (:commands result)))
        (let [model ((get-in session [:options :model!]))]
          (adopt-epoch! session model)
          model)
        model))
    model))

(defn- close-resource! [session kind]
  (when-let [handle (get @(:resources session) kind)]
    (reset! (:resources session) (dissoc @(:resources session) kind))
    (when (= kind :schedule) (update-state! session update :schedule-generation (fnil inc 0)))
    (try (if (= kind :schedule) (handle) ((get-in session [:options kind :close!]) handle))
         (catch Throwable error (record-error! session error)))))

(defn- start-schedule! [session]
  (when-let [schedule! (when (= :active (:status @(:state session)))
                        (get-in session [:options :schedule!]))]
    (let [schedule-generation (:schedule-generation (update-state! session update :schedule-generation (fnil inc 0)))
          cancel (schedule! #(locking (:lock session)
                               (when (= schedule-generation (:schedule-generation @(:state session)))
                                 (refresh! session))))]
      (when-not (ifn? cancel) (throw (ex-info "schedule! must return a cancellation function" {})))
      (reset! (:resources session) (assoc @(:resources session) :schedule cancel)))))

(defn open!
  "Acquire owned transports and start the profile. Repeated open is idempotent.
  On partial failure, acquired resources are closed before the error propagates."
  [session]
  (locking (:lock session)
    (when (#{:closed :failed} (:status @(:state session)))
      (let [{:keys [profile midi display model!]} (:options session)
            generation (inc (:generation @(:state session)))]
        (update-state! session assoc :status :opening :generation generation
                       :local (:initial-state profile {}) :epoch (:epoch (model!)) :show-id (:show-id (model!))
                       :failure nil :last-ack nil)
        (try
          (when midi
            (let [handle ((:open! midi) #(receive! session generation %))]
              (reset! (:resources session) (assoc @(:resources session) :midi handle))))
          (when display
            (let [handle ((:open! display))]
              (reset! (:resources session) (assoc @(:resources session) :display handle))))
          (update-state! session assoc :status :active)
          (when-let [start (:start profile)]
            (enact! session (start (:local @(:state session)) (model!) (envelope! session))))
          (refresh! session)
          (start-schedule! session)
          (catch Throwable error
            (record-error! session error)
            (update-state! session assoc :status :failed :generation (inc generation))
            (close-resource! session :schedule)
            (close-resource! session :feedback-source)
            (close-resource! session :display)
            (close-resource! session :midi)
            (throw error)))))
    session))

(defn receive!
  "Deliver an input. Transport callbacks pass their captured generation so old
  listeners cannot affect a reopened session. Manual callers may omit it."
  ([session input] (receive! session (:generation @(:state session)) input))
  ([session generation input]
   (locking (:lock session)
     (let [{:keys [profile model!]} (:options session)
           state @(:state session)]
       (when (and (= generation (:generation state)) (#{:active :suspended} (:status state)))
         (try
           (let [event ((get profile :decode identity) input)]
             (when event
               (if (= :suspended (:status state))
                 (when (and (:resume-event? profile) ((:resume-event? profile) event))
                   (resume! session))
                 (let [_ (retry-gesture-ends! session)
                       model (model!)]
                   (adopt-epoch! session model)
                   (let [reconciled (reconcile! session model)]
                     (when (= (show-identity model) (show-identity reconciled))
                       (enact! session ((:input profile) (:local @(:state session)) event
                                        reconciled (envelope! session reconciled)))))
                   (refresh! session)))))
           (catch Exception error
             (record-error! session error)
             (when (:device/transport-failed (ex-data error))
               (close! session true)
               (update-state! session assoc :status :failed))
             ;; Malformed input is reported without relinquishing a healthy port.
             nil))))
     (snapshot session))))

(defn- feedback-model [session local model]
  (if-let [surface (get-in session [:options :feedback-source])]
    (try
      (let [handle (or (:feedback-source @(:resources session))
                       (let [opened ((:open! surface))]
                         (swap! (:resources session) assoc :feedback-source opened)
                         opened))]
        ((:project! surface) handle local model))
      (catch Exception error
        (record-error! session error)
        (close-resource! session :feedback-source)
        model))
    model))

(defn refresh!
  "Render latest model with bounded profile feedback while active. Also attempt
  due teardown gesture ends even if suspended or closed. The caller owns any
  retries after the session scheduler stops."
  [session]
  (locking (:lock session)
    (try
      (retry-gesture-ends! session)
      (when (= :active (:status @(:state session)))
        (let [{:keys [profile model!]} (:options session)
              model (model!)]
          (adopt-epoch! session model)
          (let [model (reconcile! session model)]
            (when-let [feedback (:feedback profile)]
              (let [local (:local @(:state session))]
                (enact! session (feedback local (feedback-model session local model) (envelope! session))))))))
      (catch Exception error
        (record-error! session error)
        (when (:device/transport-failed (ex-data error))
          (close! session true)
          (update-state! session assoc :status :failed))
        (throw error)))
    (snapshot session)))

(defn suspend!
  "Release held gestures and restore device state before giving up its display.
  MIDI input stays owned solely to recognize the explicit resume event."
  [session]
  (locking (:lock session)
    (when (= :active (:status @(:state session)))
      (let [{:keys [profile model!]} (:options session)]
        (adopt-epoch! session (model!))
        (update-state! session assoc :status :suspended)
        (close-resource! session :schedule)
        (try
          (when-let [stop (:stop profile)]
            (enact! session (stop (:local @(:state session)) (model!) (envelope! session) false)))
          (catch Exception error (record-error! session error))
          (finally
            (close-resource! session :feedback-source)
            (close-resource! session :display)))))
    (snapshot session)))

(defn resume! [session]
  (locking (:lock session)
    (when (= :suspended (:status @(:state session)))
      (let [{:keys [profile display model!]} (:options session)]
        (try
          (when display
            (reset! (:resources session)
                    (assoc @(:resources session) :display ((:open! display)))))
          (update-state! session assoc :status :active :local (:initial-state profile {}) :failure nil)
          (when-let [start (:start profile)]
            (enact! session (start (:local @(:state session)) (model!) (envelope! session))))
          (refresh! session)
          (start-schedule! session)
          (catch Throwable error
            (record-error! session error)
            (close-resource! session :feedback-source)
            (close-resource! session :display)
            (update-state! session assoc :status :suspended)))))
    (snapshot session)))

(defn close!
  "Release only this session's gestures/resources. disconnected? skips protocol
  restoration while still releasing held show instances and closing handles."
  ([session] (close! session false))
  ([session disconnected?]
   (locking (:lock session)
     (let [{:keys [profile model!]} (:options session)
           status (:status @(:state session))]
       (when-not (= :closed status)
         (update-state! session assoc :status :closing)
         (update-state! session update :generation inc)
         (close-resource! session :schedule)
         (try
           (adopt-epoch! session (model!))
           (when (and (= status :active) (:stop profile))
             (enact! session ((:stop profile) (:local @(:state session)) (model!) (envelope! session) disconnected?)))
           (catch Exception error (record-error! session error))
           (finally
             (close-resource! session :feedback-source)
            (close-resource! session :display)
             (close-resource! session :midi)
             (update-state! session assoc :status :closed :local (:initial-state profile {}))))))
     (snapshot session))))

(defn reconnect! [session]
  (close! session true)
  (open! session))
