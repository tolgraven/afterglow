(ns afterglow.control.devices.session
  "Explicit device I/O shell. Each session serializes its own resource lifecycle;
  show dispatch remains the host coordinator's responsibility. No work starts at
  namespace load. Profiles are pure transitions; transports are injected maps.")

(declare receive! refresh! close! suspend! resume!)

(defn create
  "Create an inert session. Required options: :session-id, :profile, :model!
  (snapshot fn), :dispatch! (command -> result/ack synchronously), :now-ms!.
  A grid cue launch/release may return a queue receipt. Profiles can reconcile
  those receipts against the committed model before input and feedback.
  Optional :midi transport {:open! (fn [receive!] handle), :send! (fn [handle
  messages]), :close! (fn [handle])}; :display uses :open! [] and :render! [handle
  view]. Optional :schedule! takes a refresh callback and returns cancellation.
  A :feedback-source may supply :open! [], :project! [handle local model] and
  :close! [handle]. Only feedback sees its projection; input always receives
  the committed model. Its handle belongs to the active session.
  Call open! explicitly; without schedule! the host owns the refresh cadence."
  [{:keys [session-id profile model! dispatch! now-ms!] :as options}]
  (when-not (and (or (keyword? session-id) (and (string? session-id) (seq session-id)))
                 (map? profile) (every? ifn? [model! dispatch! now-ms!]))
    (throw (ex-info "Session needs ID, profile, model!, dispatch! and now-ms!" {})))
  {:options options :lock (Object.) :resources (atom {})
   :command-prefix (if (:grid-launches? profile) (str (java.util.UUID/randomUUID)) session-id)
   :state (atom {:status :closed :generation 0 :counter 0
                 :local (:initial-state profile {}) :errors []})})

(defn snapshot [session] @(:state session))

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

(defn- adopt-epoch! [session model]
  (let [epoch (:epoch model) state @(:state session)]
    (when-not (= [(:show-id model) epoch] [(:show-id state) (:epoch state)])
      (update-state! session assoc :show-id (:show-id model) :epoch epoch
                     :local (if-let [reset-model (:reset-model (:profile (:options session)))]
                              (reset-model (:local state))
                              (:initial-state (:profile (:options session)) {}))))))

(defn- grid-launch? [template]
  (and (= :cue/launch (:op template)) (contains? template :grid)))

(defn- dispatch-commands! [session commands]
  (let [{:keys [dispatch! profile]} (:options session)]
    (loop [remaining (seq commands) count 0]
      (when-let [template (first remaining)]
        (when (>= count 64)
          (throw (ex-info "Device transition emitted too many commands" {})))
        ;; Admission time/identity are assigned here, including delayed releases.
        (let [envelope (envelope! session)
              scheduled-launch? (grid-launch? template)
              timed-cue? (or scheduled-launch? (= :cue/cancel-launch (:op template)))
              stale? (and timed-cue? (some #(and (contains? template %)
                                                (not= (get template %) (get envelope %)))
                                          [:show-id :epoch]))
              command (cond-> (merge template envelope)
                        (and scheduled-launch? (:command-id template)) (assoc :command-id (:command-id template)))
              response (if stale? {:status :rejected :reason :stale-epoch} (dispatch! command))
              ack (or (:ack response) response)]
          (when-not (or (#{:accepted :rejected} (:status ack))
                        (and timed-cue? (#{:pending :fired :cancelled :missed} (:status ack))))
            (throw (ex-info "dispatch! must return a synchronous command acknowledgement" {})))
          (update-state! session assoc :last-ack ack)
          (let [result (when-let [acknowledge (:ack profile)]
                         (acknowledge (:local @(:state session)) command ack))]
            (when result (update-state! session assoc :local (:state result)))
            (recur (concat (next remaining) (:commands result)) (inc count))))))))

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
      (if (seq (:commands result))
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
                 (let [model (model!)]
                   (adopt-epoch! session model)
                   (let [model (reconcile! session model)]
                     (enact! session ((:input profile) (:local @(:state session)) event model (envelope! session model))))
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
  "Render latest model with bounded profile feedback. No background scheduler
  is allocated; callers can invoke this from a shared UI scheduler."
  [session]
  (locking (:lock session)
    (when (= :active (:status @(:state session)))
      (try
        (let [{:keys [profile model!]} (:options session)
              model (model!)]
          (adopt-epoch! session model)
          (let [model (reconcile! session model)]
            (when-let [feedback (:feedback profile)]
              (let [local (:local @(:state session))]
                (enact! session (feedback local (feedback-model session local model) (envelope! session)))))))
        (catch Exception error
          (record-error! session error)
          (when (:device/transport-failed (ex-data error))
            (close! session true)
            (update-state! session assoc :status :failed))
          (throw error))))
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
