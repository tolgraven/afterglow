(ns afterglow.control.devices.encoder-gesture
  "Receipt and release state for touch-sensitive scalar encoder edits.")

(def ^:private encoder-release-tail-ms 200)

(def ^:private encoder-end-retry-ms 100)

(defn observe-temporary-tails [state time-ms]
  (if-let [tails (:temporary-release-tails state)]
    (let [deadlines (if (:temporary-release-time-ms state) tails (update-vals tails #(+ time-ms %)))
          active (into {} (filter (fn [[_ deadline]] (> deadline time-ms))) deadlines)]
      (if (seq active)
        (assoc state :temporary-release-tails active :temporary-release-time-ms time-ms)
        (dissoc state :temporary-release-tails :temporary-release-time-ms)))
    state))

(defn start-temporary-tail [state encoder time-ms]
  (-> state (assoc-in [:temporary-release-tails encoder] (+ time-ms encoder-release-tail-ms))
      (assoc :temporary-release-time-ms time-ms)))

(defn reset-ownership [state]
  ;; Physical suppression survives the show. Preserve remaining tail intervals
  ;; until the next envelope supplies the new clock.
  (cond-> (dissoc state :encoder-gestures :encoder-releases :temporary-release-time-ms)
    (:encoder-touch-modes state)
    (update :encoder-touch-modes #(into {} (filter (comp #{:temporary} val)) %))
    (:temporary-release-time-ms state)
    (update :temporary-release-tails update-vals #(- % (:temporary-release-time-ms state)))))

(defn- gesture-command [gesture op]
  (assoc (select-keys gesture [:show-id :epoch :control-id :gesture-id :instance-id :param]) :op op))

(defn- end-encoder-gesture [{:keys [status last-sequence pending-end temporary?] :as gesture}]
  (when (and (#{:pending :accepted} status) (nil? pending-end))
    (if temporary?
      (gesture-command gesture :gesture/cancel)
      (assoc (gesture-command gesture :gesture/end) :last-sequence last-sequence))))

(defn- begin-encoder-gesture [state {:keys [control-id temporary?] :as gesture}]
  {:state (-> state (assoc-in [:encoder-gestures control-id] gesture)
              (update :encoder-releases dissoc control-id))
   :commands [(cond-> (gesture-command gesture :gesture/begin)
                temporary? (assoc :temporary? true))]})

(defn- retry-encoder-end [state {:keys [control-id released?] :as gesture}]
  (if-let [end (and released? (end-encoder-gesture gesture))]
    {:state (assoc-in state [:encoder-gestures control-id :end-retry] :in-flight)
     :commands [end]}
    {:state state}))

(defn start [state control-id selection envelope temporary?]
  (let [path [:encoder-gestures control-id]
        gesture (get-in state path)]
    (if (or (nil? gesture) (and (:released? gesture) (nil? (:retouch gesture))))
      (let [touch (assoc selection :control-id control-id :gesture-id (:command-id envelope)
                         :show-id (:show-id envelope) :epoch (:epoch envelope) :last-sequence 0
                         :temporary? temporary?)]
        (if gesture
          ;; One still-held touch waits for the preceding terminal on this encoder.
          (let [ending (assoc gesture :retouch touch)
                state (assoc-in state path ending)]
            (if (get-in ending [:end-retry :retouch-now?])
              (retry-encoder-end state ending)
              {:state state}))
          (begin-encoder-gesture state touch)))
      {:state state})))

(defn release [state control-id time-ms touched?]
  (let [path [:encoder-gestures control-id]
        gesture (get-in state path)
        end (when-not (:released? gesture) (end-encoder-gesture gesture))
        ;; A settled predecessor can disappear before input clears its retouch.
        retouch? (or (:retouch gesture)
                     (and touched? (contains? (:encoder-releases state) control-id)))
        state (cond-> state
                (:retouch gesture) (update-in path dissoc :retouch)
                (or retouch? (= :waiting (:status gesture)))
                (assoc-in [:encoder-releases control-id] time-ms))]
    (cond
      end {:state (-> state
                      (assoc-in (conj path :released?) true)
                      (assoc-in [:encoder-releases control-id] time-ms))
           :commands [end]}
      (and gesture (not (:released? gesture))) {:state (update state :encoder-gestures dissoc control-id)}
      :else {:state state})))

(defn active [state control-id]
  (let [gesture (get-in state [:encoder-gestures control-id])]
    (if (:released? gesture) (:retouch gesture) gesture)))

(defn after-release? [state control-id time-ms]
  (when-let [released-at (get-in state [:encoder-releases control-id])]
    ;; An unlabelled trailing detent must not change a just-settled edit.
    (< (- time-ms released-at) encoder-release-tail-ms)))

(defn edit
  ([state gesture edit-parameter] (edit state gesture edit-parameter nil))
  ([state gesture edit-parameter sample-context]
   (cond
     (and (= :accepted (:status gesture)) (nil? (:pending gesture)))
     (let [result (edit-parameter)]
       (if-let [write (first (:commands result))]
         (assoc result :commands [(cond-> (assoc (gesture-command gesture :gesture/sample)
                                                 :sequence (inc (:last-sequence gesture)) :value (:value write))
                                    (some? sample-context) (assoc :sample-context sample-context))])
         result))
     (= :pass-through (:status gesture)) (edit-parameter)
     :else {:state state})))

(defn detached-terminals [state]
  (into []
        (keep (fn [{:keys [pending-end] :as gesture}]
                (if-let [[command completion] pending-end]
                  {:command command :completion completion}
                  (when-let [command (end-encoder-gesture gesture)]
                    {:command command}))))
        (vals (:encoder-gestures state))))

(defn- finish-encoder-gesture [state {:keys [control-id retouch]}]
  (if retouch
    (begin-encoder-gesture state retouch)
    {:state (update state :encoder-gestures dissoc control-id)}))

(defn acknowledge [state {:keys [op control-id gesture-id sequence time-ms] :as command}
                            {:keys [status code reason completion detached-gesture]}]
  (let [path [:encoder-gestures control-id]
        gesture (get-in state path)
        failure (or code reason)]
    (cond
      (not= gesture-id (:gesture-id gesture)) {:state state}

      (and (= :gesture/begin op) (= :gesture-end-pending failure) detached-gesture)
      {:state (assoc-in state path (assoc gesture :status :waiting :waiting-for detached-gesture))}

      (#{:gesture/end :gesture/cancel} op)
      (cond
        (#{:stale-epoch :wrong-show} failure) {:state (update state :encoder-gestures dissoc control-id)}
        (or (= :accepted status) (= :unknown-gesture failure)) (finish-encoder-gesture state gesture)
        (= :pending status) {:state (assoc-in state (conj path :pending-end) [command completion])}
        (#{:dispatch-busy :dispatch-error :queue-full :gesture-end-queued} failure)
        ;; A waiting retouch may use the first retry immediately. The released
        ;; gesture keeps its feedback deadline even if that touch goes away.
        (let [retry {:at-ms (+ time-ms encoder-end-retry-ms)
                     :retouch-now? (not= :in-flight (:end-retry gesture))}
              ending (assoc (dissoc gesture :pending-end) :end-retry retry)
              state (assoc-in state path ending)]
          (if (and (:retouch ending) (:retouch-now? retry))
            (retry-encoder-end state ending)
            {:state state}))
        :else {:state (update-in state path dissoc :pending-end :end-retry)})

      (and (= :gesture/begin op) (= :rejected status) (:released? gesture))
      (finish-encoder-gesture state gesture)

      :else
      {:state (assoc-in state path
                        (cond-> gesture
                          (= :pending status) (assoc :pending [command completion])
                          (not= :pending status) (dissoc :pending)
                          (= :gesture/begin op) (assoc :status (if (and (= :operator-required code)
                                                                       (not (:temporary? gesture)))
                                                                :pass-through status))
                          (and (= :gesture/sample op) (= :accepted status)) (assoc :last-sequence sequence)))})))

(defn- settled-encoder-receipts [{:keys [pending pending-end]}]
  (let [[command completion] pending
        [end end-completion] pending-end]
    (cond-> []
      (and completion (realized? completion)) (conj [command @completion])
      (and end-completion (realized? end-completion)) (conj [end @end-completion]))))

(defn reconcile [state]
  (reduce (fn [{:keys [state commands]} [command ack]]
            (let [result (acknowledge state command ack)]
              {:state (:state result) :commands (into commands (:commands result))}))
          {:state state :commands []}
          (mapcat settled-encoder-receipts (sort-by :control-id (vals (:encoder-gestures state))))))

(defn retry-due [{:keys [state] :as result} time-ms]
  (reduce (fn [result {:keys [end-retry] :as gesture}]
            (if (and (:at-ms end-retry) (>= time-ms (:at-ms end-retry)))
              (let [retry (retry-encoder-end (:state result) gesture)]
                (-> result (assoc :state (:state retry))
                    (update :commands (fnil into []) (:commands retry))))
              result))
          result (sort-by :control-id (vals (:encoder-gestures state)))))

(defn- detached-gesture-open? [model {:keys [instance-id param] :as detached}]
  (let [owner (get-in model [:control :edit-history :open [:instance-param instance-id param]])
        identity-fields [:control-id :gesture-id]]
    (= (select-keys detached identity-fields) (select-keys owner identity-fields))))

(defn resume-begins [state model ending-controls lifting]
  ;; Reconciliation sees a decoded lift before the normal input clears its touch.
  (let [cancel-retouch? (some? (get-in state [:encoder-gestures lifting :retouch]))
        state (cond-> state cancel-retouch? (update-in [:encoder-gestures lifting] dissoc :retouch))
        ready? (fn [{:keys [status control-id encoder waiting-for]}]
                 (and (= :waiting status) (not= control-id lifting)
                      (contains? (:touches state) encoder)
                      (not (contains? ending-controls control-id))
                      (not (detached-gesture-open? model waiting-for))))
        gestures (filter ready? (vals (:encoder-gestures state)))]
    (when (or cancel-retouch? (seq gestures))
      (reduce (fn [{:keys [state commands]} gesture]
                (let [resumed (begin-encoder-gesture state (dissoc gesture :status :waiting-for))]
                  {:state (:state resumed) :commands (into commands (:commands resumed))}))
              {:state state :commands []}
              (sort-by :control-id gestures)))))
