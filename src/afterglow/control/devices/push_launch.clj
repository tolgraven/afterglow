(ns afterglow.control.devices.push-launch
  "Route Push pad launches through the show owner's optional musical grid."
  (:require [afterglow.time :as time]))

(defn grid [options]
  (let [grid (get options :launch-grid :off)]
    (when-not (= :off grid)
      (when-not (and (empty? (time/validate-duration grid))
                     (not (contains? grid :ms)) (pos? (val (first grid))))
        (throw (ex-info "Push launch grid needs one positive beat, bar or phrase interval"
                        {:launch-grid grid})))
      grid)))

(defn- terminal-ack [ack]
  (case (:status ack)
    :fired (assoc ack :status :accepted)
    (:cancelled :missed :rejected) (assoc ack :status :rejected)
    :accepted ack
    nil))

(defn- receipt [launch-receipt model id]
  (or (when launch-receipt (launch-receipt model id))
      (get-in model [:control :history id :ack])))

(defn- retain-pending [state result]
  (cond-> result
    (contains? state ::pending) (assoc-in [:state ::pending] (::pending state))))

(defn- reconcile [acknowledge launch-receipt state model]
  (when (seq (::pending state))
    (reduce (fn [{:keys [state commands]} command]
              (if-let [ack (terminal-ack (receipt launch-receipt model (:command-id command)))]
                (let [result (acknowledge state command ack)]
                  {:state (:state result) :commands (into commands (:commands result))})
                {:state (update state ::pending conj command) :commands commands}))
            {:state (assoc state ::pending []) :commands []}
            (::pending state))))

(defn with-grid
  "When enabled, adapt owner queue receipts to the normal Push launch feedback.
  A host can look up a launch receipt with :launch-receipt [model launch-id]."
  [{:keys [input ack reset-model stop] :as profile} grid launch-receipt]
  (if (nil? grid)
    profile
    (let [acknowledge (fn [state command receipt]
                        (retain-pending state (ack state command receipt)))]
      (when-not (or (nil? launch-receipt) (ifn? launch-receipt))
        (throw (ex-info "Push launch-receipt must be a function" {})))
      (assoc profile
             :grid-launches? true
             :input (fn [state event model envelope]
                      (let [result (retain-pending state (input state event model envelope))
                            raw (select-keys envelope [:time-ms])]
                        (if (seq (:commands result))
                          (update result :commands
                                  (fn [commands]
                                    (mapv #(if (= :cue/launch (:op %))
                                             (cond-> (merge envelope % {:grid grid})
                                               (seq raw) (assoc :raw raw))
                                             %) commands)))
                          result)))
             :ack (fn [state command receipt]
                    (if (and (= :cue/launch (:op command)) (contains? command :grid))
                      (if (= :pending (:status receipt))
                        ;; Keep feedback bookkeeping bounded even if a host loses
                        ;; its receipt. Held releases are owned independently.
                        {:state (update state ::pending #(vec (take-last 256 (conj (vec %) command))))}
                        (acknowledge state command (terminal-ack receipt)))
                      (acknowledge state command receipt)))
             :reconcile (partial reconcile acknowledge launch-receipt)
             :reset-model #(dissoc (reset-model %) ::pending)
             :stop (fn [state model envelope disconnected?]
                     (stop (dissoc state ::pending) model envelope disconnected?))))))
