(ns afterglow.control.devices.push-strip
  "Shared interaction state for the selected-effect opacity strip.")

(defn value [state model]
  (when-let [instance (get-in model [:instances (:selected-instance state)])]
    (get-in instance [:system :opacity] 1.0)))

(defn begin [state model route]
  (if (:strip-touch state)
    state
    (assoc state :strip-touch
           (cond-> {:route route}
             (and (= :opacity route) (some? (value state model)))
             (assoc :target (assoc (select-keys model [:show-id :epoch])
                                   :instance-id (:selected-instance state)))))))

(defn release [state]
  (dissoc state :strip-touch))

(defn fence-selection
  ([state] (fence-selection state (:selected-instance state)))
  ([state selected-instance]
   (let [target (get-in state [:strip-touch :target])]
     (cond-> state
       (and target (not= (:instance-id target) selected-instance))
       (update :strip-touch dissoc :target)))))

(defn fence [state model]
  (let [state (fence-selection state)
        target (get-in state [:strip-touch :target])]
    ;; Keep the contact latched so a duplicate down cannot capture a new target.
    (cond-> state
      (and target
           (or (nil? (value state model))
               (not= (select-keys target [:show-id :epoch])
                     (select-keys model [:show-id :epoch]))))
      (update :strip-touch dissoc :target))))

(defn sample [state model position]
  (let [state (fence state model)
        target (get-in state [:strip-touch :target])]
    (cond-> {:state state}
      (and target (not (== position (value state model))))
      (assoc :commands [(assoc target :op :instance/opacity-set :value position)]))))
