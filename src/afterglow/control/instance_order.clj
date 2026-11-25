(ns afterglow.control.instance-order
  "Priority and render position shared by the control owner and frame engine.")

(defn effective-priority [instance]
  (get instance :render-priority (:priority instance)))

(defn valid-render-position? [instance]
  (and (or (not (contains? instance :render-order))
           (let [order (:render-order instance)]
             (and (integer? order) (not (neg? order)))))
       (or (not (contains? instance :render-priority))
           (let [priority (:render-priority instance)]
             (and (contains? instance :render-order)
                  (number? priority) (Double/isFinite (double priority)))))))

(defn sort-key
  "Sort by effective priority and explicit render position. Upcoming launches
  append within their authored tier. The standalone frame kernel uses input
  position to break legacy ties."
  ([instance] (sort-key instance (:id instance)))
  ([{:keys [order render-order] :as instance} tie-breaker]
   (let [priority (effective-priority instance)]
     (if (some? render-order)
       [priority 0 render-order tie-breaker]
       [priority 1 order tie-breaker]))))

(defn ordered [model]
  (vec (sort-by sort-key (vals (:instances model)))))
