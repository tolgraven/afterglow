(ns afterglow.control.instance-order
  "Priority and render position shared by the control owner and frame engine.")

(defn valid-render-order? [instance]
  (or (not (contains? instance :render-order))
      (let [order (:render-order instance)]
        (and (integer? order) (not (neg? order))))))

(defn sort-key
  "Priority always wins. A reorder positions the existing tier explicitly;
  subsequent launches append by their original launch order. The standalone
  frame kernel uses input position to break legacy ties."
  ([instance] (sort-key instance (:id instance)))
  ([{:keys [priority order render-order]} tie-breaker]
   (if (some? render-order)
     [priority 0 render-order tie-breaker]
     [priority 1 order tie-breaker])))

(defn ordered [model]
  (vec (sort-by sort-key (vals (:instances model)))))
