(ns afterglow.control.instance-order
  "Priority and render position shared by the control owner and frame engine."
  (:import [clojure.lang Ratio]
           [java.math BigDecimal]
           [java.util Comparator]))

(defn- compare-ratio-to-decimal ^long [^Ratio ratio ^BigDecimal decimal]
  ;; Cross-multiply to keep exact priorities without dividing or rounding.
  (.compareTo (BigDecimal. (.-numerator ratio))
              (.multiply decimal (BigDecimal. (.-denominator ratio)))))

(defn compare-priority
  "Compare finite priorities without losing exact values. Floating-point values
  use their standard decimal representation when compared across types. Missing
  priorities in partial models sort before numeric priorities."
  ^long [left right]
  (cond
    (or (identical? (class left) (class right)) (nil? left) (nil? right)) (compare left right)
    (ratio? left) (compare-ratio-to-decimal left (bigdec right))
    (ratio? right) (- (compare-ratio-to-decimal right (bigdec left)))
    :else (.compareTo (bigdec left) (bigdec right))))

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
  "Return the render position as data. Use render-instance-comparator to sort
  model instances with mixed numeric priorities."
  ([instance] (sort-key instance (:id instance)))
  ([{:keys [order render-order] :as instance} tie-breaker]
   (let [priority (effective-priority instance)]
     (if (some? render-order)
       [priority 0 render-order tie-breaker]
       [priority 1 order tie-breaker]))))

(defn- compare-render-position ^long [left right]
  (let [priority (compare-priority (effective-priority left) (effective-priority right))]
    (if (zero? priority)
      (let [left-order (:render-order left)
            right-order (:render-order right)]
        (cond
          (nil? left-order) (if (nil? right-order) (compare (:order left) (:order right)) 1)
          (nil? right-order) -1
          :else (compare left-order right-order)))
      priority)))

(def ^Comparator render-position-comparator
  "Sort by effective priority and explicit render position. New launches append
  within their tier. Stable sorting preserves input order when positions tie."
  (reify Comparator
    (compare [_ left right] (compare-render-position left right))))

(def ^Comparator render-instance-comparator
  "Order model instances with stable IDs as the last tie-breaker."
  (reify Comparator
    (compare [_ left right]
      (let [position (compare-render-position left right)]
        (if (zero? position) (compare (:id left) (:id right)) position)))))

(def ^Comparator authored-instance-comparator
  "Order cue and group views by launch priority and launch order."
  (reify Comparator
    (compare [_ left right]
      (let [priority (compare-priority (:priority left) (:priority right))]
        (if (zero? priority)
          (let [order (compare (:order left) (:order right))]
            (if (zero? order) (compare (:id left) (:id right)) order))
          priority)))))

(defn ordered [model]
  (vec (sort render-instance-comparator (vals (:instances model)))))

(defn- layer-id [instance]
  (get-in instance [:source :native-layer :id]))

(defn priority-override-errors
  "Return path/message errors for a frame-local instance ID to finite priority
  map. Unknown IDs are ignored because an instance can end between sampling and
  evaluation. Members of one native layer must not receive different values."
  [instances overrides]
  (if-not (map? overrides)
    [{:path [] :message "Priority overrides must be an instance ID to priority map"}]
    (let [invalid (into [] (keep (fn [[id priority]]
                                   (when-not (and (number? priority) (Double/isFinite (double priority)))
                                     {:path [id] :message "Priority override must be finite"})))
                        overrides)
          by-layer (reduce (fn [layers [id priority]]
                             (if-let [layer (some-> (get instances id) layer-id)]
                               (update layers layer (fnil conj #{}) (bigdec priority))
                               layers))
                           {} (when (empty? invalid) overrides))]
      (into invalid (keep (fn [[layer values]]
                            (when (> (count values) 1)
                              {:path [layer] :message "Native layer members need one priority override"})))
            by-layer))))

(defn with-priority-overrides
  "Return frame-local render positions for instances with modulated priority.
  An override that differs from the effective priority places the instance, and
  every other member of its native layer, in the overriding tier with no explicit
  render position, so equal priorities tie by launch order. An override equal to
  the current effective priority keeps the existing position. The result is for
  ordering one frozen frame only; it is never written back to the model."
  [instances overrides]
  (if (empty? overrides)
    instances
    (let [layer-values (into {} (keep (fn [[id priority]]
                                        (when-let [layer (some-> (get instances id) layer-id)]
                                          [layer priority])))
                             overrides)
          override-for (fn [instance]
                         (if-let [layer (layer-id instance)]
                           (get layer-values layer)
                           (get overrides (:id instance))))]
      (persistent!
       (reduce-kv (fn [result id instance]
                    (let [priority (override-for instance)]
                      (if (and (some? priority)
                               (not (zero? (compare-priority priority (effective-priority instance)))))
                        (assoc! result id (-> instance (assoc :priority priority)
                                              (dissoc :render-priority :render-order)))
                        result)))
                  (transient instances) instances)))))

(defn ordered-with-priorities
  "Order model instances as one frame with frame-local priority overrides."
  [model overrides]
  (vec (sort render-instance-comparator (vals (with-priority-overrides (:instances model) overrides)))))
