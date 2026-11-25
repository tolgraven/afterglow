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
  use their standard decimal representation when compared across types."
  ^long [left right]
  (cond
    (identical? (class left) (class right)) (compare left right)
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
