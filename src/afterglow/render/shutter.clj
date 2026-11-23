(ns afterglow.render.shutter
  "Interpret the physical coarse DMX ranges that close a profiled light gate."
  (:require [clojure.string :as str]))

(defn profile [channels]
  (into []
        (keep (fn [attr]
                (let [{:keys [functions inverted-from fine fine-offset]} (get channels attr)
                      closed (filterv #(and (keyword? (:type %)) (str/includes? (name (:type %)) "closed")) functions)]
                  (when (seq closed) [attr inverted-from (boolean (or fine fine-offset)) closed]))))
        [:shutter :strobe]))

(defn open? [profile read-value]
  (every? (fn [[field pivot fine? ranges]]
            (let [level (* 255.0 (double (read-value field 0.0)))
                  raw (if (and pivot (>= level (double pivot))) (- 255.0 (- level (double pivot))) level)
                  coarse (if fine? (long raw) (Math/round (double raw)))]
              (not-any? #(<= (:start %) coarse (:end %)) ranges))) profile))
