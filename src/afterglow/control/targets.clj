(ns afterglow.control.targets
  "Portable selectors accepted by cue definitions and launch adapters.")

(defn- id? [v] (or (keyword? v) (and (string? v) (not (.isBlank ^String v)))))

(defn selector? [selector]
  (or (= selector :all)
      (and (map? selector) (= 1 (count selector))
           (case (ffirst selector)
             :fixture-ids (let [ids (:fixture-ids selector)] (and (vector? ids) (every? id? ids)))
             (:group-id :volume-id) (id? (val (first selector)))
             false))))
