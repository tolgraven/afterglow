(ns afterglow.render.fields
  "Evaluate requested numeric fields at the frame owner's compute boundary."
  (:require [afterglow.runtime.faults :as faults])
  (:import [java.util IdentityHashMap]))

(defrecord UniformField [type components values])

(defn uniform-batch
  "Represent a known uniform GPU sample using one exclusively owned tuple per
  field. Only the local fixture renderer consumes this layout."
  [sample target-count]
  (assoc sample :count target-count :outputs (update-vals (:outputs sample) map->UniformField)))

(defn uniform-field? [field] (instance? UniformField field))

;; Writes the evaluated array in place. The field evaluator must return arrays
;; this request owns; never route it through a reuse binding with
;; :shared-outputs? true (see doc/architecture/pure-effect-reuse.md).
(defn- scale-field! [outputs attribute gain]
  (let [values (get-in outputs [attribute :values])]
    (when-not (and (instance? double/1 values)
                   (number? gain) (<= 0 gain 1))
      (throw (ex-info "Field envelope needs an evaluated field and a gain in [0,1]"
                      {:attribute attribute :gain gain})))
    (when-not (== 1 gain)
      (let [^doubles values values, gain (double gain)]
        (dotimes [i (alength values)]
          (aset-double values i (* gain (aget values i))))))))

(defn- evaluate-request! [evaluate! {:keys [group env scales]}]
  (when-not (and (some? group) (map? env) (or (nil? scales) (map? scales)))
    (throw (ex-info "A field request needs a group, captured environment and optional scales" {})))
  (let [{:keys [outputs count]} (evaluate! group env)]
    (when-not (and (integer? count) (<= 0 count) (map? outputs) (seq outputs))
      (throw (ex-info "Field evaluator must return a count and named outputs" {})))
    (doseq [[attribute gain] scales] (scale-field! outputs attribute gain))
    {:count count :outputs outputs}))

(defn frame-evaluator
  "Create a single frame owner's evaluator. Effect middleware can return an ordinary
  :batch block carrying :field-request {:group group :env env :scales {field gain}}.
  evaluate! receives the group and captured env and returns the evaluate-batch
  result layout with exclusively owned arrays. Scales are optional.

  Call the returned function with ordered contributions before resolve-contributions.
  Reuse it only for retries of this same frame. Requests already evaluated for
  healthy effects retain their results if another effect is isolated. Release
  the function with the frame. A new frame evaluates its own captured inputs."
  [evaluate!]
  (let [completed (volatile! nil)]
    (fn [contributions]
      ;; Keep ordinary streams on the existing dense path without copying every
      ;; block. Only requests need a replacement block and owned output arrays.
      (let [blocks (if (vector? contributions) contributions (vec contributions))]
        (reduce-kv
         (fn [resolved index {:keys [kind batch source] :as block}]
           (if (and (= :batch kind) (contains? batch :field-request))
             (try
               (let [request (:field-request batch)
                     ^IdentityHashMap cache (or @completed (vreset! completed (IdentityHashMap.)))
                     result (or (.get cache request)
                                (let [result (evaluate-request! evaluate! request)]
                                  (.put cache request result)
                                  result))]
                 (when-not (= (count (:target-ids batch)) (:count result))
                   (throw (ex-info "Evaluated field count differs from selected fixture count"
                                   {:count (:count result) :targets (count (:target-ids batch))})))
                 (assoc resolved index (assoc block :batch (merge (dissoc batch :field-request) result))))
               (catch Exception error (throw (faults/attributed-error error source))))
             resolved))
         blocks blocks)))))
