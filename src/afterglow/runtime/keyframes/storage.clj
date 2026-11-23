(ns afterglow.runtime.keyframes.storage
  "Transit-ready, checked keyframe endpoints. Dense doubles use standard binary
  values in network byte order. Runtime rig bindings and callbacks are rebuilt."
  (:require [afterglow.runtime.keyframes :as kf]
            [afterglow.runtime.keyframes.values :as values]
            [afterglow.time :as time])
  (:import [java.nio ByteBuffer]))

(defn- invalid! [] (throw (ex-info "Invalid saved keyframe window" {:type ::invalid-window})))

(defn- pack [^doubles data]
  (let [out (ByteBuffer/allocate (Math/multiplyExact (int Double/BYTES) (alength data)))]
    (.put (.asDoubleBuffer out) data)
    (.array out)))

(defn- unpack [data]
  (when-not (and (bytes? data) (zero? (mod (alength ^bytes data) Double/BYTES))) (invalid!))
  (let [input (.asDoubleBuffer (ByteBuffer/wrap data))
        out (double-array (.remaining input))]
    (.get input out)
    out))

(def window-keys [:unit :span :start :end :inputs :options :origin-clock :target-clock :progress])

(defn freeze [window]
  (when window
    (let [encode #(values/map-columns pack %)]
      (assoc (select-keys window window-keys) :origin (encode (:origin window)) :target (encode (:target window))))))

(defn- value? [attribute v]
  (if (or (= :color attribute) (values/geometry attribute))
    (and (vector? v) (= 3 (count v)) (every? time/finite-number? v))
    (time/finite-number? v)))

(defn- validate-block! [{:keys [kind assignments batch] :as block}]
  (let [target-id? #(or (keyword? %) (string? %))
        blends #{:replace :add :max}
        valid-row? (fn [{:keys [target-id attribute value blend]}]
                     (and (target-id? target-id) (values/continuous attribute)
                          (or (nil? blend) (blends blend)) (value? attribute value)))]
    (case kind
      :assignments (when-not (and (= #{:kind :assignments} (set (keys block)))
                                  (vector? assignments) (every? valid-row? assignments)) (invalid!))
      :batch (let [{:keys [target-ids count outputs blend]} batch n (clojure.core/count target-ids)]
               (when-not (and (= #{:kind :batch} (set (keys block)))
                              (vector? target-ids) (every? target-id? target-ids)
                              (or (nil? count) (= count n)) (map? outputs) (seq outputs)
                              (or (nil? blend) (blends blend))
                              (every? (fn [[attr {:keys [components type values]}]]
                                        (let [vec3? (or (= attr :color) (values/geometry attr))]
                                          (and (values/continuous attr) (= components (if vec3? 3 1))
                                               (= type (if vec3? :vec3 :number)) (instance? double/1 values)
                                               (= (alength ^doubles values) (* n components))
                                               (every? time/finite-number? values))))
                                      outputs))
                 (invalid!)))
      (invalid!))))

(defn restore [saved fixtures epoch]
  (when saved
    (let [{:keys [unit span start end inputs progress options origin-clock target-clock]} saved]
      (when-not (and (map? saved) (#{:ms :beats} unit)
                     (every? time/finite-number? [span start end progress]) (pos? span) (< start end)
                     (vector? inputs) (= 9 (count inputs))
                     (every? (fn [c] (every? time/finite-number? ((juxt :time-ms :beat :bpm) c))) [origin-clock target-clock])
                     (or (nil? options) (kf/validate! options))) (invalid!))
      (let [decode (fn [blocks]
                     (when-not (vector? blocks) (invalid!))
                     (let [out (values/map-columns unpack blocks)] (run! validate-block! out) out))
            origin (decode (:origin saved)) target (decode (:target saved))
            ;; Check topology before a malformed file can replace the running show.
            _ (values/blend origin target 0.5 (nth inputs 5))]
        (assoc (select-keys saved window-keys)
               :epoch epoch :rig fixtures :origin origin :target target
               :result (values/blend origin target progress (nth inputs 5)))))))
