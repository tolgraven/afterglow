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
  (when (and window (not (:forecast-failed? window)))
    (let [encode #(values/map-columns pack %)]
      (assoc (select-keys window window-keys) :origin (encode (:origin window)) :target (encode (:target window))))))

(defn restore [saved fixtures epoch]
  (when saved
    (let [{:keys [unit span start end inputs progress options origin-clock target-clock]} saved]
      (when-not (and (map? saved) (#{:ms :beats} unit)
                     (every? time/finite-number? [span start end progress]) (pos? span) (< start end)
                     (vector? inputs) (= 9 (count inputs)) (or (nil? (nth inputs 5)) (boolean? (nth inputs 5)))
                     (every? (fn [c] (every? time/finite-number? ((juxt :time-ms :beat :bpm) c))) [origin-clock target-clock])
                     (or (nil? options) (kf/validate! options))) (invalid!))
      (let [decode (fn [blocks]
                     (when-not (vector? blocks) (invalid!))
                     (with-meta (values/validate-blocks! (values/map-columns unpack blocks) (nth inputs 5))
                       {::values/restored true}))
            [origin target] (values/endpoints (decode (:origin saved)) (decode (:target saved)) fixtures (:curve options))]
        (assoc (select-keys saved window-keys)
               :epoch epoch :rig fixtures :origin origin :target target
               :result (values/blend origin target progress (nth inputs 5)))))))
