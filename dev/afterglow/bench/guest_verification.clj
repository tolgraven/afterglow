(ns afterglow.bench.guest-verification
  "Measure only the independent readback checks on a retained render group."
  (:require [afterglow.render.distributed :as distributed]
            [afterglow.render.ir :as ir]
            [afterglow.render.verified :as verified])
  (:import [java.nio ByteBuffer ByteOrder]))

(defn -main [& [size]]
  (let [n (parse-long (or size "4096"))
        points (mapv #(vector (* 0.005 %) 2.0 0.4) (range n))
        field {:op :sin :args [{:op :add :args [{:op :position :axis :x} {:op :param :key :phase}]}]}
        expressions {:direction {:op :vec3 :args [field {:op :cos :args [field]} field]}}
        env {:params {:phase 0.3}} plan (ir/compile-batch expressions) group (distributed/prepare-group expressions points plan)
        job {:start 0 :count n} raw (ir/evaluate-batch plan env points)
        bytes (byte-array (* 3 n Float/BYTES)) buffer (.asFloatBuffer (.order (ByteBuffer/wrap bytes) ByteOrder/LITTLE_ENDIAN))
        _ (doseq [x (get-in raw [:outputs :direction :values])] (.put buffer (float x)))
        witness (aclone bytes)
        sample (fn [f] (let [t (System/nanoTime)] (assert (f)) (/ (- (System/nanoTime) t) 1e6)))
        measure (fn [f] (dotimes [_ 16] (sample f))
                  (let [xs (vec (sort (repeatedly 64 #(sample f))))]
                    {:median-ms (xs 31) :p95-ms (xs 60)}))]
    (prn {:rows n :floats (* 3 n) :samples 64
          :full (measure #(verified/readback group env job bytes))
          :redundant (measure #(verified/agree? group env job bytes witness))})))
