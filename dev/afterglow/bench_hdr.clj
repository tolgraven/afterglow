(ns afterglow.bench-hdr
  "Measure HDR packing and single-bounce spill on a long RGB strip."
  (:require [afterglow.render.frame :as frame])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]))

(defn- fixtures [n]
  (mapv (fn [i] {:id i :address (inc (mod (* i 3) 510)) :universe (quot (* i 3) 510)
                 :position [(* i 0.01) 0 0] :channels {:red 1 :green 2 :blue 3}}) (range n)))

(defn- measure [patch limit hdr warmup measurements]
  (let [ids (:target-order patch)
        rgb (double-array (mapcat #(vector (if (zero? (rem % 10)) limit 0.65) 0.3 0.15) ids))
        blocks [{:kind :batch :batch {:target-ids ids :outputs {:color {:type :vec3 :components 3 :values rgb}}}}]
        run! #(frame/resolve-contributions patch blocks {:include-values? false :compact-values? true :hdr hdr})
        ^ThreadMXBean bean (ManagementFactory/getPlatformMXBean ThreadMXBean)]
    (dotimes [_ warmup] (run!))
    (let [cpu (.getCurrentThreadCpuTime bean) bytes (.getCurrentThreadAllocatedBytes bean)]
      (dotimes [_ measurements] (run!))
      {:mean-owner-cpu-ms (/ (- (.getCurrentThreadCpuTime bean) cpu) 1.0e6 measurements)
       :mean-owner-bytes (/ (double (- (.getCurrentThreadAllocatedBytes bean) bytes)) measurements)})))

(defn -main [& args]
  (let [[n warmup measurements] (if (seq args) (mapv parse-long args) [2048 150 200])
        patch (frame/compile-patch (fixtures n))
        spill {:spill 1.0 :radius 0.05 :white-mix 1.0 :spill-white-mix 1.0}]
    (prn {:pixels n :warmup warmup :frames measurements
          :sdr (measure patch 0.9 nil warmup measurements)
          :neutral (measure patch 0.9 {} warmup measurements)
          :boost (measure patch 0.9 (assoc spill :gain 1.2) warmup measurements)
          :authored-overrange (measure patch 1.21 spill warmup measurements)})))
