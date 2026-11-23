(ns afterglow.bench.typed-expression
  "Measure one full CPU batch call over a captured expression and ordered rig positions."
  (:require [afterglow.render.ir :as ir]
            [clojure.edn :as edn])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]
           [java.util Arrays]))

(defn- frame-env [env frame]
  (let [beat (* frame 0.05)]
    (merge {:elapsed-beats beat :beat beat :elapsed-ms (* 25 frame) :time-ms (* 25 frame)
            :meter {:beats-per-bar 4 :bars-per-phrase 4}}
           env)))

(defn- verify-fields! [scalar batch positions env]
  (let [result (ir/evaluate-batch batch env positions)]
    (doseq [[attribute evaluate] scalar]
      (let [expected (double-array (mapcat (fn [position]
                                            (let [v (evaluate (assoc env :position position))]
                                              (if (vector? v) v [v]))) positions))
            ^doubles actual (get-in result [:outputs attribute :values])]
        (when-not (Arrays/equals expected actual)
          (throw (ex-info "CPU batch differs from the scalar reference" {:attribute attribute})))))))

(defn- distribution [samples]
  (let [sorted (vec (sort samples))
        at (fn [q] (nth sorted (dec (int (Math/ceil (* q (count sorted)))))))]
    {:mean (/ (double (reduce + samples)) (count samples))
     :p50 (at 0.5) :p95 (at 0.95) :p99 (at 0.99)}))

(defn measure [{:keys [outputs positions env]} warmup frames]
  (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        _ (when-not (and (.isThreadCpuTimeEnabled bean) (.isThreadAllocatedMemoryEnabled bean))
            (throw (ex-info "This benchmark needs current thread CPU and allocation counters" {})))
        plan (ir/compile-batch outputs)
        scalar (update-vals outputs ir/compile-expression)
        sample (fn [i]
                 (let [frame (frame-env env i)
                       cpu (.getCurrentThreadCpuTime bean)
                       bytes (.getCurrentThreadAllocatedBytes bean)
                       wall (System/nanoTime)
                       result (ir/evaluate-batch plan frame positions)
                       end (System/nanoTime)
                       allocated (- (.getCurrentThreadAllocatedBytes bean) bytes)
                       cpu-ns (- (.getCurrentThreadCpuTime bean) cpu)
                       hashes (mapv (fn [key] (Arrays/hashCode ^doubles (get-in result [:outputs key :values])))
                                    (sort (keys outputs)))]
                   {:wall-ms (/ (double (- end wall)) 1e6) :cpu-ms (/ (double cpu-ns) 1e6)
                    :allocated-bytes allocated :hash hashes}))]
    (doseq [frame [0 (dec frames)]] (verify-fields! scalar plan positions (frame-env env frame)))
    (dotimes [i warmup] (sample i))
    (let [rows (mapv sample (range frames))]
      {:targets (count positions) :fields (vec (sort (keys outputs))) :warmup warmup :frames frames
       :java (System/getProperty "java.runtime.version") :processors (.availableProcessors (Runtime/getRuntime))
       :output-hash (hash (mapv :hash rows))
       :statistics (into {} (map (fn [k] [k (distribution (map k rows))]))
                         [:wall-ms :cpu-ms :allocated-bytes])})))

(defn -main [fixture output warmup frames]
  (let [warmup (parse-long warmup)
        frames (parse-long frames)]
    (when-not (and (nat-int? warmup) (pos-int? frames))
      (throw (ex-info "Supply FIXTURE.edn OUTPUT.edn WARMUP FRAMES" {})))
    (let [report (measure (edn/read-string (slurp fixture)) warmup frames)]
      (spit output (pr-str report))
      (prn report))))
