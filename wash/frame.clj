(require '[tolglow.perf.output-deadlines :as deadlines] '[tolglow.perf.admission-cost :as admission])
(let [model (:model (admission/workload 1024 128))
      result (#'deadlines/run-case :pixel-sculpture model 120 240 0)
      costs (vec (sort (for [{:keys [slot cost-ms]} (:renders result) :when (<= 121 slot 360)] cost-ms)))
      percentile (fn [p] (nth costs (dec (long (Math/ceil (* p (count costs)))))))
      stats (assoc (:summary result) :render-wall-p50-ms (percentile 0.5) :render-wall-p99-ms (percentile 0.99))]
  (spit (first *command-line-args*) (pr-str stats))
  (prn stats))
(shutdown-agents)
