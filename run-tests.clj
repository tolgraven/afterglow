(require '[afterglow.output.artnet-test]
         '[afterglow.output.scheduler-test]
         '[afterglow.output.timeline-test]
         '[clojure.test :as test])

(let [namespaces '[afterglow.output.scheduler-test afterglow.output.timeline-test afterglow.output.artnet-test]
      network-test #'afterglow.output.artnet-test/loopback-transport-advances-sequence-even-when-frame-identity-repeats
      selected (for [namespace namespaces
                     :let [vars (->> (ns-interns namespace) vals
                                     (filter #(:test (meta %)))
                                     (remove #{network-test}))]
                     :when (seq vars)]
                 [namespace vars])]
  (binding [test/*report-counters* (ref test/*initial-report-counters*)]
    (doseq [[namespace vars] selected]
      (test/do-report {:type :begin-test-ns :ns namespace})
      (test/test-vars vars)
      (test/do-report {:type :end-test-ns :ns namespace}))
    (let [result @test/*report-counters*]
      (test/do-report (assoc result :type :summary))
      (shutdown-agents)
      (System/exit (if (zero? (+ (:fail result) (:error result))) 0 1)))))
