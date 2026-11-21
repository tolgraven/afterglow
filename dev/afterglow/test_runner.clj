(ns afterglow.test-runner
  (:require [clojure.test :as test]))

(def suites
  {"pure" '[afterglow.core-test afterglow.runtime-test]
   "legacy" '[afterglow.core-test afterglow.runtime-test
               afterglow.channels-test afterglow.rhythm-test
               afterglow.effects-test afterglow.effects.color-test
               afterglow.effects.pipeline-test afterglow.effects.channel-test
               afterglow.effects.oscillators-test afterglow.show-test]})

(defn -main [& [suite & extra]]
  (let [namespaces (get suites (or suite "pure"))]
    (when (or (seq extra) (nil? namespaces))
      (binding [*out* *err*] (println "Usage: bin/test [pure|legacy]"))
      (System/exit 2))
    (let [status (try
                   (doseq [namespace namespaces] (require namespace))
                   (let [{:keys [fail error]} (apply test/run-tests namespaces)]
                     (if (zero? (+ fail error)) 0 1))
                   (catch Throwable error
                     (.printStackTrace error)
                     1)
                   (finally (shutdown-agents)))]
      (System/exit status))))
