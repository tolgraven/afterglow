(require '[afterglow.render.ir :as ir] '[clojure.edn :as edn] '[clojure.java.io :as io])
(import '[java.io DataOutputStream])
(let [{:keys [outputs positions]} (edn/read-string (slurp (first *command-line-args*)))
      plan (ir/compile-batch outputs)]
  (with-open [out (DataOutputStream. (io/output-stream (second *command-line-args*)))]
    (.writeInt out (count positions))
    (doseq [position positions coordinate position] (.writeDouble out coordinate))
    (doseq [beat (range 0 33 2)]
      (let [^doubles values (get-in (ir/evaluate-batch plan {:elapsed-beats beat} positions) [:outputs :color :values])]
        (doseq [color values] (.writeDouble out color))))))
