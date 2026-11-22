(ns afterglow.effects.oscillators-test
  (:require [clojure.test :refer :all]
            [afterglow.effects.oscillators :as oscillator]
            [afterglow.rhythm :as rhythm]
            [afterglow.effects.params :as params]
            [afterglow.show-context :refer [with-show]]))

(defn- snapshot [phase]
  (rhythm/->MetronomeSnapshot 0 120 4 4 (* phase 500) 1 1 1 phase (/ phase 4) (/ phase 16)))

(defn- samples [osc phases]
  (mapv #(double (oscillator/evaluate osc {} (snapshot %) nil)) phases))

(deftest fixed-waveforms-use-the-supplied-snapshot
  (let [phases [0.0 0.25 0.5 0.75]]
    (is (= [0.0 0.25 0.5 0.75] (samples (oscillator/sawtooth) phases)))
    (is (= [1.0 0.75 0.5 0.25] (samples (oscillator/sawtooth :down? true) phases)))
    (is (= [0.0 0.5 1.0 0.5] (samples (oscillator/triangle) phases)))
    (is (= [1.0 1.0 0.0 0.0] (samples (oscillator/square) phases)))
    (is (= [1.0 0.0 0.0 0.0] (samples (oscillator/square :width 0.25) phases)))))

(deftest phase-and-interval-configuration-are-composable
  (is (= [0.25 0.5 0.75 0.0]
         (samples (oscillator/sawtooth :phase 0.25) [0.0 0.25 0.5 0.75])))
  (is (= [0.0 0.5 0.0 0.5]
         (samples (oscillator/sawtooth :interval-ratio 1/2) [0.0 0.25 0.5 0.75])))
  (is (= [0.0 0.0625 0.125 0.1875]
         (samples (oscillator/sawtooth :interval :bar) [0.0 0.25 0.5 0.75]))))

(deftest pulse-width-endpoints-and-validation
  (is (= [0.0 0.0] (samples (oscillator/square :width 0) [0.0 0.9])))
  (is (= [1.0 1.0] (samples (oscillator/square :width 1) [0.0 0.9])))
  (doseq [width [-0.1 1.1]]
    (is (thrown? IllegalArgumentException (oscillator/square :width width)))))

(deftest resolving-static-inputs-freezes-their-show-values
  (let [show {:variables (atom {:down true :width 0.25 :phase 0.25})}]
    (with-show show
      (let [static (fn [id type default] (params/build-variable-param id :type type :default default :frame-dynamic false))
            waves [(oscillator/sawtooth :down? (static :down Boolean false))
                   (oscillator/square :width (static :width Number 0.5))
                   (oscillator/sawtooth :phase (static :phase Number 0))]
            fixed (mapv #(oscillator/resolve-non-frame-dynamic-elements % show (snapshot 0.25) nil) waves)]
        (reset! (:variables show) {:down false :width 1.0 :phase 0.5})
        (is (= [0.75 0.0 0.5]
               (mapv #(oscillator/evaluate % show (snapshot 0.25) nil) fixed)))))))
