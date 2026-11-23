(ns afterglow.render.compute-test
  (:require [afterglow.render.compute :as compute]
            [afterglow.render.frame :as frame]
            [afterglow.render.fields :as fields]
            [afterglow.render.gpu.movement :as movement]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]]))

(def patch (frame/compile-patch [{:id :spot :universe 0 :address 1 :channels {:focus [1 2]}}]))
(def outputs {:focus {:op :position :axis :x}})

(deftest cpu-renderer-packs-ordinary-and-deferred-fields
  (let [owner (compute/open!)
        render (compute/frame-renderer owner (System/nanoTime))
        compiled (ir/compile-batch outputs)
        positions (double-array [0.123456789 0 0])
        group (compute/prepare-group outputs positions compiled)
        request {:kind :batch :source :sweep :batch {:target-ids [:spot] :field-request {:group group :env {}}}}
        assignments [{:kind :assignments :assignments [{:target-id :spot :attribute :focus :value 0.123456789}]}]
        reference (frame/portable-frame (frame/resolve-contributions patch assignments))]
    (aset-double positions 0 0.5)
    (let [evaluate-fields (fields/frame-evaluator (fn [& _] (throw (AssertionError. "ordinary block evaluated"))))]
      (is (identical? assignments (evaluate-fields assignments))))
    (is (false? (compute/expressions-enabled? owner)))
    (is (= {:requested :cpu :active :cpu} (compute/status owner)))
    (is (= {:requested :cpu :backend :cpu} (compute/movement-status owner nil)))
    (is (= reference (frame/portable-frame (render patch assignments {}))
           (frame/portable-frame (render patch [request] {}))))
    (compute/close! owner)))

(deftest prepared-chart-survives-mutation-and-cpu-fallback
  (let [output {:focus {:op :surface-uv :axis :u}}
        uvs (double-array [0.25 0.75])
        group (compute/prepare-group output [[0.7 0.6 1.0]] (ir/compile-batch output) uvs)
        request {:kind :batch :batch {:target-ids [:spot] :field-request {:group group :env {}}}}
        owner (compute/open!)]
    (try
      (aset-double uvs 0 0.9)
      (let [render (compute/frame-renderer owner (System/nanoTime))
            actual (render patch [request] {})
            expected (frame/resolve-frame patch [{:target-id :spot :attribute :focus :value 0.25}])]
        (is (= (frame/portable-frame expected) (frame/portable-frame actual))))
      (finally (compute/close! owner)))))

(deftest movement-owner-reports-intent-and-honors-the-frame-deadline
  (let [owner (compute/open! {:movement-backend :native-gpu :budget-ms 75})
        render (compute/frame-renderer owner (- (System/nanoTime) 200000000))
        patch (frame/compile-patch [{:id :spot :universe 0 :address 1 :channels {:pan [1 2] :tilt 3}}])
        layers [{:kind :assignments :source :aim :assignments [{:target-id :spot :attribute :aim :value [1 2 3]}]}]]
    (try
      (is (false? (compute/expressions-enabled? owner)))
      (is (= {:requested :native-gpu :backend :idle} (compute/movement-status owner nil)))
      (let [out (render patch layers {})]
        (is (= {:requested :native-gpu :backend :cpu :reason :timeout :cpu-heads 1 :gpu-heads 0}
               (compute/movement-status owner out)))
        (is (= (frame/portable-frame (frame/resolve-contributions patch layers)) (frame/portable-frame out))))
      (finally (compute/close! owner)))))

(deftest invalid-native-options-fail-before-resource-acquisition
  (doseq [options [{:compute-backend :unknown} {:movement-backend :other}
                   {:compute-backend :native-gpu :budget-ms 0} {:movement-backend :native-gpu :budget-ms 10001}
                   {:compute-backend :native-gpu :gpu-options {:queue-capacity -1}}
                   {:compute-backend :native-gpu :gpu-options {:timeout-ms 11000}}]]
    (is (thrown? clojure.lang.ExceptionInfo (compute/open! options)))))

(deftest moving-head-driver-teardown-honors-timed-close
  (let [owner (movement/open!) entered (promise) release (promise)
        solver (reify java.io.Closeable (close [_] (deliver entered true) @release))]
    ;; With no worker running, shutdown enters the termination hook on the caller.
    (vreset! (:resident owner) {:solver solver})
    (let [closing (future (movement/close! owner 5))]
      (try
        (is (= true (deref entered 3000 ::timeout)))
        (is (false? (deref closing 1000 ::timeout)))
        (finally (deliver release true))))
    (is (true? (movement/close! owner 3000)))
    (is (nil? @(:resident owner)))))
