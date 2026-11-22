(ns afterglow.render.native-compute-test
  (:require [afterglow.render.compute :as compute]
            [afterglow.render.frame :as frame]
            [afterglow.render.gpu.movement :as movement]
            [afterglow.render.gpu.session :as session]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]])
  (:import [java.util.concurrent CompletableFuture]))

(def fixture {:id :spot :universe 0 :address 1 :position [0.5 0 0]
              :channels {:pan [1 2] :tilt [3 4] :focus [5 6]}})
(def patch (frame/compile-patch [fixture]))
(def expressions {:focus {:op :position :axis :x}
                  :direction {:op :vec3 :args [{:op :param :key :x} {:op :const :value 0.25} {:op :const :value 1.0}]}})
(defn- blocks [x]
  (let [group (compute/prepare-group expressions [[0.5 0 0]] (ir/compile-batch expressions))]
    [{:kind :assignments :source :low
      :assignments [{:target-id :spot :attribute :direction :value [0.2 0.1 0.5]}]}
     {:kind :batch :source :high
      :batch {:target-ids [:spot] :opacity 0.5 :field-request {:group group :env {:params {:x x}}}}}]))

(deftest render-owner-produces-and-retires-real-native-expression-and-movement-output
  (let [layers (blocks 0.75)
        owner (compute/open! {:compute-backend :native-gpu :movement-backend :native-gpu :budget-ms 5000})]
    (try
      (is (compute/expressions-enabled? owner))
      (let [render (compute/frame-renderer owner (System/nanoTime))
            cpu ((compute/frame-renderer nil (System/nanoTime)) patch layers {})
            native (render patch layers {})
            retried (render patch layers {})
            pack-word (fn [out i] (let [^bytes universe (get-in out [:universes 0])]
                                    (+ (* 256 (bit-and 255 (aget universe i)))
                                       (bit-and 255 (aget universe (inc i))))))]
        (is (= (frame/portable-frame native) (frame/portable-frame retried)))
        (is (= {:requested :native-gpu :backend :native-gpu :gpu-heads 1 :cpu-heads 0}
               (compute/movement-status owner native)))
        (is (= 1 (:native-dispatches (compute/status owner))) "Retries reuse this frame's healthy fields")
        (is (= 0 (:cpu-fallbacks (compute/status owner))))
        (is (= (pack-word cpu 4) (pack-word native 4)))
        (doseq [i [0 2]] (is (<= (abs (- (pack-word cpu i) (pack-word native i))) 1)))
        (doseq [axis [:pan :tilt]]
          (is (< (abs (- (get-in cpu [:values :spot axis]) (get-in native [:values :spot axis]))) 1.0e-5))))
      (finally (compute/close! owner)))
    (is (false? (compute/expressions-enabled? owner)))
    (is (= :stopped (:active (compute/status owner))))
    (is (true? (get-in (compute/status owner) [:session :closed?])))))

(deftest timed-out-fields-and-physical-movement-share-one-deadline
  (let [layers (blocks 0.75)
        owner (compute/open! {:compute-backend :native-gpu :movement-backend :native-gpu :budget-ms 100})
        draws (atom 0)
        delayed (CompletableFuture.)]
    (try
      (with-redefs [session/submit! (fn [& _] (swap! draws inc) delayed)]
        (let [render (compute/frame-renderer owner (System/nanoTime))
              output (render patch layers {})
              retry (render patch layers {})
              reference ((compute/frame-renderer nil (System/nanoTime)) patch layers {})]
          (is (.isCancelled delayed))
          (is (= 1 @draws))
          (is (= 1 (:deadline-fallbacks (compute/status owner))))
          (is (= :timeout (:reason (compute/movement-status owner output))))
          (is (= (frame/portable-frame reference) (frame/portable-frame output) (frame/portable-frame retry)))))
      (finally (compute/close! owner)))))

(deftest acquisition-and-runtime-failure-preserve-the-reference-path
  (let [layers (blocks 0.66)
        reference ((compute/frame-renderer nil (System/nanoTime)) patch layers {})]
    (with-redefs [session/open! (fn [_] (throw (UnsatisfiedLinkError. "missing platform")))]
      (let [owner (compute/open! {:compute-backend :native-gpu :budget-ms 10001})]
        (try
          (is (false? (compute/expressions-enabled? owner)))
          (is (= :open (get-in (compute/status owner) [:last-fallback :stage])))
          (is (= (frame/portable-frame reference)
                 (frame/portable-frame ((compute/frame-renderer owner (System/nanoTime)) patch layers {}))))
          (finally (compute/close! owner)))))
    (let [owner (compute/open! {:compute-backend :native-gpu :budget-ms 2000})]
      (try
        (session/close! (:session owner))
        (is (= (frame/portable-frame reference)
               (frame/portable-frame ((compute/frame-renderer owner (System/nanoTime)) patch layers {}))))
        (is (= :evaluate (get-in (compute/status owner) [:last-fallback :stage])))
        (is (false? (compute/expressions-enabled? owner)))
        (finally (compute/close! owner))))))

(deftest interruption-while-opening-expressions-retires-acquired-movement
  (let [open movement/open! captured (atom nil)]
    (with-redefs [movement/open! (fn [options] (reset! captured (open options)))
                  session/open! (fn [_] (throw (InterruptedException. "shutdown")))]
      (is (thrown? InterruptedException
                   (compute/open! {:compute-backend :native-gpu :movement-backend :native-gpu})))
      (let [blocks [{:kind :assignments :assignments [{:target-id :spot :attribute :direction :value [1 2 3]}]}]]
        (is (= :closed (:reason (:movement (movement/resolve-contributions! @captured patch blocks)))))))))

(deftest deferred-native-field-can-modify-the-prior-members-world-direction
  (let [[first-block second-block] (blocks 0.75)
        tag (fn [b member transforms]
              (assoc b :native-layer {:id :layer :member member :transforms transforms}))
        stream [(tag second-block 1 [{:attribute :direction
                                      :value {:op :add :args [{:op :previous :attribute :direction}
                                                               {:op :incoming :attribute :direction}]}}])
                (tag first-block 0 [])]
        owner (compute/open! {:compute-backend :native-gpu :movement-backend :native-gpu :budget-ms 5000})]
    (try
      (let [out ((compute/frame-renderer owner (System/nanoTime)) patch stream {})
            ref ((compute/frame-renderer nil (System/nanoTime)) patch stream {})
            direction (get-in out [:values :spot :direction])]
        (let [world [0.575 0.225 1.0]
              length (Math/sqrt (reduce + (map #(* % %) world)))]
          (is (every? #(< (abs %) 1.0e-8) (map - direction (map #(/ % length) world)))))
        (is (= direction (get-in ref [:values :spot :direction])))
        (is (= 1 (:native-dispatches (compute/status owner))))
        (is (= 1 (:gpu-heads (compute/movement-status owner out))))
        (is (< (abs (- (get-in ref [:values :spot :pan]) (get-in out [:values :spot :pan]))) 1.0e-5)))
      (finally (compute/close! owner)))))
