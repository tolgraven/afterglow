(ns afterglow.render.distributed-test
  (:require [afterglow.render.distributed :as distributed]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]])
  (:import [java.nio ByteBuffer ByteOrder]))

(def points (mapv #(vector (double %) 0.0 0.0) (range 7)))
(def expression {:dimmer {:op :position :axis :x}})
(defn group [] (distributed/prepare-group expression points (ir/compile-batch expression)))
(defn deadline [] (+ (System/nanoTime) 1000000000))
(defn result-bytes [xs]
  (let [data (byte-array (* 4 (count xs)))
        floats (.asFloatBuffer (.order (ByteBuffer/wrap data) ByteOrder/LITTLE_ENDIAN))]
    (doseq [x xs] (.put floats (float x)))
    data))

(defn peer [pool capacity]
  (let [sent (atom []) handle (promise)
        answer (fn [{:keys [job start count]}]
                 (distributed/receive! pool @handle {:op :result :job job
                                                      :values (result-bytes (range start (+ start count)))}))
        reply (atom answer)
        send! (fn [{:keys [op id] :as packet}]
                (swap! sent conj packet)
                (case op
                  :prepare (distributed/receive! pool @handle {:op :ready :id id})
                  :run (@reply packet)))]
    (deliver handle (distributed/connect! pool {:max-result-floats capacity} send!))
    {:id @handle :sent sent :reply reply :answer answer}))

(deftest retained-rig-shards-rejoin-in-physical-order
  (let [pool (distributed/create) field (group) a (peer pool 3) b (peer pool 4)
        run #(distributed/evaluate! pool field {} (deadline))]
    (try
      (is (nil? (run)) "Cold preparation never waits on a network connection")
      (is (= (mapv first points) (vec (get-in (run) [:outputs :dimmer :values]))))
      (is (= (mapv first points) (vec (get-in (run) [:outputs :dimmer :values]))))
      (doseq [peer [a b]]
        (is (= [:prepare :run :run] (mapv :op @(:sent peer)))))
      (is (= 2 (:completed (distributed/status pool))))
      (distributed/disconnect! pool (:id b))
      (is (nil? (run)) "One remaining worker cannot return the entire batch before the deadline")
      (finally (distributed/close! pool)))
    (is (thrown? Exception (distributed/connect! pool {:max-result-floats 8} identity)))))

(deftest late-wrong-and-invalid-replies-cannot-advance-a-different-frame
  (let [pool (distributed/create) field (group) p (peer pool 1024)
        run #(distributed/evaluate! pool field {} (deadline))]
    (try
      (is (nil? (run)))
      (reset! (:reply p) (constantly nil))
      (is (nil? (distributed/evaluate! pool field {} (+ (System/nanoTime) 5000000))))
      (is (= 1 (:busy (distributed/status pool))))
      (distributed/receive! pool (:id p) {:op :result :job "stale" :values (byte-array 28)})
      (is (nil? (run)))
      (is (= 2 (count @(:sent p))))
      ((:answer p) (last @(:sent p)))
      (reset! (:reply p) (:answer p))
      (is (= (mapv first points) (vec (get-in (run) [:outputs :dimmer :values]))))
      (reset! (:reply p) #(distributed/receive! pool (:id p) {:op :result :job (:job %) :values (byte-array 3)}))
      (is (nil? (run)))
      (is (= 1 (:rejected (distributed/status pool))))
      (finally (distributed/close! pool)))))
