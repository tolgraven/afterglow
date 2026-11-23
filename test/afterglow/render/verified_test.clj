(ns afterglow.render.verified-test
  (:require [afterglow.render.distributed :as pool]
            [afterglow.render.distributed-test :as rt]
            [afterglow.render.ir :as ir]
            [afterglow.render.verified :as verified]
            [clojure.test :refer [deftest is]]))

(deftest guest-never-writes-an-unchecked-channel
  (let [owner (pool/create) handle (promise) sampled (atom 0.2)
        fields {:focus {:op :const :value 0.2}} g (pool/prepare-group fields rt/points (ir/compile-batch fields))
        send! (fn [{:keys [op id job count]}]
                (case op
                  :prepare (pool/receive! owner @handle {:op :ready :id id})
                  :run (pool/receive! owner @handle {:op :result :job job
                                                    :values (rt/result-bytes (concat (repeat (dec count) 0.2) [@sampled]))})))
        render #(pool/evaluate! owner g {} (rt/deadline))]
    (try
      (deliver handle (pool/connect! owner {:max-result-floats 100 :verification :full} send!))
      (is (nil? (render)))
      (is (= (vec (repeat 7 0.2)) (vec (get-in (render) [:outputs :focus :values]))))
      (reset! sampled 0.200002)
      (is (= 0.2 (last (get-in (render) [:outputs :focus :values]))) "Local double wins within tolerance")
      (reset! sampled 0.4)
      (is (nil? (render)) "Even a single wrong component at the end discards the full frame")
      (is (= 1 (:rejected (pool/status owner))))
      (is (not (pool/connected? owner @handle)))
      (finally (pool/close! owner)))))

(deftest independent-guests-repeat-the-same-slice-and-a-disagreement-drops-the-entire-batch
  (let [owner (pool/create) g (rt/group) observed (atom []) delta (atom 0.0)
        connect (fn [id]
                  (let [handle (promise)]
                    (deliver handle
                      (pool/connect! owner {:max-result-floats 7 :verification :redundant :subject id}
                        (fn [{:keys [op job start count] program :id}]
                          (case op
                            :prepare (pool/receive! owner @handle {:op :ready :id program})
                            :run (do (swap! observed conj [id start count])
                                     (pool/receive! owner @handle
                                       {:op :result :job job :values (rt/result-bytes
                                         (map #(+ % (if (= id "b") @delta 0.0)) (range start (+ start count))))}))))))
                    @handle))
        a (connect "a") b (connect "b")
        run #(pool/evaluate! owner g {} (rt/deadline))]
    (try
      (is (nil? (run)))
      (is (= (mapv first rt/points) (vec (get-in (run) [:outputs :dimmer :values]))))
      (is (= #{["a" 0 7] ["b" 0 7]} (set @observed)))
      (reset! delta 0.1)
      (is (nil? (run)))
      (is (pool/connected? owner a))
      (is (not (pool/connected? owner b)))
      (is (= (mapv first rt/points) (vec (get-in (run) [:outputs :dimmer :values]))) "Single remaining peer uses full verification")
      (finally (pool/close! owner)))))


(deftest equal-witnesses-are-still-checked-against-unpredictable-cpu-rows
  (let [group (rt/group) job {:start 2 :count 4}
        actual (rt/result-bytes [2 3 4 5]) colluding (rt/result-bytes [2 3 4 6])]
    (is (verified/agree? group {} job actual actual))
    (is (not (verified/agree? group {} job colluding colluding)))
    (is (not (verified/agree? group {} job actual colluding)))))
