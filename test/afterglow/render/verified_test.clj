(ns afterglow.render.verified-test
  (:require [afterglow.render.distributed :as pool]
            [afterglow.render.distributed-test :as rt]
            [afterglow.render.ir :as ir]
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
