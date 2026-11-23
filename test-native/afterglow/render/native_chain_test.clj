(ns afterglow.render.native-chain-test
  (:require [afterglow.render.chain :as chain]
            [afterglow.render.compute :as compute]
            [afterglow.render.fields :as fields]
            [afterglow.render.gpu.session :as session]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]]))


(deftest desktop-transform-feedback-reads-the-composited-native-fields-in-one-draw
  (let [positions [[0.2 0 0] [0.8 0 0]], cache (chain/create-cache)
        layer (fn [rgb blend alpha]
                (let [outputs {:color {:op :param :key :tint :type :vec3} :focus {:op :position :axis :x}}
                      group (compute/prepare-group outputs positions (ir/compile-batch outputs))]
                  {:kind :batch :batch {:target-ids [:a :b] :blend blend :opacity alpha
                                        :field-request {:group group :env {:params {:tint rgb}}}}}))
        base (layer [0.125 0.25 0.5] :replace 1)
        highest (layer [0.25 0.5 0.75] :max 0.5)
        ;; Sixteen preceding full replacements are dead once the base arrives.
        stages (into (vec (repeat 16 (layer [0.1 0.2 0.3] :replace 1))) [base highest])
        fused (chain/fuse cache compute/prepare-group stages)]
    (is (= 1 (count fused)))
    (with-open [owner (session/open!)]
      (let [result ((fields/frame-evaluator (fn [group env] (session/evaluate! owner (:shader group) env))) fused)
            output (get-in result [0 :batch :outputs])]
        (is (= [0.1875 0.375 0.625 0.1875 0.375 0.625] (vec (get-in output [:color :values]))))
        (is (every? #(< (abs %) 1.0e-6) (map - (get-in output [:focus :values]) [0.2 0.8])))
        (is (= 1 (:draws (session/status owner))))
        (is (= 1 (:resident (session/status owner))))))))
