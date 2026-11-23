(ns afterglow.render.native-chain-test
  (:require [afterglow.render.chain :as chain]
            [afterglow.render.compute :as compute]
            [afterglow.render.fields :as fields]
            [afterglow.render.frame :as frame]
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

(defn- field-request [source field expression params]
  (let [outputs {field expression}
        positions [[0.25 1 0] [0.75 0 0]]
        group (compute/prepare-group outputs positions (ir/compile-batch outputs) [[0.5 0.25] nil])]
    {:kind :batch :source source
     :batch {:target-ids [:left :right] :field-request {:group group :env {:params params}}}}))

(deftest native-frame-restores-covered-material-on-fade-and-attributes-bad-input
  (let [old (field-request :material :focus {:op :multiply :args [{:op :surface-uv :axis :u}
                                                                   {:op :param :key :scale}]}
                           {:scale 1.0})
        mask (assoc (field-request :paint :color {:op :const :value [0.0 0.5 1.0]} {})
                    :native-layer {:id :paint :member 0 :target-weights {:left 0.25 :right 0.5}})
        cover (field-request :wash :focus {:op :const :value 0.25} {})
        patch (frame/compile-patch
               (mapv (fn [id address] {:id id :address address :universe 1
                                       :channels {:focus 1 :red 2 :green 3 :blue 4}})
                     [:left :right] [1 5]))
        owner (compute/open! {:compute-backend :native-gpu :budget-ms 5000})
        render (fn [owner blocks]
                 (frame/portable-frame ((compute/frame-renderer owner (System/nanoTime)) patch blocks {})))]
    (try
      (doseq [[blocks submissions] [[[old mask cover] 2]
                                    [[old mask (assoc-in cover [:batch :opacity] 0.5)] 3]
                                    [[old mask] 2]]]
        (let [before (:native-dispatches (compute/status owner))]
          (is (= (render nil blocks) (render owner blocks)))
          (is (= submissions (- (:native-dispatches (compute/status owner)) before)))))
      (let [invalid (assoc-in old [:batch :field-request :env :params :scale] 4.0)
            error (try (render owner [invalid mask cover]) nil (catch Exception e e))]
        (is (= :material (:effect-source (ex-data error)))))
      (is (zero? (:cpu-fallbacks (compute/status owner))))
      (finally (compute/close! owner)))))
