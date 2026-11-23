(ns afterglow.qa.effect-blocks
  "Emit optical shaders and CPU reference values for the WebGL2 readback test."
  (:require [afterglow.render.blocks :as blocks]
            [afterglow.render.ir :as ir]
            [clojure.data.json :as json]
            [clojure.java.io :as io]))

(def positions [[0.2 0.75 -0.8] [0.2 0.75 1.7] [-0.4 0.1 0.3] [0.85 -0.65 0.7] [0.2 0.75 -0.8]])
(def surface-uvs [[0.14 0.22] [0.14 0.22] nil [0.87 0.95] [0.93 0.66]])
(def beats [0.0 0.5 2.25])

(defn- color-gel []
  (let [y {:op :position :axis :y}
        phase {:op :multiply :args [y {:op :const :value 2.8}]}
        band {:op :multiply :args [{:op :const :value 0.5}
                                   {:op :add :args [{:op :const :value 1.0}
                                                    {:op :sin :args [phase]}]}]}]
    {:block :optics/gel
     :inputs {:transmission {:op :mix :args [{:op :const :value [1.0 0.16 0.05]}
                                             {:op :const :value [0.05 0.68 0.97]} band]}}}))

(defn- fields [coordinates]
  (let [water {:block :optics/through-water :coordinates coordinates
               :inputs {:depth 0.96 :frequency 0.85 :rate 0.22}}
        fog {:block :optics/fog-transmission
             :inputs {:extinction 0.3 :density {:op :param :key :density} :distance 2.4}}
        field (fn [base & stages] (:expression (blocks/plan {:base base :stages (vec stages)})))]
    {:color (field [0.98 0.92 0.90] (assoc water :amount 0.82) (color-gel) fog)
     :dimmer (field 0.9 (assoc water :amount 0.72) fog)
     :focus (field 0.78 (assoc water :amount 0.65)
                   {:block :optics/ribbed-glass :coordinates coordinates :amount 0.5})}))

(defn- samples [expressions]
  (let [readers (update-vals expressions ir/compile-expression)]
    (vec (for [beat beats density [0.0 0.42]]
           {:beat beat :density density
            :values (mapv (fn [position uv]
                            (let [env {:position position :surface-uv uv :elapsed-beats beat :params {:density density}}]
                              (update-vals readers #(% env)))) positions surface-uvs)}))))

(defn- fixture [coordinates]
  (let [expressions (fields coordinates)]
    {:fragments (update-vals expressions #(ir/emit-glsl % coordinates))
     :batch (ir/emit-glsl-batch expressions {:surface-uv? true})
     :samples (samples expressions)}))

(defn -main [output]
  (with-open [writer (io/writer output)]
    (json/write {:positions positions :surface-uvs surface-uvs :world (fixture :world) :uv (fixture :surface-uv)}
                writer)))
