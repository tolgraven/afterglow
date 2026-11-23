(ns afterglow.control.resolution-test
  (:require [afterglow.control.resolution :as resolution]
            [afterglow.control.parameter-edit :as edit]
            [afterglow.render.frame :as frame]
            [afterglow.render.frame-test :refer [assignment bytes-at]]
            [clojure.test :refer [deftest is]]))

(defn fixture [chans] {:id :light :address 1 :universe 1 :channels chans})
(def knob {:op :param :key :width})
(defn definition [attr] {:outputs {attr {:op :multiply :args [knob {:op :const :value 1.0}]}}})

(deftest direct-and-indirect-output-width-follows-patch-and-targets
  (let [coarse (fixture {:pan 1 :tilt 2 :dimmer 3})
        fine (assoc (fixture {:pan [1 2] :tilt [3 4] :dimmer [5 6]}) :id :fine)
        patch (resolution/patch-widths [coarse fine])]
    (is (= 16 (resolution/parameter-bits patch (definition :pan) :width)))
    (is (= 8 (resolution/parameter-bits patch (definition :pan) :width [:light])))
    (is (= 16 (resolution/parameter-bits patch (definition :dimmer) :width [:fine])))
    (is (= 16 (resolution/parameter-bits patch (definition :direction) :width)))
    (is (nil? (resolution/parameter-bits patch (definition :pan) :speed)))
    (is (= 8 (resolution/parameter-bits [(fixture {:red 1 :green 2 :blue 3})] (definition :dimmer) :width)))))

(deftest normalized-fine-tick-reaches-the-next-physical-code
  (doseq [attr [:pan :tilt :dimmer] bits [8 16]]
    (let [fixture (fixture {attr (if (= bits 8) 1 [1 2])})
          actual (resolution/parameter-bits [fixture] (definition attr) :width)
          max-code (if (= bits 8) 255.0 65535.0)
          start (if (= bits 8) 63 255)
          value (/ start max-code)
          schema {:type :number :bounds [0 0.9]}
          next-value (edit/edit schema value 1 {:fine? true :dmx-bits actual})
          encoded #(let [out (frame/resolve-frame [fixture] [(assignment :light attr %)])]
                     (if (= bits 8) (bytes-at out 1 1) (bytes-at out 1 1 2)))]
      (is (= bits actual))
      (is (= (if (= bits 8) [63] [0 255]) (encoded value)))
      (is (= (if (= bits 8) [64] [1 0]) (encoded next-value))))))

(deftest every-physical-fine-code-is-addressable-across-universes
  (let [buffers {1 (byte-array 512) 2 (byte-array 512)}
        channel {:coarse [1 511] :fine [2 0]}]
    (is (nil?
         (some (fn [code]
                 (frame/pack-value! buffers channel (/ code 65535.0))
                 (let [read-code (+ (* 256 (bit-and 255 (aget ^bytes (buffers 1) 511)))
                                    (bit-and 255 (aget ^bytes (buffers 2) 0)))]
                   (when-not (= code read-code) [code read-code])))
               (range 65536))))))
