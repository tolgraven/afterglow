(ns afterglow.effects.movement-test
  (:require [clojure.test :refer :all]
            [afterglow.effects.movement :as movement]
            [afterglow.transform :as transform])
  (:import [org.jogamp.java3d Transform3D]
           [org.jogamp.vecmath Vector3d]))

(def head {:rotation (Transform3D.) :pan-center 127.5 :pan-half-circle 85.0
           :tilt-center 127.5 :tilt-half-circle 85.0})

(defn direction [pan tilt]
  (let [v (Vector3d. 0 0 1)]
    (.transform (movement/current-rotation head pan tilt) v)
    v))

(deftest calibrated-half-circle-is-pi-not-half-pi
  (is (.epsilonEquals (Vector3d. 0 0 -1) (direction 212.5 127.5) 1.0e-9))
  (is (.epsilonEquals (Vector3d. 1 0 0) (direction 170.0 127.5) 1.0e-9))
  (is (.epsilonEquals (Vector3d. 0 -1 0) (direction 127.5 170.0) 1.0e-9)))

(deftest inverse-movement-agrees-with-forward-calibration
  (doseq [desired [(Vector3d. 0 0 1) (Vector3d. 1 0 0)
                   (Vector3d. 1 1 1) (Vector3d. -1 1 1)]]
    (let [[pan tilt] (transform/direction-to-dmx head desired nil)
          expected (Vector3d. desired)]
      (.normalize expected)
      (is (.epsilonEquals expected (direction pan tilt) 1.0e-8)))))
