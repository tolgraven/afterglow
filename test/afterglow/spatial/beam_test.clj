(ns afterglow.spatial.beam-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.spatial.beam :as beam]
            [afterglow.spatial.geometry :as geo]
            [clojure.test :refer [deftest is testing]]))

(def lamp {:id :head :position [0 0 0] :direction [0 0 1] :beam-angle 20.0 :lens-radius-m 0.1
           :channels {:red 1 :green 2 :blue 3 :pan 4 :tilt 5} :universe 1 :address 1})
(def lit {:emitted-color [0.8 0.1 0] :intensity 1.0 :direction [0 0 1]})

(defn- at [fixture output point options]
  (beam/contribution fixture output {:shape :sphere :position point :radius 0.0}
                     {:weight-at #(when (= % point) 0.75) :center point :bounds {:min point :max point}} options))

(deftest a-live-beam-has-finite-aperture-and-a-full-included-angle
  (doseq [point [[0.09 0 0.001] [0.9 0.0 5.0]]]
    (is (< (abs (- 0.6 (:weight (at lamp lit point {})))) 1.0e-9)))
  (doseq [point [[0.12 0 0.001] [1.1 0 5] [0 0 -1] [0 0 12]]]
    (is (nil? (at lamp lit point {:range-m 10.0}))))
  (is (nil? (at lamp (assoc lit :emitted-color [0 0 0]) [0 0 5] {})))
  (is (nil? (at lamp (assoc lit :shutter-open? false) [0 0 5] {})))
  (is (nil? (at lamp lit [0 0 5] {:intensity-threshold 0.9}))))

(deftest optical-selection-uses-each-points-path-through-air-and-the-venue
  (let [wall {:id :wall :point [0 0 2] :normal [0 0 1] :size [0.2 1]}
        blocked (beam/prepare-options {:surfaces [wall] :range-m 10})]
    (is (nil? (at lamp lit [0 0 4] blocked)))
    (is (at lamp lit [0.7 0 4] blocked) "Off-axis light passes beside the finite wall")
    (is (at lamp lit [0 0 2] blocked) "Light reaches the surface itself")
    (is (nil? (at lamp lit [0 0 4] {:extinction-per-m 1 :min-transmission 0.1})))
    (is (< (abs (- (* 0.6 (Math/exp -2)) (:weight (at lamp lit [0 0 2] {:extinction-per-m 1})))) 1.0e-9))))

(deftest aimable-selects-reachable-dark-heads-and-obeys-mounting-and-dmx-calibration
  (let [head (assoc lamp :rotation-deg [0 90 0] :calibration {:pan {:min-deg -20 :max-deg 20}
                                                              :tilt [128 510]})
        options {:selection #{:aimable} :range-m 8}
        aim [5.0 1.0 0.0]
        dark {:emitted-color [0 0 0]}]
    (is (= {:weight 0.75 :aim aim} (at head dark aim options)))
    (is (nil? (at head dark [0 0 5] options)))
    (is (nil? (at head dark [1 4 0] options)))
    (is (nil? (at head dark [0 0 0] options)))
    (is (nil? (at (update head :channels dissoc :pan) dark aim options)))
    (is (nil? (at head dark aim {})))
    (is (nil? (at head dark aim (assoc options :surfaces [{:id :wall :point [3 0 0] :normal [1 0 0]}]))))
    (let [resolved (frame/resolve-frame [head] [{:target-id :head :attribute :aim :value aim}])
          pose (frame/fixture-pose head (get-in resolved [:values :head]))]
      (is (get-in resolved [:values :head :aim-reachable?]))
      (is (pos? (first (:direction pose)))))
    (is (nil? (at head (assoc lit :pan 0.5 :tilt (/ 128 255.0)) [0 0 4] {}))
        "Committed pose takes precedence over a requested direction")))

(deftest volume-probes-cover-bounds-and-clip-a-ray-to-thin-polyhedra
  (let [box {:shape :box :min [0 -0.05 4] :max [2 0.05 4.1]}
        box-sample {:center [1 0 4.05] :bounds box :weight-at #(if (geo/inside? box %) 1 0)}
        planes [{:normal [0 0 -1] :distance -2.01} {:normal [0 0 1] :distance 2.02}]
        slab {:shape :polyhedron :planes planes}
        calls (atom 0)
        sample {:weight-at #(do (swap! calls inc) (if (geo/inside? slab %) 0.5 0))}]
    (is (beam/contribution lamp lit box box-sample {}))
    (is (= {:weight 0.4} (beam/contribution lamp lit slab sample {})))
    (is (<= @calls 27))))

(deftest a-bounded-volume-outside-the-optical-path-needs-no-weight-samples
  (let [samples (atom 0)
        bounds {:min [5 4 0] :max [6 5 1]}
        sampling {:bounds bounds :weight-at (fn [_] (swap! samples inc) 1)}]
    (is (nil? (beam/contribution lamp lit {:shape :box} sampling {})))
    (is (zero? @samples))))

(deftest weighted-aim-and-actual-light-coexist
  (let [point {:center [0 0 3] :weight-at (constantly 0.6)
               :bounds {:min [0 0 3] :max [0 0 3]}}]
    (is (= {:weight 0.6 :aim [0 0 3]}
           (beam/contribution lamp lit {} point {:selection #{:aimable :beam}})))))
