(ns afterglow.spatial.beam-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.spatial.beam :as beam]
            [afterglow.spatial.field :as field]
            [afterglow.spatial.geometry :as geo]
            [clojure.test :refer [deftest is testing]]))

(def lamp {:id :head :position [0 0 0] :direction [0 0 1] :beam-angle 20.0 :lens-radius-m 0.1
           :channels {:red 1 :green 2 :blue 3 :pan 4 :tilt 5} :universe 1 :address 1})
(def lit {:emitted-color [0.8 0.1 0] :intensity 1.0 :direction [0 0 1]})

(deftest custom-occluders-still-decide-visibility-for-prepared-volume-queries
  (let [volume {:shape :sphere :position [0 0 3] :radius 0.2 :selection #{:beam}}
        sampling (field/prepare volume)
        options (beam/prepare-options {:surfaces [{:id :floor :point [0 -1 0] :normal [0 1 0]}]})
        for-volume #(beam/volume-options % #{:beam} sampling)
        weight #(get (beam/contribution lamp lit volume sampling %) :weight)
        override #(assoc % :occluded? (constantly true))]
    (is (= 0.8 (weight (for-volume options))))
    (is (nil? (weight (for-volume (override options)))))
    (is (nil? (weight (override (for-volume options)))))))

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

(defn- tiny-union [spheres]
  (let [corners (fn [sign] (map #(mapv (fn [axis] (+ axis (* sign (:radius %)))) (:position %)) spheres))
        bounds {:min (apply mapv min (corners -1)) :max (apply mapv max (corners 1))}
        volume {:shape :union :parts spheres}]
    [volume {:bounds bounds :center (mapv #(* 0.5 (+ %1 %2)) (:min bounds) (:max bounds))
             :weight-at #(if (geo/inside? volume %) 1.0 0.0)}]))

(defn- hits-small-sphere [lamp center radius opts]
  (let [[volume sampling] (tiny-union [{:shape :sphere :position center :radius radius}
                                        {:shape :sphere :position [10 11 12] :radius 0.02}])]
    (beam/contribution lamp lit volume sampling opts)))

(deftest a-small-off-axis-island-survives-union-with-a-distant-island
  (is (= {:weight 0.8} (hits-small-sphere lamp [0.71 0.28 5.17] 0.025 {})))
  (is (nil? (hits-small-sphere lamp [2.1 1.1 4.17] 0.025 {}))))

(deftest a-sphere-can-graze-a-cone-with-its-centre-outside
  (let [source (assoc lamp :beam-angle 90 :lens-radius-m 0.1)
        normal (/ 1.0 (Math/sqrt 2))
        center (fn [gap] [(+ 3.1 (* normal gap)) 0.0 (- 3.0 (* normal gap))])]
    (is (= {:weight 0.8} (hits-small-sphere source (center 0.25) 0.25 {:range-m 8})))
    (is (nil? (hits-small-sphere source (center 0.251) 0.25 {:range-m 8})))
    (is (nil? (hits-small-sphere source (center 0.25) 0.25 {:range-m 2})))))

(deftest finite-optical-reach-clips-the-off-axis-cap-at-the-end-of-each-ray
  (let [range-m 4.0, theta 0.4, lens 0.1
        source (assoc lamp :beam-angle 90 :lens-radius-m lens)
        cap-z (* range-m (Math/cos theta))
        cap-r (+ (* range-m (Math/sin theta)) (* lens (Math/tan theta)))
        radial-normal (* range-m (Math/sin theta))
        axial-normal (+ cap-z (/ lens (Math/pow (Math/cos theta) 2)))
        length (Math/hypot radial-normal axial-normal)
        center (fn [gap] [(+ cap-r (* gap (/ radial-normal length))) 0.0
                          (+ cap-z (* gap (/ axial-normal length)))])]
    (is (= {:weight 0.8} (hits-small-sphere source (center 0.125) 0.125 {:range-m range-m})))
    (is (nil? (hits-small-sphere source (center 0.126) 0.125 {:range-m range-m})))))

(deftest prepared-world-witnesses-include-scaled-translated-body-geometry
  (let [local {:shape :ball :position [0.35 0.28 5.17]
               :geometry {:shape :sphere :position [0.20 0 0] :radius 0.025}}
        scaled-world {:shape :sphere :position [0.75 0.28 5.17] :radius 0.05}
        sampling {:center [4 2 5] :bounds {:min [-2 -1 3] :max [10 8 12]}
                  :weight-at #(if (geo/inside? scaled-world %) 1.0 0.0)
                  :witnesses [{:center (:position scaled-world) :radius (:radius scaled-world)}]}]
    (is (= {:weight 0.8} (beam/contribution lamp lit local sampling {})))
    (is (nil? (beam/contribution lamp lit local (assoc sampling :weight-at (constantly 0.0)) {}))
        "The complete field can subtract an island even when a witness falls inside the cone")))

(deftest shape-witness-work-is-bounded
  (let [counted (atom 0)
        seeds (repeatedly #(do (swap! counted inc) {:center [0.5 0.5 5] :radius 0.01}))]
    (is (nil? (beam/contribution lamp lit {:shape :union}
                                {:witnesses seeds :weight-at (constantly 0.0)} {})))
    (is (<= 1 @counted 64))))

(deftest a-sphere-may-touch-only-the-lens-or-the-moving-heads-range-limit
  (is (= {:weight 0.8} (hits-small-sphere lamp [0.05 0 -0.25] 0.25 {})))
  (is (nil? (hits-small-sphere lamp [0.05 0 -0.251] 0.25 {})))
  (let [result (hits-small-sphere lamp [5.0625 0 0] 0.125 {:selection #{:aimable} :range-m 5})]
    (is (= 1.0 (:weight result)))
    (is (<= 4.9375 (first (:aim result)) 5.0))))

(deftest finite-segments-trace-the-open-space-between-emitter-and-volume
  (let [surface {:id :panel :point [0 0 2] :normal [0 0 -1] :u-axis [1 0 0] :size [1 1]}
        options {:selection #{:beam} :surfaces [surface]}]
    (is (some? (at lamp lit [0 0 1] options)))
    (is (some? (at lamp lit [0 0 2] options)))
    (is (nil? (at lamp lit [0 0 3] options)))
    (is (some? (at (assoc lamp :position [0 0 2]) lit [0 0 3] options)))
    (is (some? (at (assoc lamp :position [1 0 0]) lit [1 0 4] options)))))
