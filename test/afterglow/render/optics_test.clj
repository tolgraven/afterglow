(ns afterglow.render.optics-test
  (:require [afterglow.render.optics :as optics]
            [clojure.test :refer [deftest is testing]]))

(def floor {:id :floor :point [0 0 0] :normal [0 1 0]})
(def source {:position [0 5 0] :direction [0 -1 0] :beam-angle 30})
(defn- near? [a b] (< (abs (- a b)) 1.0e-8))
(defn- dot [a b] (reduce + (map * a b)))
(defn- distance [a b] (let [v (mapv - a b)] (Math/sqrt (dot v v))))
(defn- at-edge? [{:keys [center major-axis minor-axis major-radius-m minor-radius-m]} p]
  (let [delta (mapv - p center)
        u (/ (dot delta major-axis) major-radius-m)
        v (/ (dot delta minor-axis) minor-radius-m)]
    (near? 1.0 (+ (* u u) (* v v)))))

(deftest fixture-angles-and-committed-direction
  (let [fixture {:beam-angle 18 :position [0 4 0]}
        output {:zoom 0.5 :pose {:direction [0 -1 0]} :direction [1 0 0]}]
    (is (= 18 (:beam-angle (optics/fixture-beam fixture output))))
    (is (near? 35 (:beam-angle (optics/fixture-beam (assoc fixture :zoom-range-deg [10 60]) output))))
    (is (near? 29 (:beam-angle (optics/fixture-beam {} output))))
    (is (= [0 -1 0] (:direction (optics/fixture-beam fixture output))))
    (is (near? 0.119 (:lens-radius-m (optics/fixture-beam fixture output))))))

(deftest footprint-circle-oblique-and-finite-aperture
  (doseq [r [0.0 0.119 0.25]]
    (let [beam (assoc source :lens-radius-m r)
          spot (optics/beam-footprint beam floor)]
      (is (near? 5 (:distance-m spot)))
      (is (= [0.0 0.0 0.0] (:hit spot) (:center spot)))
      (is (near? (+ r (* 5 (Math/tan (/ Math/PI 12)))) (:major-radius-m spot)))
      (is (near? (:major-radius-m spot) (:minor-radius-m spot)))
      (is (false? (:clipped? spot)))))
  (let [beam (assoc source :direction [1 -1 0])
        spot (optics/beam-footprint beam floor)]
    (is (< (:minor-radius-m spot) (:major-radius-m spot)))
    (is (< (first (:hit spot)) (first (:center spot))))
    (doseq [angle [30.0 60.0]]
      (is (at-edge? spot [(* 5 (Math/tan (Math/toRadians angle))) 0.0 0.0])))
    (is (near? 0 (distance (:hit spot) [5 0 0]))))
  (let [tilted {:id :slope :point [0 1 0] :normal [1 1 1] :u-axis [1 -1 0]}
        beam (assoc source :direction [0 -1 0])
        spot (optics/beam-footprint beam tilted)]
    (is (< (abs (dot (:normal tilted) (mapv - (:center spot) (:point tilted)))) 1.0e-8))
    (is (near? 0 (distance (:hit spot) [0 1 0])))
    (is (near? 0 (dot (:normal tilted) (:major-axis spot))))))

(deftest missed-clipped-and-nearest-receivers
  (let [other (assoc floor :id :near :point [0 2 0])]
    (is (= :near (:surface-id (optics/nearest-footprint source [floor other]))))
    (is (= :other (:surface-id (optics/nearest-footprint source [(assoc floor :id :other) floor]))))
    (is (:clipped? (optics/beam-footprint source (assoc floor :size [1 10]))))
    (is (nil? (optics/beam-footprint source (assoc floor :point [3 0 0] :size [1 1]))))
    (is (nil? (optics/beam-footprint source (assoc floor :point [0 10 0]))))
    (is (nil? (optics/beam-footprint (assoc source :direction [1 0 0]) floor)))
    (is (nil? (optics/beam-footprint (assoc source :direction [1 -0.05 0]) floor)))
    ;; The near grazing receiver occludes the farther bounded spot.
    (is (nil? (optics/nearest-footprint source [(assoc other :normal [1 0.01 0]) floor])))
    (doseq [bad [(assoc source :direction [0 0 0]) (assoc source :beam-angle 180)
                 (assoc source :position [0 ##NaN 0])]]
      (is (thrown? clojure.lang.ExceptionInfo (optics/beam-footprint bad floor))))
    (is (thrown? clojure.lang.ExceptionInfo (optics/beam-footprint source (assoc floor :u-axis [0 1 0]))))))

(deftest tangency-of-unlike-finite-apertures-on-an-oblique-plane
  (let [surface {:id :wall :point [1 0 2] :normal [0.2 1 0.4] :size [100 100]}
        leader (optics/beam-footprint (assoc source :direction [0.1 -1 0.2] :lens-radius-m 0.28) surface)
        follower {:position [3 4 -2] :beam-angle 21 :lens-radius-m 0.13}
        along [1 0 0]]
    (loop [previous leader step 0]
      (when (< step 3)
        (let [follower (assoc follower :position (mapv + (:center previous) [3 4 -2]))
              {:keys [aim direction contact footprint]} (optics/edge-aim previous follower surface along)]
          (is (some? footprint))
          (is (at-edge? previous contact))
          (is (at-edge? footprint contact))
          (is (pos? (dot (mapv - (:center footprint) (:center previous)) along)))
          (is (near? 0 (distance aim (:hit (optics/beam-footprint (assoc follower :direction direction) surface)))))
          ;; Both ellipses have the picked separating tangent at the exact contact.
          (doseq [[spot sign] [[previous -1] [footprint 1]]]
            (let [offset (mapv - contact (:center spot))
                  normal (:normal spot)
                  side (mapv - along (mapv #(* % (dot along normal)) normal))
                  p (dot (:major-axis spot) side)
                  q (dot (:minor-axis spot) side)
                  support (Math/hypot (* (:major-radius-m spot) p) (* (:minor-radius-m spot) q))]
              (is (near? support (* (- sign) (dot offset side))))))
          (recur footprint (inc step)))))
    (is (nil? (optics/edge-aim leader follower surface (:normal surface))))
    (is (nil? (optics/edge-aim (assoc leader :clipped? true) follower surface along)))
    (is (nil? (optics/edge-aim leader follower (assoc surface :size [0.1 0.1]) along)))))

(deftest overlap-distinguishes-crossing-ellipses-from-touching-or-separated-spots
  (let [spot {:surface-id :floor :center [0 0 0] :major-axis [1 0 0] :minor-axis [0 0 1]
              :major-radius-m 5 :minor-radius-m 0.2}
        parallel (fn [z] (assoc spot :center [0 0 z]))
        crossed (fn [x] (assoc spot :center [x 0 0] :major-axis [0 0 1] :minor-axis [-1 0 0]))]
    (is (optics/footprints-overlap? spot spot))
    (is (optics/footprints-overlap? spot (parallel 0.399)))
    (is (not (optics/footprints-overlap? spot (parallel 0.4))))
    (is (not (optics/footprints-overlap? spot (parallel 0.401))))
    (is (optics/footprints-overlap? spot (crossed 5.19)))
    (is (optics/footprints-overlap? (crossed 5.19) spot))
    (is (not (optics/footprints-overlap? spot (crossed 5.2))))
    (is (not (optics/footprints-overlap? spot (assoc spot :surface-id :other))))))
