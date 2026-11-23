(ns afterglow.spatial-field-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.spatial :as spatial]
            [afterglow.spatial.field :as field]))

(def fixtures
  [{:id :center :position [0 0 0]} {:id :rim :position [1 0 0]}
   {:id :spill :position [1.25 0 0]} {:id :outside :position [1.6 0 0]}])

(deftest continuous-light-field-retains-underlying-show-at-the-edge
  (let [volume {:shape :sphere :position [0 0 0] :radius 1 :strength 0.75
                :falloff {:inner-m 0.5 :outer-m 0.5 :curve :linear}}]
    (is (= {:center 0.75 :rim 0.375 :spill 0.1875}
           (:weights (field/positions volume (spatial/prepare-rig fixtures)))))
    (is (= {:center 1.0 :rim 1.0} (:weights (field/positions (dissoc volume :strength :falloff) fixtures))))
    (is (empty? (:weights (field/positions (assoc volume :selection #{:beam}) fixtures))))))

(def cube {:shape :rounded-box :position [0 0 0] :size [4 2 2] :rounding 0})
(def cut {:shape :sphere :radius 0.5 :position [0 0 0]})

(deftest sculpted-box-and-moving-boolean-fields
  (let [point (fn [v p] ((:weight-at (field/prepare v)) p))
        hollow {:shape :difference :parts [cube cut] :translation [3 1 0]}
        orb {:shape :ball :position [3 1 0] :radius 2 :geometry (assoc cube :rounding 1)}]
    (is (= 1.0 (point cube [1.9 0.9 0])))
    (is (zero? (point (assoc cube :rounding 1) [1.9 0.9 0])))
    (is (zero? (point hollow [3 1 0])))
    (is (= 1.0 (point hollow [4 1 0])))
    (is (zero? (point orb [4.9 1.9 0])))
    (is (= 1.0 (point orb [4 1 0])))
    (is (= {:min [1.0 0.0 -1.0] :max [5.0 2.0 1.0]} (:bounds (field/prepare orb))))
    (is (= 1.0 (point {:shape :intersection :parts [cube cut]} [0.1 0 0])))
    (is (= 0.0 (point {:shape :intersection :parts [cube cut]} [1 0 0])))
    (is (= 1.0 (point {:shape :union :parts [cube (assoc cut :position [3 0 0])]} [3 0 0])))))

(deftest throw-through-a-cutout-emits-contact-for-both-solid-pieces
  (let [body {:shape :ball :position [0 1 0] :velocity [1000 0 0] :radius 0.1
              :geometry {:shape :difference
                         :parts [{:shape :box :min [-1 -0.2 -0.2] :max [1 0.2 0.2]}
                                 {:shape :box :min [-0.3 -1 -1] :max [0.3 1 1]}]}}
        rig [{:id :pixel :position [2 1 0]}]
        scene (spatial/prepare {:bounds {:min [-10 0 -10] :max [10 5 10]}
                                :gravity [0 0 0] :volumes {:body body}})
        step (fn [prev t] (spatial/advance prev scene {:epoch 1 :time-ms t} rig {}))
        result (step (:state (step nil 0)) 5)]
    (is (= [:spatial/enter :spatial/exit :spatial/enter :spatial/exit]
           (mapv :type (:events result))))
    (is (every? #(< (abs %) 1.0e-8) (map - [1.0 1.7 2.3 3.0] (map :time-ms (:events result)))))
    (is (empty? (get-in result [:members :body])))))

(deftest stretch-keeps-the-centre-and-transforms-both-child-and-body
  (let [volume {:shape :sphere :position [1 2 3] :radius 1 :scale [3 1 0.5] :translation [1 0 0]}
        {:keys [weight-at bounds witnesses]} (field/prepare volume)]
    (is (= [5.0 3.0 3.5] (:max bounds)))
    (is (= [2.0 2.0 3.0] (:center (first witnesses))))
    (is (= 1.0 (weight-at [4.9 2 3])))
    (is (zero? (weight-at [2 2 3.6])))
    (is (thrown? clojure.lang.ExceptionInfo (field/prepare (assoc volume :scale [1 0 2]))))))

(deftest field-combines-live-beams-and-head-positions
  (let [spot {:id :spot :position [0 0 0] :direction [0 0 1] :beam-angle 12 :channels {:red 1}}
        pixel {:id :pixel :position [0 0 4]}
        volume {:shape :sphere :radius 0.25 :position [0 0 4] :selection #{:position :beam}}
        prior {:values {:spot {:emitted-color [0.6 0 0] :direction [0 0 1]}}}]
    (is (= {:pixel 1.0 :spot 0.6} (:weights (field/sample volume [spot pixel] prior))))
    (is (= {:pixel 1.0} (:weights (field/sample volume [spot pixel] (assoc prior :extinction-per-m 3.0)))))))
