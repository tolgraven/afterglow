(ns afterglow.render.emission-test
  (:require [afterglow.render.emission :as emission]
            [afterglow.render.frame :as frame]
            [clojure.test :refer [deftest is]]))

(def fixtures
  [{:id :head :channels {:red 1 :white 2 :dimmer {:offset 3 :fine-offset 4 :inverted-from 33.75}
                         :strobe 5 :pan 6 :shutter 7} :universe 0 :address 510}
   {:id :strip :channels {:red 1 :blue 2} :universe 1 :address 8}
   {:id :fog :channels {:dimmer 1 :fog 2} :universe 2 :address 1}
   {:id :spot :channels {:dimmer 1} :emission-color [0.5 1 0.5] :universe 2 :address 4}])
(def patch (frame/compile-patch fixtures))
(defn head [id] (get-in patch [:by-id id]))
(defn row [id a v] {:target-id id :attribute a :value v})
(def rows [(row :head :red 0.7) (row :head :white 0.1) (row :head :dimmer 0.8)
           (row :head :pan 0.4) (row :head :strobe 0.9) (row :head :shutter 0.25)
           (row :strip :red 0.7) (row :strip :blue 0.3) (row :spot :dimmer 1)
           (row :fog :dimmer 1) (row :fog :fog 0.35)])
(defn near? [a b] (< (abs (- a b)) 0.005))
(defn freeze [f] (update-vals (:universes f) vec))

(deftest scaled-output-meets-budget-without-changing-other-channels
  (doseq [compact? [false true]]
    (let [source (frame/resolve-frame patch rows {:master 0.65 :include-values? (not compact?) :compact-values? compact?})
          bytes (freeze source)
          request {:head 0.4 :strip 0.6 :spot 0.2 :fog 0.0}
          out (emission/scale-emission patch source request)
          rgb (:red (emission/emitted-levels (head :head) out))
          view (if compact? (first (frame/project-compact (:compact out))) (get-in out [:values :head]))]
      (is (= bytes (freeze source)))
      (is (identical? source (emission/scale-emission patch source {:head 1.0})))
      (is (nil? (emission/levels (head :fog) out)))
      (doseq [id [:head :strip :spot]
              [attr before] (emission/emitted-levels (head id) source)]
        (let [after (get (emission/emitted-levels (head id) out) attr)]
          (is (<= after (* before (request id))))
          (is (near? after (* before (request id))))))
      (is (near? (:intensity view) (:dimmer (emission/levels (head :head) out))))
      (is (near? (first (:emitted-color view)) (+ rgb (:white (emission/emitted-levels (head :head) out)))))
      (is (= (subvec (get bytes 1) 1 4) (subvec (get (freeze out) 1) 1 4)))
      (is (= (subvec (get bytes 2) 0 2) (subvec (get (freeze out) 2) 0 2))))))

(deftest colored-release-survives-a-dark-input-frame
  (let [idle (frame/resolve-frame patch [] {:include-values? false :compact-values? true})
        before (frame/project-compact (:compact idle))
        release (emission/with-emitted-levels patch idle {:head {:red 0.2 :white 0.0}})
        view (first (frame/project-compact (:compact release)))]
    (is (near? 0.2 (:red (emission/emitted-levels (head :head) release))))
    (is (near? 0.2 (first (:emitted-color view))))
    (is (= before (frame/project-compact (:compact idle))))
    (is (thrown? Exception (emission/with-emitted-levels patch idle {:head {:pan 0.5}})))))

(deftest fractional-inversions-never-exceed-the-accepted-budget
  (doseq [pivot [nil 0 0.2 63.25 254.8] fine [nil 2]]
    (let [p (frame/compile-patch [{:id :lamp :channels {:dimmer (cond-> {:offset 1}
                                                                fine (assoc :fine-offset fine)
                                                                pivot (assoc :inverted-from pivot))}
                                   :address 512 :universe 1}])
          f (get-in p [:by-id :lamp])
          maximum (frame/resolve-frame p [(row :lamp :dimmer 1.0)] {})
          full (:dimmer (emission/levels f maximum))]
      (doseq [gain (map #(/ % 135.0) (range 136))]
        (let [out (emission/scale-emission p maximum {:lamp gain})
              delivered (:dimmer (emission/levels f out))]
          (is (<= 0.0 delivered (* full gain)))
          (is (< (- (* full gain) delivered) (/ 1.01 (if fine 65025.0 255.0)))))))))
