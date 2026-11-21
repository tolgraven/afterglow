(ns afterglow.render.native-gpu-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.native-gpu :as gpu]
            [clojure.test :refer [deftest is testing]]))

(def fixtures
  [{:id :back :position [3 1 0] :rotation-deg [0 90 0]
    :universe 1 :address 510 :channels {:pan [1 2] :tilt [3 4]}
    :calibration {:pan {:min-deg -270 :max-deg 270}}}
   {:id :strip :position [0 0 0] :universe 2 :address 10 :channels {:red 1}}
   {:id :wing :position [-1 0 0] :rotation-deg [180 42 15]
    :universe 0 :address 4 :channels {:pan [1 2] :tilt [3 4]}
    :calibration {:pan [125 -170] :tilt {:min-deg -45 :max-deg 55}}}])

(defn- cpu [patch targets options]
  (frame/resolve-frame patch
                       (mapv (fn [[id target]] {:target-id id :attribute :aim :value target}) targets)
                       options))

(defn- assert-axes [expected actual]
  (doseq [[id values] actual]
    (is (= (get-in expected [id :aim-reachable?]) (:aim-reachable? values)) (str id))
    (doseq [axis [:pan :tilt]]
      ;; Transcendental GPU instructions are implementation-dependent.
      (is (< (abs (- (get-in expected [id axis]) (axis values))) 1.0e-5) (str id " " axis)))))

(deftest native-gl-solves-the-paired-shader-with-committed-cpu-history
  (let [patch (frame/compile-patch fixtures)
        reordered (frame/compile-patch (vec (reverse fixtures)))
        targets {:back [3 1 -1] :wing [2 -2 -3]}
        previous (frame/resolve-frame reordered [{:target-id :back :attribute :pan :value 0.0}]
                                      {:compact-values? true})
        histories [{} {:previous-values (:values previous)}
                   {:previous-compact (:compact previous)}
                   {:previous-values {:back {:pan 0.86}} :previous-compact (:compact previous)}]
        solver (gpu/open! patch)]
    (try
      (println "Native moving-head renderer" (select-keys (:resources solver) [:renderer :version]))
      (doseq [history histories]
        (let [expected (:values (cpu patch targets history)) actual (gpu/solve! solver targets history)]
          (is (= #{:back :wing} (set (keys actual))))
          (assert-axes expected actual)))
      (let [first-result (gpu/solve! solver targets)
            next-result (gpu/solve! solver targets (second histories))]
        (is (< 0.65 (get-in first-result [:back :pan]) 0.68))
        (is (< (get-in next-result [:back :pan]) 1.0e-5))
        (is (= first-result (gpu/solve! solver targets))))
      (testing "invalid inputs and zero vectors cannot affect a subsequent solve"
        (doseq [bad [(dissoc targets :wing) (assoc targets :extra [1 2 3])
                     (assoc targets :wing [0 ##Inf 1]) (assoc targets :wing [1.0e100 0 1])
                     (assoc targets :wing [-1 0 0])]]
          (is (thrown? clojure.lang.ExceptionInfo (gpu/solve! solver bad))))
        (is (thrown? clojure.lang.ExceptionInfo (gpu/solve! solver targets {:previous-values {:back {:pan -0.1}}})))
        (assert-axes (:values (cpu patch targets {})) (gpu/solve! solver targets)))
      (finally (.close solver)))
    (.close solver)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed" (gpu/solve! solver targets)))))

(deftest batched-moving-heads-follow-changing-targets-from-committed-cpu-frames
  (let [n 64
        patch (frame/compile-patch
               (mapv (fn [i]
                       {:id i :position [(- (mod i 8) 4) (+ 2.0 (mod i 3)) (- (quot i 8) 4)]
                        :rotation-deg [(if (odd? i) 180 0) (- (mod (* i 31) 340) 170) (mod i 27)]
                        :universe 0 :address (inc (* 4 i)) :channels {:pan [1 2] :tilt [3 4]}
                        :calibration {:pan {:min-deg -270 :max-deg 270} :tilt [120 150]}})
                     (range n)))]
    (with-open [solver (gpu/open! patch)]
      (loop [i 0 history {}]
        (when (< i 12)
          (let [targets (into {} (for [id (range n) :let [phase (+ (* id 0.37) (* i 0.19))]]
                                   [id [(* 4.8 (Math/sin phase)) (* 1.5 (Math/cos (* phase 0.9)))
                                        (* 3.5 (Math/cos (* phase 1.2)))]]))
                expected (cpu patch targets (assoc history :compact-values? true))
                actual (gpu/solve! solver targets history)]
            (is (= n (count actual)))
            (assert-axes (:values expected) actual)
            (recur (inc i) {:previous-compact (:compact expected)})))))))
