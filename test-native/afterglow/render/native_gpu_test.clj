(ns afterglow.render.native-gpu-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.native-gpu :as gpu]
            [afterglow.render.gpu.movement :as movement]
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
                       (vec (for [[id input] targets
                                  [attribute value] (if (map? input) input {:aim input})]
                              {:target-id id :attribute attribute :value value}))
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
        unlit (frame/resolve-frame patch [])
        histories [{} {:previous-values (:values previous)}
                   {:previous-values (:values unlit)}
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
        (is (thrown? clojure.lang.ExceptionInfo (gpu/solve! solver targets {:previous-values []})))
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

(deftest one-native-draw-mixes-aims-and-world-directions
  (let [patch (frame/compile-patch fixtures)
        point {:back [3 1 -1] :wing {:aim [2 -2 -3]}}
        mixed (assoc point :back {:direction [0 0 -8]})
        both (assoc point :wing {:direction [1 7 0] :aim [2 -2 -3]})]
    (with-open [solver (gpu/open! patch)]
      (doseq [targets [mixed both point]]
        (let [actual (gpu/solve! solver targets)]
          (assert-axes (:values (cpu patch targets {})) actual)
          (is (= (gpu/solve! solver point) actual))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (gpu/solve! solver (assoc mixed :back {:direction [0 0 0]}))))
      (assert-axes (:values (cpu patch mixed {})) (gpu/solve! solver mixed)))))

(defn- movement-blocks [alpha]
  [{:kind :assignments :source :background
    :assignments [{:target-id :back :attribute :aim :value [1 4 2]}
                  {:target-id :wing :attribute :pan :value 0.25}
                  {:target-id :wing :attribute :tilt :value 0.75}
                  {:target-id :strip :attribute :red :value 0.75}]}
   {:kind :batch :source :sweep
    :batch {:target-ids [:back] :opacity alpha
            :outputs {:aim {:type :vec3 :components 3 :values (double-array [4 2 -1])}}}}
   {:kind :assignments :source :overlay
    :assignments [{:target-id :wing :attribute :direction :value [1 0 0] :opacity 0}
                  {:target-id :back :attribute :direction :value [0 1 0]}]}])

(defn- motor-word [frame fixture axis]
  (let [{:keys [coarse fine]} (get-in fixture [:compiled-channels axis])
        byte-at (fn [[universe offset]] (bit-and (aget ^bytes (get-in frame [:universes universe]) offset) 255))]
    (+ (* 256 (byte-at coarse)) (byte-at fine))))

(deftest published-frames-use-only-effective-selected-movement
  (let [patch (frame/compile-patch fixtures)
        reordered (frame/compile-patch (vec (reverse fixtures)))
        before (frame/resolve-frame reordered [{:target-id :back :attribute :pan :value 0.04}] {:compact-values? true})]
    (with-open [owner (movement/open! {:budget-ms 10000})]
      (doseq [rich? [true false] alpha [0.0 0.25 0.75 1.0]
              :let [options {:previous-compact (:compact before) :include-values? rich? :compact-values? true}
                    expected (frame/resolve-contributions patch (movement-blocks alpha) options)
                    actual (movement/resolve-contributions! owner patch (movement-blocks alpha) options)
                    ref (first (frame/project-compact (:compact expected)))
                    pose (first (frame/project-compact (:compact actual)))]]
        (is (= {:backend :native-gpu :gpu-heads 1 :cpu-heads 0} (:movement actual)))
        (is (= (:aim ref) (:aim pose)))
        (is (= (rest (frame/project-compact (:compact expected))) (rest (frame/project-compact (:compact actual)))))
        (is (= (vec (get-in expected [:universes 0])) (vec (get-in actual [:universes 0]))))
        (doseq [axis [:pan :tilt]]
          (is (< (abs (- (axis ref) (axis pose))) 1.0e-5))
          (is (<= (abs (- (motor-word expected (get-in patch [:by-id :back]) axis)
                           (motor-word actual (get-in patch [:by-id :back]) axis))) 1)))
        (when rich?
          (let [compare-attr (fn [attr] (abs (- (get-in expected [:values :back attr])
                                                 (get-in actual [:values :back attr]))))]
            (is (< (compare-attr :pan-deg) 0.001))
            (is (< (compare-attr :tilt-deg) 0.001))
            (is (= (get-in expected [:values :back :aim-reachable?])
                   (get-in actual [:values :back :aim-reachable?]))))))
      (testing "changed position and ordering replace the resident native mounts"
        (let [next-patch (frame/compile-patch (vec (reverse (assoc-in fixtures [0 :position] [5 2 1]))))
              options {:previous-compact (:compact before)}
              blocks (movement-blocks 0.25)
              actual (movement/resolve-contributions! owner next-patch blocks options)
              reference (frame/resolve-contributions next-patch blocks options)]
          (is (= :native-gpu (get-in actual [:movement :backend])))
          (assert-axes (:values reference) (select-keys (:values actual) [:back]))))
      (testing "the sparse solver leaves exact world coordinates and singulars to the CPU"
        (doseq [[assignment reason] [[{:attribute :aim :value [1/3 2 1]} :cpu-input]
                                     [{:attribute :direction :value [0 0 -1]} :ambiguous]]
                :let [blocks [{:kind :assignments :assignments [(assoc assignment :target-id :back)]}]
                      out (movement/resolve-contributions! owner patch blocks)
                      cpu (frame/resolve-contributions patch blocks)]]
          (is (= reason (get-in out [:movement :reason])))
          (is (= 0 (get-in out [:movement :gpu-heads])))
          (is (= (frame/portable-frame cpu) (frame/portable-frame out)))))
      (testing "bad authored geometry reaches the supervised source without contaminating later frames"
        (try
          (movement/resolve-contributions! owner patch [{:kind :assignments :source :broken
                                                         :assignments [{:target-id :back :attribute :aim
                                                                        :value [3 1 0]}]}])
          (is false "zero distance should fail")
          (catch clojure.lang.ExceptionInfo error (is (= :broken (:effect-source (ex-data error))))))
        (is (= :native-gpu (get-in (movement/resolve-contributions! owner patch (movement-blocks 0.25))
                                   [:movement :backend])))))))

(deftest late-draws-cannot-change-a-published-frame-or-enter-a-later-frame
  (let [patch (frame/compile-patch fixtures)
        blocks (movement-blocks 0.25)
        owner (movement/open! {:budget-ms 10000})
        started (promise) release (promise) finished (promise)
        actual-solve gpu/solve-selected!
        accepted (frame/resolve-frame patch [{:target-id :back :attribute :pan :value 0.15}]
                                      {:compact-values? true})]
    (try
      (is (= :native-gpu (get-in (movement/resolve-contributions! owner patch blocks) [:movement :backend])))
      (with-redefs [gpu/solve-selected! (fn [solver targets history]
                                         (deliver started true)
                                         (deref release 5000 nil)
                                         (try (actual-solve solver targets history)
                                              (finally (deliver finished history))))]
        (let [waiter (future (movement/resolve-contributions! owner patch blocks
                                                             {:previous-compact (:compact accepted)
                                                              :deadline-nanos (+ (System/nanoTime) 500000000)}))]
          (is (true? (deref started 2000 nil)))
          (let [out (deref waiter 2000 nil)
                expected (frame/resolve-contributions patch blocks {:previous-compact (:compact accepted)})
                snapshot (frame/portable-frame out)]
            (is (= :timeout (get-in out [:movement :reason])))
            (is (= (frame/portable-frame expected) snapshot))
            (is (= :busy (get-in (movement/resolve-contributions! owner patch (movement-blocks 0.75))
                                 [:movement :reason])))
            (aset ^doubles (get-in accepted [:compact :fields :pan :values]) 0 0.99)
            (deliver release true)
            (is (= {:previous-values {:back {:pan 0.15}}} (deref finished 5000 nil)))
            (is (= snapshot (frame/portable-frame out))))))
      (let [next-patch (frame/compile-patch (vec (reverse fixtures)))
            next-blocks (movement-blocks 1.0)
            out (movement/resolve-contributions! owner next-patch next-blocks)]
        (is (= :native-gpu (get-in out [:movement :backend])))
        (assert-axes (:values (frame/resolve-contributions next-patch next-blocks))
                     (select-keys (:values out) [:back])))
      (finally (deliver release true) (movement/close! owner)))
    (is (= :closed (get-in (movement/resolve-contributions! owner patch blocks) [:movement :reason])))))

(deftest missing-native-context-and-expired-budget-use-pure-output
  (let [patch (frame/compile-patch fixtures)
        blocks (movement-blocks 0.75)
        attempts (atom 0)]
    (with-redefs [gpu/open! (fn [& _] (swap! attempts inc) (throw (UnsatisfiedLinkError. "no platform library")))]
      (with-open [owner (movement/open! {:budget-ms 5000})]
        (is (= :timeout (get-in (movement/resolve-contributions! owner patch blocks {:deadline-nanos Long/MIN_VALUE})
                                [:movement :reason])))
        (is (= :no-geometry (get-in (movement/resolve-contributions! owner patch []) [:movement :reason])))
        (is (zero? @attempts))
        (dotimes [_ 2]
          (let [out (movement/resolve-contributions! owner patch blocks)]
            (is (= :unavailable (get-in out [:movement :reason])))
            (is (= "java.lang.UnsatisfiedLinkError" (get-in out [:movement :error])))
            (is (= (frame/portable-frame (frame/resolve-contributions patch blocks)) (frame/portable-frame out)))))
        (is (= 1 @attempts))))))
