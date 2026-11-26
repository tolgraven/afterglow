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
    (if fine (+ (* 256 (byte-at coarse)) (byte-at fine)) (byte-at coarse))))

(defn- fine-native?
  "Whether the resident renderer's guard window fits inside one 16-bit code
  step. Wider rows resolve every coarse/fine axis on the reference."
  [owner]
  (< (* 2.0 65535 (get-in (movement/renderer owner) [:rounding :margin])) 1.0))

(defn- with-coarse-axes
  "The same rig with 8-bit pan and tilt. Every table row keeps these native."
  [fixtures]
  (mapv #(cond-> % (:pan (:channels %)) (assoc :channels {:pan 1 :tilt 3})) fixtures))

(deftest physical-movement-resolves-a-rounding-boundary-on-the-reference
  (doseq [[channels boundary-code] [[{:pan [1 2] :tilt [3 4]} 32768] [{:pan 1 :tilt 3} 128]]]
    (testing channels
      (let [head {:position [0 0 0] :universe 1 :channels channels}
            patch (frame/compile-patch [(assoc head :id :boundary :address 512)
                                        (assoc head :id :stable :address 50)])
            blocks [{:kind :assignments
                     :assignments [{:target-id :boundary :attribute :direction :value [0.0 0.25 1.0]}
                                   {:target-id :stable :attribute :direction :value [0.45 0.33 1.0]}]}]
            expected (frame/resolve-contributions patch blocks)]
        (with-open [owner (movement/open! {:budget-ms 10000})]
          (let [actual (movement/resolve-contributions! owner patch blocks)]
            (is (= (if (or (not (vector? (:pan channels))) (fine-native? owner))
                     {:backend :native-gpu :gpu-heads 1 :cpu-heads 1}
                     {:backend :cpu :gpu-heads 0 :cpu-heads 2 :reason :ambiguous})
                   (:movement actual)))
            (is (= boundary-code (motor-word actual (get-in patch [:by-id :boundary]) :pan)))
            (is (= (update-vals (:universes expected) vec)
                   (update-vals (:universes actual) vec)))))))))

(deftest a-beam-near-the-pan-axis-resolves-its-pan-on-the-reference
  (let [margin 1.0e-6]
    (doseq [elevation [0.0 45.0 -80.0 82.0]]
      (is (= margin (gpu/pan-margin margin elevation)) (str elevation)))
    (doseq [elevation [87.0 -88.5 89.9]
            :let [secant (/ 1.0 (Math/cos (Math/toRadians elevation)))]]
      (is (< (abs (- (* margin (/ secant 8.0)) (gpu/pan-margin margin elevation))) 1.0e-18) (str elevation)))
    (is (every? #(< 1.0 (gpu/pan-margin margin %)) [90.0 -90.0])
        "On the pan axis the margin exceeds the whole normalized range")
    (is (zero? (gpu/pan-margin 0.0 89.9))))
  ;; Both heads request one pan, clear of a 16-bit rounding boundary by twice
  ;; the Apple margin. Only the elevation differs: 63.4 and 89.7 degrees.
  (let [head {:position [0 0 0] :universe 0 :channels {:pan [1 2] :tilt [3 4]}}
        patch (frame/compile-patch [(assoc head :id :near :address 1) (assoc head :id :clear :address 5)])
        targets {:near {:direction [0.003 1.0 0.004]} :clear {:direction [0.3 1.0 0.4]}}]
    (with-open [solver (gpu/open! patch)]
      (let [fine? (< (* 2.0 65535 (get-in solver [:resources :rounding :margin])) 1.0)
            unguarded (assoc-in solver [:resources :rounding :margin] 0.0)]
        (is (= (if fine? #{:clear} #{}) (set (keys (gpu/solve-selected! solver targets {})))))
        (is (= #{:near :clear} (set (keys (gpu/solve-selected! unguarded targets {})))))))))

(deftest an-aim-near-its-mount-packs-the-reference-bytes
  ;; Every component of this aim passes movement's float32 subtraction check.
  ;; Subtracted in float32, its pan was 1.13 times its guard margin off on an
  ;; Apple M4 Pro and packed one 16-bit code above the reference.
  (let [position [2.7790385965192548 2.4569145810083777 3.104342354608092]
        aim [2.55913148710616 2.660773155197291 3.2690111407200733]
        patch (frame/compile-patch
               [{:id :near :position position :rotation-deg [-48.70789975821497 134.36556034807018 6.9888084391654814]
                 :universe 0 :address 1 :channels {:pan [1 2] :tilt [3 4]}
                 :calibration {:pan {:min-deg -180.0 :max-deg 180.0} :tilt {:min-deg -135.0 :max-deg 135.0}}}])
        blocks [{:kind :assignments :assignments [{:target-id :near :attribute :aim :value aim}]}]
        expected (frame/resolve-contributions patch blocks)]
    (with-open [solver (gpu/open! patch)
                owner (movement/open! {:budget-ms 10000})]
      (let [unguarded (assoc-in solver [:resources :rounding :margin] 0.0)]
        (is (= (gpu/solve-selected! unguarded {:near {:direction (mapv - aim position)}} {})
               (gpu/solve-selected! unguarded {:near {:aim aim}} {}))
            "An aim draws as the float64 direction from its mount"))
      (let [actual (movement/resolve-contributions! owner patch blocks)]
        (is (= 46321 (motor-word expected (get-in patch [:by-id :near]) :pan)))
        (is (= (update-vals (:universes expected) vec) (update-vals (:universes actual) vec)))))))

(defn- sweep-patch [heads channels]
  (frame/compile-patch
   (mapv (fn [i]
           {:id i :position [(- (mod i 8) 4) (+ 2.0 (mod i 3)) (- (quot i 8) 2)]
            :rotation-deg [(if (odd? i) 180 0) (- (mod (* i 31) 340) 170) (mod i 27)]
            :universe 0 :address (inc (* 4 i)) :channels channels
            :calibration (if (even? i)
                           {:pan {:min-deg -270 :max-deg 270} :tilt [120 150]}
                           {:pan [125 -170] :tilt {:min-deg -45 :max-deg 55}})})
         (range heads))))

(defn- axis-errors
  "Largest unguarded :scaled, :pan and :tilt errors of the solved heads.
  :scaled is what a row margin has to cover: the tilt error, and the pan error
  divided by the factor that gpu/pan-margin widens the margin by at that
  elevation."
  [expected solved]
  (reduce (fn [worst [id values]]
            (let [error (fn [axis] (abs (- (get-in expected [id axis]) (axis values))))
                  pan (error :pan) tilt (error :tilt)]
              (-> worst
                  (update :scaled max tilt (/ pan (gpu/pan-margin 1.0 (:tilt-deg values))))
                  (update :pan max pan)
                  (update :tilt max tilt))))
          {:scaled 0.0 :pan 0.0 :tilt 0.0} solved))

(defn- movement-sweep
  "Send seeded random aims through the guarded owner and compare each packed
  frame with the reference. Also read every head the shader itself accepts
  without the rounding guard, to measure the float32 axis error it must cover."
  [{:keys [heads frames seed channels]}]
  (let [patch (sweep-patch heads channels)
        rng (java.util.Random. seed)
        coordinate #(* % (- (.nextDouble rng) 0.5))]
    (with-open [solver (gpu/open! patch)
                owner (movement/open! {:budget-ms 10000})]
      (let [unguarded (assoc-in solver [:resources :rounding :margin] 0.0)]
        (loop [frame 0 history {} result {:retained 0 :accepted 0 :mismatched []
                                          :errors {:scaled 0.0 :pan 0.0 :tilt 0.0}}]
          (if (< frame frames)
            (let [targets (into {} (for [id (range heads)] [id [(coordinate 6.0) (coordinate 3.0) (coordinate 6.0)]]))
                  blocks [{:kind :assignments
                           :assignments (vec (for [[id aim] targets] {:target-id id :attribute :aim :value aim}))}]
                  options (assoc history :compact-values? true)
                  expected (frame/resolve-contributions patch blocks options)
                  actual (movement/resolve-contributions! owner patch blocks options)
                  solved (gpu/solve-selected! unguarded targets history)]
              (recur (inc frame) {:previous-compact (:compact expected)}
                     (cond-> (-> result
                                 (update :retained + (get-in actual [:movement :gpu-heads]))
                                 (update :accepted + (count solved))
                                 (update :errors #(merge-with max % (axis-errors (:values expected) solved))))
                       (not= (update-vals (:universes expected) vec) (update-vals (:universes actual) vec))
                       (update :mismatched conj frame))))
            (merge result (select-keys (:resources solver) [:renderer :version :rounding]))))))))

(deftest a-seeded-movement-sweep-packs-the-reference-bytes
  ;; Every driver must publish the reference bytes and keep its unguarded axis
  ;; error inside the margin that gpu/rounding-margins assigns to it. The
  ;; printed scaled maximum is the measurement that qualifies a table row. The
  ;; raw pan maximum has no bound: it grows as a sample lands nearer the pan
  ;; axis. 8-bit axes keep native results under every row, so the byte
  ;; comparison also covers drivers whose row resolves all coarse/fine axes on
  ;; the reference.
  (doseq [{:keys [heads frames channels apple-floor] :as rig}
          [{:rig :fine-acceptance :heads 32 :frames 40 :seed 555 :channels {:pan [1 2] :tilt [3 4]} :apple-floor 1000}
           {:rig :fine :heads 64 :frames 400 :seed 648 :channels {:pan [1 2] :tilt [3 4]}}
           {:rig :coarse :heads 64 :frames 400 :seed 649 :channels {:pan 1 :tilt 2}}]]
    (testing (:rig rig)
      (let [{:keys [renderer version rounding retained accepted errors mismatched]} (movement-sweep rig)
            margin (:margin rounding)
            worst (:scaled errors)
            ;; Share of one physical code step that the guard window spans.
            window (* 2.0 margin (if (vector? (:pan channels)) 65535 255))
            clear (max 0.0 (- 1.0 window))
            total (* heads frames)]
        (println "Movement sweep" {:rig (:rig rig) :renderer renderer :version version :rounding rounding
                                   :max-scaled-error worst :error-over-margin (/ worst margin)
                                   :max-pan-error (:pan errors) :max-tilt-error (:tilt errors)
                                   :axis-samples (* 2 accepted) :gpu-heads retained :heads total})
        (is (= [] mismatched) "Every frame must pack the reference bytes")
        (is (< worst margin) "Unguarded axis error must stay inside the renderer's rounding margin")
        ;; An axis stays native while its guard window sits inside one code
        ;; step, so both axes of a head do for about the square of that share.
        (is (<= (* 0.9 clear clear accepted) retained accepted total))
        ;; A margin above half a step reaches a boundary even from a clamped end.
        (when (< 1.0 window)
          (is (zero? retained) "A window wider than one code step always straddles a rounding boundary"))
        (when (and apple-floor (= :apple-m-series (:row rounding)))
          (is (<= apple-floor retained)))))))

(deftest the-rounding-table-qualifies-only-measured-renderers
  (let [ulp (double (Math/ulp (float 1.0)))
        row (fn [renderer] (:row (gpu/rounding-guard renderer)))]
    (is (= {:row :apple-m-series :ulps 8 :margin (* 8 ulp)} (gpu/rounding-guard "Apple M4 Pro")))
    (is (= {:row :mesa-llvmpipe :ulps 128 :margin (* 128 ulp)}
           (gpu/rounding-guard "llvmpipe (LLVM 21.1.8, 256 bits)")))
    (is (= {:row :apple-software :ulps 512 :margin (* 512 ulp)} (gpu/rounding-guard "Apple Software Renderer")))
    (is (= {:row :unqualified :ulps 512 :margin (* 512 ulp)} (gpu/rounding-guard nil)))
    (is (every? #(= :apple-m-series (row %))
                ["Apple M1" "Apple M2 Ultra" "Apple M3 Max" "Apple M4" "Apple M4 Pro" "Apple M4 Max" "Apple M12 Pro"]))
    (is (every? #(= :mesa-llvmpipe (row %))
                ["llvmpipe (LLVM 21.1.8, 256 bits)" "llvmpipe (LLVM 15.0.7, 128 bits)"]))
    ;; Software, translated and other vendors' drivers have no measured bound.
    ;; Neither has a chip name with any suffix other than Pro, Max or Ultra.
    (is (every? #(= :unqualified (row %))
                ["" "Apple Software Renderer 2" "Apple M1 (G13G B0)" "Apple M4 Pro (software)" "Apple MX"
                 "Apple Paravirtual device" "AMD Radeon Pro 5500M OpenGL Engine" "Intel(R) Iris(TM) Plus Graphics OpenGL Engine"
                 "softpipe" "zink Vulkan 1.3(llvmpipe (LLVM 21.1.8, 256 bits) (LLVMPIPE))" "llvmpipe"
                 "NVIDIA GeForce RTX 4090/PCIe/SSE2" "Mesa Intel(R) UHD Graphics 770 (ADL-S GT1)"]))
    ;; Rows never narrow in order, and the fallback row matches every renderer.
    (is (apply <= (map :ulps gpu/rounding-margins)))
    (is (nil? (:renderer (peek gpu/rounding-margins))))))

(deftest published-frames-use-only-effective-selected-movement
  (doseq [[axes rig] [[:fine fixtures] [:coarse (with-coarse-axes fixtures)]]]
    (testing axes
      (let [patch (frame/compile-patch rig)
            reordered (frame/compile-patch (vec (reverse rig)))
            before (frame/resolve-frame reordered [{:target-id :back :attribute :pan :value 0.04}] {:compact-values? true})]
        (with-open [owner (movement/open! {:budget-ms 10000})]
          (doseq [rich? [true false] alpha [0.0 0.25 0.75 1.0]
                  :let [options {:previous-compact (:compact before) :include-values? rich? :compact-values? true}
                        expected (frame/resolve-contributions patch (movement-blocks alpha) options)
                        actual (movement/resolve-contributions! owner patch (movement-blocks alpha) options)
                        ref (first (frame/project-compact (:compact expected)))
                        pose (first (frame/project-compact (:compact actual)))]]
            (is (= (if (or (= :coarse axes) (fine-native? owner))
                     {:backend :native-gpu :gpu-heads 1 :cpu-heads 0}
                     {:backend :cpu :gpu-heads 0 :cpu-heads 1 :reason :ambiguous})
                   (:movement actual)))
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
          (let [backend (if (or (= :coarse axes) (fine-native? owner)) :native-gpu :cpu)]
            (testing "changed position and ordering replace the resident native mounts"
              ;; This position keeps both axes clear of every row's 8-bit guard window.
              (let [next-patch (frame/compile-patch (vec (reverse (assoc-in rig [0 :position] [6 2 1]))))
                    options {:previous-compact (:compact before)}
                    blocks (movement-blocks 0.25)
                    actual (movement/resolve-contributions! owner next-patch blocks options)
                    reference (frame/resolve-contributions next-patch blocks options)]
                (is (= backend (get-in actual [:movement :backend])))
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
              (is (= backend (get-in (movement/resolve-contributions! owner patch (movement-blocks 0.25))
                                     [:movement :backend]))))))))))

(deftest late-draws-cannot-change-a-published-frame-or-enter-a-later-frame
  (let [patch (frame/compile-patch fixtures)
        blocks (movement-blocks 0.25)
        owner (movement/open! {:budget-ms 10000})
        started (promise) release (promise) finished (promise)
        actual-solve gpu/solve-selected!
        accepted (frame/resolve-frame patch [{:target-id :back :attribute :pan :value 0.15}]
                                      {:compact-values? true})]
    (try
      (let [first-frame (movement/resolve-contributions! owner patch blocks)]
        (is (= (if (fine-native? owner) :native-gpu :cpu) (get-in first-frame [:movement :backend]))))
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
        (is (= (if (fine-native? owner) :native-gpu :cpu) (get-in out [:movement :backend])))
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
