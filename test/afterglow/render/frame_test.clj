(ns afterglow.render.frame-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.render.atmosphere :as atmosphere]
            [afterglow.render.ir :as ir]
            [afterglow.render.coverage :as coverage]
            [afterglow.render.fields :as fields]
            [afterglow.render.frame :as frame]))

(def rgb {:id :rgb :position [1 2 3] :universe 1 :address 1
          :channels {:red 1 :green 2 :blue 3}})

(defn assignment [id attribute value & [blend]]
  {:target-id id :attribute attribute :value value :blend (or blend :replace)})

(defn bytes-at [result universe & offsets]
  (let [buffer (get-in result [:universes universe])]
    (mapv #(bit-and 255 (aget ^bytes buffer (dec %))) offsets)))

(defn near? [a b] (< (Math/abs (double (- a b))) 1.0e-9))

(deftest profiled-fog-opacity-fades-from-the-physical-off-bytes
  (let [nozzle {:id :jet :universe 1 :address 512 :channels {:fog [1 2]}
                :fogger {:flow-m3-min 60 :dmx-range [220.25 20.25]}}
        patch (frame/compile-patch [nozzle])
        channel (get-in patch [:by-id :jet :compiled-channels :fog])
        row (fn [physical blend opacity]
              (assoc (assignment :jet :fog (atmosphere/physical-level channel physical) blend)
                     :opacity opacity))
        bytes (fn [output] [(first (bytes-at output 1 512)) (first (bytes-at output 2 1))])]
    (doseq [include-values? [true false]
            [physical opacity expected] [[220.25 0.5 [220 64]] [20.25 0.5 [120 64]]
                                         [20.25 0.0 [220 64]] [20.25 1.0 [20 64]]]
            blend [:replace :max :add]]
      (let [assignment (row physical blend opacity)
            options {:include-values? include-values?}
            batch {:target-ids [:jet] :outputs {:fog {:type :number :components 1
                                                     :values (double-array [(:value assignment)])}}
                   :blend blend :opacity opacity}]
        (is (= expected (bytes (frame/resolve-frame patch [assignment] options))))
        (is (= expected (bytes (frame/resolve-contributions patch [{:kind :assignments :assignments [assignment]}] options))))
        (is (= expected (bytes (frame/resolve-batches patch [batch] options))))))
    (doseq [include-values? [true false]]
      (let [before (row 180.25 :replace 1.0)
            after (row 20.25 :replace 1.0)
            options {:include-values? include-values?}
            ordinary {:kind :assignments :assignments [before]}
            native {:kind :assignments :assignments [after]
                    :native-layer {:id :native :member 0 :opacity 0.5 :target-weights {:jet 1.0}}}]
        (is (= [200 64] (bytes (frame/resolve-frame patch [before (row 220.25 :replace 0.5)] options))))
        (is (= [180 64] (bytes (frame/resolve-frame patch [before (row 20.25 :replace 0.0)] options))))
        (is (= [120 64] (bytes (frame/resolve-contributions patch [ordinary (assoc-in native [:native-layer :member-opacity] 0.75)] options))))
        (is (= [180 64] (bytes (frame/resolve-contributions patch [ordinary (assoc-in native [:native-layer :member-opacity] 0.0)] options))))))))

(deftest fog-opacity-interpolates-physical-values-across-the-inversion-pivot
  (let [patch (frame/compile-patch [{:id :jet :universe 1 :address 1
                                    :channels {:fog {:offset 1 :inverted-from 120}}
                                    :fogger {:flow-m3-min 60 :dmx-range [200 255]}}])
        channel (get-in patch [:by-id :jet :compiled-channels :fog])
        row (fn [physical] (assignment :jet :fog (atmosphere/physical-level channel physical)))
        after (row 30)
        base {:kind :assignments :assignments [(row 220)]}
        native {:kind :assignments :assignments [after]
                :native-layer {:id :native :member 0}}
        native-batch (assoc native :kind :batch :batch
                            {:target-ids [:jet] :outputs {:fog {:type :number :components 1
                                                              :values (double-array [(:value after)])}}})]
    (doseq [include-values? [true false]
            :let [options {:include-values? include-values?}
                  byte (fn [blocks] (first (bytes-at (frame/resolve-contributions patch blocks options) 1 1)))]]
      (is (= [166] (bytes-at (frame/resolve-frame patch [(assoc after :opacity 0.2)] options) 1 1)))
      (is (= 166 (byte [(assoc-in native [:native-layer :member-opacity] 0.2)])))
      (is (= 166 (byte [(assoc-in native-batch [:native-layer :target-weights] {:jet 0.2})])))
      (is (= 125 (byte [base (assoc-in native [:native-layer :member-opacity] 0.5)])))
      (is (= 220 (byte [base (assoc-in native [:native-layer :member-opacity] 0.0)])))
      (is (= 30 (byte [base native]))))))

(deftest linear-rgb-and-master-dimming-without-hardware-dimmer
  (let [result (frame/resolve-frame [rgb]
                                   [(assignment :rgb :color [1.0 0.5 0.0])
                                    (assignment :rgb :dimmer 0.5)]
                                   {:master 0.5})]
    (is (= [64 32 0] (bytes-at result 1 1 2 3)))
    (is (= [0.25 0.125 0.0] (get-in result [:values :rgb :emitted-color])))
    (is (= [1 2 3] (get-in result [:values :rgb :position])))
    (is (= [:rgb] (:target-order result)))))

(deftest real-dimmer-is-applied-once-and-blackout-stops-emission
  (let [fixture (assoc rgb :channels {:red 1 :green 2 :blue 3 :dimmer 4})
        contributions [(assignment :rgb :color [1.0 0.5 0.25])
                       (assignment :rgb :dimmer 0.5)]
        result (frame/resolve-frame [fixture] contributions {:master 0.5})
        dark (frame/resolve-frame [fixture] contributions {:master 0.5 :blackout? true})]
    (is (= [255 128 64 64] (bytes-at result 1 1 2 3 4)))
    (is (= [0.25 0.125 0.0625] (get-in result [:values :rgb :emitted-color])))
    (is (= [0 0 0 0] (bytes-at dark 1 1 2 3 4)))
    (is (= [0.0 0.0 0.0] (get-in dark [:values :rgb :emitted-color])))))

(deftest explicit-rgbw-extraction-and-white-override
  (let [fixture (assoc rgb :channels {:red 1 :green 2 :blue 3 :white 4})
        assignments [(assignment :rgb :color [0.5 0.25 0.75])]
        none (frame/resolve-frame [fixture] assignments)
        extracted (frame/resolve-frame [(assoc fixture :rgbw-policy :extract-min)] assignments)
        override (frame/resolve-frame [(assoc fixture :rgbw-policy :extract-min)]
                                      (conj assignments (assignment :rgb :white 0.5)))]
    (is (= [128 64 191 0] (bytes-at none 1 1 2 3 4)))
    (is (= [64 0 128 64] (bytes-at extracted 1 1 2 3 4)))
    (is (= [0.5 0.25 0.75] (get-in extracted [:values :rgb :emitted-color])))
    (is (= [64 0 128 128] (bytes-at override 1 1 2 3 4)))
    (is (seq (frame/validate-patch [(assoc rgb :rgbw-policy :extract-min)])))))

(deftest color-correction-serves-rich-and-compact-rgb-output
  (let [assignments [(assignment :rgb :color [1.0 0.5 0.25])]
        fixture (assoc rgb :color-correction {:red 0.5 :green 0.0})]
    (doseq [include-values? [true false]
            :let [options {:include-values? include-values? :compact-values? true}
                  output (frame/resolve-frame [fixture] assignments options)
                  projected (frame/project-compact (:compact output) [0])
                  untrimmed (frame/resolve-frame [rgb] assignments options)
                  identity-trim (frame/resolve-frame [(assoc rgb :color-correction {:red 1 :green 1 :blue 1})]
                                                     assignments options)]]
      (is (= [128 0 64] (bytes-at output 1 1 2 3)))
      (is (= [0.5 0.0 0.25] (get-in projected [0 :emitted-color])))
      (is (= [255 128 64] (bytes-at untrimmed 1 1 2 3) (bytes-at identity-trim 1 1 2 3))))))

(deftest color-correction-happens-after-native-blending-and-rgbw-extraction
  (let [fixture (assoc rgb :channels {:red 1 :green 2 :blue 3 :white 4} :rgbw-policy :extract-min
                       :color-correction {:red 0.0 :blue 0.5 :white 0.5})
        blocks [{:kind :assignments :assignments [(assignment :rgb :color [0.5 0.5 1.0])]}
                {:kind :batch
                 :batch {:target-ids [:rgb] :outputs {:color {:type :vec3 :components 3
                                                            :values (double-array [1.0 0.0 1.0])}}}
                 :native-layer {:id :tint :member 0 :opacity 0.5}}
                {:kind :assignments :assignments [(assignment :rgb :red 0.5)]}]]
    (doseq [include-values? [true false]
            intensity [{:master 0.5} {:hdr {:gain 0.5}}]
            :let [output (frame/resolve-contributions [fixture] blocks
                           (assoc intensity :include-values? include-values? :compact-values? true))
                  projected (frame/project-compact (:compact output) [0])]]
      (is (= [64 0 48 16] (bytes-at output 1 1 2 3 4)))
      (is (= [0.3125 0.0625 0.25] (get-in projected [0 :emitted-color])))
      (when include-values?
        (is (= [0.75 0.25 1.0] (get-in output [:values :rgb :color])))))))

(deftest blend-order-and-independent-targets
  (let [b (assoc rgb :id :b :address 10)
        assignments [(assignment :rgb :color [0.2 0.3 0.4])
                     (assignment :rgb :color [0.1 0.5 0.2] :max)
                     (assignment :rgb :color [0.1 0.1 0.1] :add)
                     (assignment :b :color [1.0 0.0 0.0])
                     (assignment :rgb :red 0.8)]
        result (frame/resolve-frame [b rgb] assignments)]
    (is (= [:b :rgb] (:target-order result)))
    (is (= [204 153 128] (bytes-at result 1 1 2 3)))
    (is (= [255 0 0] (bytes-at result 1 10 11 12)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Blended assignment"
                          (frame/resolve-frame [rgb]
                                               [(assignment :rgb :red 0.8)
                                                (assignment :rgb :red 0.8 :add)])))))

(deftest dimmer-only-defaults-to-zero
  (let [fixture {:id :d :position [0 0 0] :universe 0 :address 512 :channels {:dimmer 1}}]
    (is (= [0] (bytes-at (frame/resolve-frame [fixture] []) 0 512)))
    (is (= [128] (bytes-at (frame/resolve-frame [fixture] [(assignment :d :dimmer 0.5)]) 0 512)))
    (is (= [0.5 0.5 0.5] (get-in (frame/resolve-frame [fixture] [(assignment :d :dimmer 0.5)])
                                [:values :d :emitted-color])))
    (is (= [0.5 0.25 0.0] (get-in (frame/resolve-frame [(assoc fixture :emission-color [1 0.5 0])]
                                                     [(assignment :d :dimmer 0.5)])
                                 [:values :d :emitted-color])))))

(deftest prepared-movement-packs-only-axes-for-the-captured-targets
  (let [head {:id :head :position [0 2 0] :universe 0 :address 1 :channels {:pan 1 :tilt 2}}
        patch (frame/compile-patch [head rgb])
        blocks [{:kind :assignments :source :point :assignments [(assignment :head :aim [1 3 4])
                                                                 (assignment :rgb :red 1/2)]}
                {:kind :assignments :source :overlay
                 :assignments [(assoc (assignment :head :aim [3 3 0]) :opacity 1/2)
                               (assignment :head :direction [0 1 0])]}]
        solution {:pan 0.25 :tilt 0.75 :pan-deg 45.0 :tilt-deg 12.0 :aim-reachable? true}]
    (doseq [rich? [true false]
            :let [opts {:include-values? rich? :compact-values? true}
                  {:keys [pack targets]} (frame/prepare-movement-frame patch blocks opts)]]
      (is (= {:head {:aim [2N 3N 2N]}} targets))
      (is (= (frame/portable-frame (frame/resolve-contributions patch blocks opts))
             (frame/portable-frame (pack {}))))
      (let [out (pack {:head solution})]
        (is (= [64 191] (bytes-at out 0 1 2)))
        (is (= [128] (bytes-at out 1 1)))
        (is (= [2.0 3.0 2.0] (:aim (first (frame/project-compact (:compact out))))))
        (when rich? (is (= solution (select-keys (get-in out [:values :head]) (keys solution))))))
      (is (thrown? clojure.lang.ExceptionInfo (pack {:rgb solution})))
      (try (pack {:head (assoc solution :pan ##NaN)})
           (is false "invalid movement cannot pack")
           (catch clojure.lang.ExceptionInfo error (is (= :overlay (:effect-source (ex-data error)))))))))

(deftest multi-universe-coarse-fine-and-inversion
  (let [fixture {:id :head :position [0 0 0] :universe 2 :address 512
                 :channels {:pan [1 2] :dimmer {:offset 3 :inverted-from 0}}}
        patch (frame/compile-patch [(assoc rgb :universe 9) fixture])]
    (doseq [include-values? [true false]]
      (let [options {:include-values? include-values? :compact-values? true}
            half (frame/resolve-frame patch [(assignment :head :pan 0.5)
                                             (assignment :head :dimmer 0.25)] options)
            full (frame/resolve-frame patch [(assignment :head :pan 1.0)] options)
            idle (frame/idle-universes patch)
            buffers [(:universes half) (:universes full) idle]]
        (doseq [universes buffers]
          (is (sorted? universes))
          (is (= [2 3 9] (vec (keys universes))))
          (is (= [512 512 512] (mapv #(alength ^bytes %) (vals universes)))))
        (is (= 9 (count (distinct (mapcat vals buffers)))))
        (is (= [128] (bytes-at half 2 512)))
        (is (= [0 191] (bytes-at half 3 1 2)))
        (is (= [255] (bytes-at full 2 512)))
        (is (= [255] (bytes-at full 3 1)))
        (is (= [0 0 0] (bytes-at full 9 1 2 3)))
        (is (= [0 255] (bytes-at {:universes idle} 3 1 2)))
        (is (every? zero? (concat (idle 2) (drop 2 (idle 3)) (idle 9))))))))

(deftest movement-uncertainty-uses-the-physical-channel-quantizer
  (let [fixture {:id :head :position [0 0 0] :universe 2 :address 512
                 :channels {:pan [1 2] :tilt 3
                            :focus {:offset 4 :fine-offset 5 :inverted-from 128}}}
        patch (frame/compile-patch [fixture])
        channel (get-in patch [:by-id :head :compiled-channels])
        margin 9.5e-7]
    (is (= [[2 511] [3 0]] ((juxt :coarse :fine) (:pan channel))))
    (is (frame/stable-channel-code? (:pan channel) (/ 30000.0 65535) margin))
    (is (not (frame/stable-channel-code? (:pan channel) (/ 30000.5 65535) margin)))
    (is (frame/stable-channel-code? (:tilt channel) (/ 128.0 255) margin))
    (is (not (frame/stable-channel-code? (:tilt channel) (/ 128.5 255) margin)))
    (is (not (frame/stable-channel-code? (:focus channel) (/ 128.0 255) margin)))
    (is (frame/stable-channel-code? (:pan channel) 0.0 margin))
    (is (frame/stable-channel-code? (:pan channel) 1.0 margin))))

(deftest invalid-patches-and-assignments-are-rejected
  (doseq [fixtures [[rgb rgb]
                    [(assoc rgb :address 0)]
                    [(assoc rgb :universe -1)]
                    [(assoc rgb :position [0 Double/NaN 0])]
                    [(assoc rgb :surface-uv [1.0 Double/NaN])]
                    [(assoc rgb :surface-uv [0 1 2])]
                    [(assoc rgb :channels {:red 0})]
                    [(assoc rgb :channels {:red [1 1]})]
                    [(assoc rgb :channels {:red 1 :green 1})]
                    [(assoc rgb :rgbw-policy :magic)]
                    [rgb (assoc rgb :id :b :address 3)]
                    [(assoc rgb :calibration {:pan {:min-deg 5 :max-deg 0}})]
                    [(assoc rgb :channels {:color 1})]]]
    (is (seq (frame/validate-patch fixtures)) (pr-str fixtures)))
  (is (seq (frame/validate-patch [(assoc rgb :universe Integer/MAX_VALUE :address 512)])))
  (doseq [assignments [[(assignment :missing :red 0.5)]
                       [(assignment :rgb :red -0.1)]
                       [(assignment :rgb :red Double/NaN)]
                       [(assignment :rgb :red 0.2 :unknown)]
                       [(assignment :rgb :color [1 2 3])]
                       [(assignment :rgb :unsupported 0.2)]
                       [(assignment :rgb :aim [1 2 3])]]]
    (is (thrown? clojure.lang.ExceptionInfo (frame/resolve-frame [rgb] assignments))))
  (is (thrown? clojure.lang.ExceptionInfo (frame/resolve-frame [rgb] [] {:master 2}))))

(deftest overlap-detection-crosses-universe-boundaries
  (is (seq (frame/validate-patch
            [(assoc rgb :address 512)
             (assoc rgb :id :b :universe 2 :address 2)]))))

(deftest compiled-plan-and-returned-buffers-have-independent-lifetimes
  (let [patch (frame/compile-patch [rgb])
        input [(assignment :rgb :color [1 0 0])]
        first (frame/resolve-frame patch input)
        second (frame/resolve-frame patch [])]
    (is (= [255 0 0] (bytes-at first 1 1 2 3)))
    (is (= [0 0 0] (bytes-at second 1 1 2 3)))
    (aset-byte ^bytes (get-in second [:universes 1]) 0 (byte 42))
    (is (= [255] (bytes-at first 1 1)))
    (is (= input [(assignment :rgb :color [1 0 0])]))
    (is (= [:rgb] (:target-order patch)))))

(def moving {:id :moving :position [1 2 3] :universe 1 :address 1
             :channels {:pan [1 2] :tilt [3 4] :focus 5}
             :calibration {:pan {:min-deg -180 :max-deg 180}
                           :tilt {:min-deg -90 :max-deg 90}}})

(deftest basic-world-aim-and-calibration
  (let [forward (frame/resolve-frame [moving] [(assignment :moving :aim [1 2 4])])
        right (frame/resolve-frame [moving] [(assignment :moving :aim [2 2 3])])
        above (frame/resolve-frame [moving] [(assignment :moving :direction [0 1 0])])]
    (is (= [128 0 128 0] (bytes-at forward 1 1 2 3 4)))
    (is (near? 0.75 (get-in right [:values :moving :pan])))
    (is (near? 90.0 (get-in right [:values :moving :pan-deg])))
    (is (= [1.0 0.0 0.0] (get-in right [:values :moving :direction])))
    (is (near? 1.0 (get-in above [:values :moving :tilt])))
    (is (true? (get-in forward [:values :moving :aim-reachable?])))
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/resolve-frame [moving] [(assignment :moving :aim [1 2 3])])))))

(deftest rotated-rigs-and-legacy-center-half-circle-calibration
  (let [rotated (assoc moving :rotation-deg [0 90 0])
        result (frame/resolve-frame [rotated] [(assignment :moving :direction [1 0 0])])
        legacy (assoc moving :calibration {:pan [127 85] :tilt [127 127]})
        calibrated (frame/resolve-frame [legacy] [(assignment :moving :direction [1 0 0])])]
    (is (near? 0.5 (get-in result [:values :moving :pan])))
    (is (near? (/ 169.5 255) (get-in calibrated [:values :moving :pan])))
    (is (= [170 42] (bytes-at calibrated 1 1 2)))))

(deftest calibrated-pan-prefers-reachability-and-preserves-wrap-ties
  (doseq [[calibration direction previous expected reachable?]
          [[{:min-deg -360 :max-deg 360} [0 0 -1] 0.5 0.75 true]
           [[127.5 -63.75] [0 0 -1] 0.5 0.25 true]
           [{:min-deg 0 :max-deg 270} [-1 0 0] 0.0 1.0 true]
           [{:min-deg -90 :max-deg 90} [0 0 -1] 0.5 1 false]
           [{:min-deg -90 :max-deg 90} [0 0 -1] 0.0 0 false]]]
    (let [fixture (assoc-in moving [:calibration :pan] calibration)
          result (frame/resolve-frame [fixture] [(assignment :moving :direction direction)]
                                      {:previous-values {:moving {:pan previous}}})
          head (get-in result [:values :moving])]
      (is (= expected (:pan head)) [calibration direction previous])
      (is (= reachable? (:aim-reachable? head))))))

(deftest pan-continuity-and-unreachable-aim
  (let [wide (assoc moving :calibration {:pan {:min-deg -360 :max-deg 360}
                                        :tilt {:min-deg -30 :max-deg 30}})
        left (frame/resolve-frame [wide] [(assignment :moving :direction [0 0 -1])]
                                  {:previous-values {:moving {:pan 0.2}}})
        right (frame/resolve-frame [wide] [(assignment :moving :direction [0 0 -1])]
                                   {:previous-values {:moving {:pan 0.8}}})
        up (frame/resolve-frame [wide] [(assignment :moving :direction [0 1 0])])]
    (is (near? 0.25 (get-in left [:values :moving :pan])))
    (is (near? 0.75 (get-in right [:values :moving :pan])))
    (is (false? (get-in up [:values :moving :aim-reachable?])))
    (is (= 1 (get-in up [:values :moving :tilt])))))

(defn buffer-values [result]
  (into {} (map (fn [[u bytes]] [u (vec bytes)]) (:universes result))))

(deftest packed-output-matches-preview-output-on-mixed-rigs
  (let [fixtures (mapv (fn [i]
                         {:id i :position [i 0 0] :universe 1 :address (inc (* i 25))
                          :rgbw-policy (if (even? i) :extract-min :none)
                          :channels (cond-> {:red 1 :green 2 :blue 3 :white 4 :focus [5 6]
                                             :strobe {:offset 7 :inverted-from 1} :amber 8 :uv 9}
                                      (odd? i) (assoc :dimmer 10))}) (range 20))
        patch (frame/compile-patch fixtures)
        assignments (vec (mapcat (fn [i]
                                  [(assignment i :color [(/ (double (mod i 9)) 10.0) 0.3 0.5])
                                   (assignment i :color [0.0 0.2 0.0] :add)
                                   (assignment i :red 0.2 :max)
                                   (assignment i :white (/ (double (mod i 4)) 4.0))
                                   (assignment i :focus (/ (double i) 20.0))
                                   (assignment i :dimmer 0.75)
                                   (assignment i :strobe 0.5)
                                   (assignment i :amber 0.3)
                                   (assignment i :uv 0.2)]) (range 20)))]
    (doseq [options [{:master 1.0} {:master 0.25} {:master 0.0} {:blackout? true}]]
      (let [with-values (frame/resolve-frame patch assignments options)
            packed (frame/resolve-frame patch assignments (assoc options :include-values? false))]
        (is (= (buffer-values with-values) (buffer-values packed)))
        (is (nil? (:values packed)))
        (is (= (:target-order with-values) (:target-order packed)))))))

(deftest packed-option-retains-exact-number-and-geometry-semantics
  (let [fixtures [(assoc moving :channels {:pan [1 2] :tilt [3 4] :focus [5 6]})]]
    (doseq [assignments [[(assignment :moving :focus 1/10) (assignment :moving :focus 7/10 :add)]
                         [(assignment :moving :focus 0.1M) (assignment :moving :focus 0.7M :add)]
                         [(assignment :moving :direction [0 0 -1]) (assignment :moving :focus 0.5)]]]
      (let [options {:previous-values {:moving {:pan 0.9}}}
            with-values (frame/resolve-frame fixtures assignments options)
            packed (frame/resolve-frame fixtures assignments (assoc options :include-values? false))]
        (is (= (buffer-values with-values) (buffer-values packed)))))))

(deftest packed-option-rejects-the-same-invalid-assignments
  (doseq [assignments [[(assignment :rgb :red 0.8) (assignment :rgb :red 0.8 :add)]
                       [(assignment :rgb :color [1 2 3])]
                       [(assignment :missing :red 0.5)]
                       [(assignment :rgb :red Double/NaN)]
                       [(assignment :rgb :red 0.5 :unknown)]]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/resolve-frame [rgb] assignments {:include-values? false})))))

(deftest heterogeneous-attributes-use-bounded-sparse-fallback
  (let [fixtures (mapv (fn [i] {:id i :universe 1 :address (inc i)
                               :channels {(keyword (str "attribute-" i)) 1}}) (range 70))
        assignments (mapv (fn [i] (assignment i (keyword (str "attribute-" i)) 0.5)) (range 70))]
    (is (= (buffer-values (frame/resolve-frame fixtures assignments))
           (buffer-values (frame/resolve-frame fixtures assignments {:include-values? false}))))))

(deftest compiled-channel-scatter-preserves-public-packing-at-fine-boundaries
  (doseq [pivot [nil 0 1 24.25 1/10]
          fine? [false true]
          level [0.0 (/ 1.0 255.0) 0.1 0.5 (/ 127.0 255.0) 0.999 1.0 0.8M 4/5]]
    (let [spec (cond-> {:offset 1} fine? (assoc :fine-offset 2) (some? pivot) (assoc :inverted-from pivot))
          fixture {:id :channel :position [0 0 0] :universe 1 :address 1 :channels {:focus spec}}
          result (frame/resolve-frame [fixture] [(assignment :channel :focus level)])
          expected {1 (byte-array 512)}
          channel (cond-> {:coarse [1 0]} fine? (assoc :fine [1 1]) (some? pivot) (assoc :inverted-from pivot))]
      (frame/pack-value! expected channel level)
      (is (= (vec (get expected 1)) (vec (get-in result [:universes 1])))
          (pr-str {:pivot pivot :fine? fine? :level level})))))

(deftest compact-preview-fields-match-rich-values-without-another-render
  (let [moving (assoc moving :channels {:pan [1 2] :tilt [3 4] :focus 5 :zoom 6 :strobe 7})
        pixel (assoc rgb :address 20)
        fixtures [moving pixel]
        assignments [(assignment :moving :aim [2 2 3]) (assignment :moving :focus 0.7)
                     (assignment :moving :zoom 0.2) (assignment :rgb :color [0.5 0.25 0.75])]
        rich (frame/resolve-frame fixtures assignments {:compact-values? true})
        lean (frame/resolve-frame fixtures assignments {:include-values? false :compact-values? true})
        projected (frame/project-compact (:compact lean))]
    (is (= (buffer-values rich) (buffer-values lean)))
    (is (nil? (:values lean)))
    (is (= [:moving :rgb] (mapv :id projected)))
    (doseq [value projected, [attribute number-or-vector] (dissoc value :id)]
      (let [expected (if (#{:pan :tilt :focus :zoom :strobe} attribute)
                       (get-in rich [:values (:id value) :channels attribute])
                       (get-in rich [:values (:id value) attribute]))]
        (is (if (vector? number-or-vector) (every? true? (map == number-or-vector expected))
                (== number-or-vector expected)))))
    (is (not (contains? (second projected) :focus)))
    (is (= [(second projected)] (frame/project-compact (:compact lean) [1])))
    (is (thrown? clojure.lang.ExceptionInfo (frame/project-compact (:compact lean) [2])))
    (aset-double ^doubles (get-in lean [:compact :fields :focus :values]) 0 0.1)
    (is (== 0.7 (aget ^doubles (get-in rich [:compact :fields :focus :values]) 0)))))

(deftest dense-color-compact-projection-matches-general-rgbw-resolution
  (let [fixture (assoc rgb :channels {:red 1 :green 2 :blue 3 :white 4} :rgbw-policy :extract-min)
        assignments [(assignment :rgb :color [0.5 0.25 0.75]) (assignment :rgb :dimmer 0.8)]
        rich (frame/resolve-frame [fixture] assignments {:master 0.5})
        compact (frame/resolve-frame [fixture] assignments {:master 0.5 :include-values? false :compact-values? true})
        projected (first (frame/project-compact (:compact compact)))]
    (is (= (buffer-values rich) (buffer-values compact)))
    (is (= (get-in rich [:values :rgb :emitted-color]) (:emitted-color projected)))
    (is (= (get-in rich [:values :rgb :intensity]) (:intensity projected)))))

(defn field [type components values] {:type type :components components :values (double-array values)})

(defn caught-exception [f]
  (try (f) nil (catch Exception error error)))

(def source-a {:instance-id "a" :effect-id :color :effect-version 1 :cue-id :left})

(def source-b {:instance-id "b" :effect-id :movement :effect-version 2 :cue-id :right})

(defn sourced [source & assignments]
  {:kind :assignments :source source :assignments (vec assignments)})

(deftest contribution-failures-identify-the-current-source-and-retain-cause
  (let [good (sourced source-a (assignment :rgb :red 0.75))]
    (doseq [options [{} {:include-values? false} {:include-values? false :compact-values? true}]
            bad [(sourced source-b (assignment :rgb :red 0.5 :add))
                 (sourced source-b (assignment :missing :red 0.1))
                 (sourced source-b (assignment :rgb :red 1.1))
                 {:kind :assignments :source source-b :assignments nil}
                 {:kind :unknown :source source-b}
                 {:kind :batch :source source-b
                  :batch {:target-ids [:rgb] :outputs {:red (field :number 1 [Double/NaN])}}}
                 {:kind :batch :source source-b
                  :batch {:target-ids [:rgb] :outputs {:red (field :number 1 [0.1 0.2])}}}
                 {:kind :batch :source source-b
                  :batch {:target-ids [:rgb] :blend :add :outputs {:red (field :number 1 [0.5])}}}]]
      (let [error (caught-exception #(frame/resolve-contributions [rgb] [good bad] options))
            cause (ex-cause error)]
        (is (instance? clojure.lang.ExceptionInfo error))
        (is (identical? source-b (:effect-source (ex-data error))))
        (is (= :afterglow.render.frame/invalid-frame (:type (ex-data error))))
        (is (= (dissoc (ex-data error) :effect-source) (ex-data cause)))
        (is (= (ex-message cause) (ex-message error)))))))

(deftest exact-arithmetic-failure-retains-source-and-original-exception
  (doseq [options [{} {:include-values? false} {:include-values? false :compact-values? true}]]
    (let [blocks [(sourced source-a (assignment :moving :focus 1/3))
                  (sourced source-b (assignment :moving :focus 0.1M :add))]
          error (caught-exception #(frame/resolve-contributions [moving] blocks options))]
      (is (instance? clojure.lang.ExceptionInfo error))
      (is (instance? ArithmeticException (ex-cause error)))
      (is (= source-b (:effect-source (ex-data error))))
      (is (= (ex-data (ex-cause error)) (not-empty (dissoc (ex-data error) :effect-source)))))))

(deftest geometric-failure-follows-effective-positive-opacity-source
  (let [good-aim (assignment :moving :aim [1.0 2.0 4.0])
        bad-aim (assignment :moving :aim [1.0 2.0 3.0])
        direction (assignment :moving :direction [1.0 0.0 0.0])
        cases [[[(sourced source-a good-aim) (sourced source-b bad-aim)] source-b]
               [[(sourced source-a bad-aim) (sourced source-b direction)] source-a]
               [[(sourced source-a bad-aim) (sourced source-b (assoc good-aim :opacity 0))] source-a]
               [[(sourced source-a good-aim)
                 (sourced source-b (assoc (assignment :moving :aim [1.0 2.0 2.0]) :opacity 0.5))] source-b]
               [[(sourced source-a direction)
                 (sourced source-b (assoc (assignment :moving :direction [-1.0 0.0 0.0]) :opacity 0.5))] source-b]
               [[(sourced source-a good-aim)
                 {:kind :batch :source source-b
                  :batch {:target-ids [:moving] :outputs {:aim (field :vec3 3 [1.0 2.0 3.0])}}}] source-b]
               [[(sourced source-a good-aim) (sourced nil bad-aim)] nil]]]
    (doseq [options [{} {:include-values? false} {:include-values? false :compact-values? true}]
            [blocks expected-source] cases]
      (let [error (caught-exception #(frame/resolve-contributions [moving] blocks options))]
        (is (instance? clojure.lang.ExceptionInfo error))
        (is (= expected-source (:effect-source (ex-data error))))
        (is (= :afterglow.render.frame/invalid-frame (:type (ex-data error))))
        (is (re-find #"finite nonzero distance" (ex-message error)))))
    (doseq [options [{} {:include-values? false :compact-values? true}]
            blocks [[(sourced source-a bad-aim) (sourced source-b good-aim)]
                    [(sourced source-a (assoc bad-aim :opacity 0))]
                    [(sourced source-a good-aim) (sourced source-b (assignment :moving :direction [0 0 0]))]]]
      (let [with-source (frame/resolve-contributions [moving] blocks options)
            without-source (frame/resolve-contributions [moving] (mapv #(dissoc % :source) blocks) options)]
        (is (= (buffer-values without-source) (buffer-values with-source)))
        (is (= (:values without-source) (:values with-source)))
        (when (:compact with-source)
          (is (= (frame/project-compact (:compact without-source)) (frame/project-compact (:compact with-source)))))))))

(deftest global-render-errors-do-not-blame-effect-provenance
  (let [blocks [(sourced source-a (assignment :moving :aim [1 2 4]))]]
    (doseq [fixtures [[moving] [(assoc moving :address 0)]]
            options [{:master 2} {:previous-values {:moving {:pan Double/NaN}}}
                     {:previous-compact {:count 1 :target-order [:moving] :fields {}}}]
            mode [{} {:include-values? false :compact-values? true}]]
      (let [error (caught-exception #(frame/resolve-contributions fixtures blocks (merge options mode)))]
        (is (instance? clojure.lang.ExceptionInfo error))
        (is (not (contains? (ex-data error) :effect-source)))))))

(deftest typed-batches-preserve-layering-target-order-and-preview
  (let [b (assoc rgb :id :b :address 10)
        patch (frame/compile-patch [rgb b])
        batches [{:target-ids [:b :rgb]
                  :outputs {:color (field :vec3 3 [0.1 0.2 0.3 0.4 0.5 0.6])}}
                 {:target-ids [:rgb] :blend :max :outputs {:red (field :number 1 [0.9])}}
                 {:target-ids [:b] :blend :add :outputs {:color (field :vec3 3 [0.1 0.1 0.1])}}]
        assignments [(assignment :b :color [0.1 0.2 0.3]) (assignment :rgb :color [0.4 0.5 0.6])
                     (assignment :rgb :red 0.9 :max) (assignment :b :color [0.1 0.1 0.1] :add)]
        expected (frame/resolve-frame patch assignments {:compact-values? true})
        actual (frame/resolve-batches patch batches {:include-values? false :compact-values? true})]
    (is (= (buffer-values expected) (buffer-values actual)))
    (is (= (frame/project-compact (:compact expected)) (frame/project-compact (:compact actual))))
    (is (= (:values expected) (:values (frame/resolve-batches patch batches))))
    (is (= [0.1 0.2 0.3 0.4 0.5 0.6] (vec (get-in (first batches) [:outputs :color :values]))))))

(deftest actual-ir-batch-feeds-aim-and-focus-without-conflating-fields
  (let [plan (ir/compile-batch {:aim {:op :const :value [2.0 2.0 3.0]}
                               :focus {:op :param :key :focus}})
        data (assoc (ir/evaluate-batch plan {:params {:focus 0.75}} [(:position moving)]) :target-ids [:moving])
        expected (frame/resolve-frame [moving] [(assignment :moving :aim [2.0 2.0 3.0]) (assignment :moving :focus 0.75)])
        actual (frame/resolve-batches [moving] [data] {:include-values? false :compact-values? true})
        projected (first (frame/project-compact (:compact actual)))]
    (is (= (buffer-values expected) (buffer-values actual)))
    (is (= [2.0 2.0 3.0] (:aim projected)))
    (is (= 0.75 (:focus projected)))
    (is (= [1.0 0.0 0.0] (:direction projected)))))

(deftest typed-batches-reject-invalid-inputs-before-returning-output
  (doseq [batch [{:target-ids [:unknown] :outputs {:red (field :number 1 [0.1])}}
                 {:target-ids [:rgb] :count 2 :outputs {:red (field :number 1 [0.1])}}
                 {:target-ids [:rgb] :outputs {:red (field :vec3 3 [0.1 0.2 0.3])}}
                 {:target-ids [:rgb] :outputs {:red {:type :number :components 1 :values [0.1]}}}
                 {:target-ids [:rgb] :outputs {:red (field :number 1 [0.1 0.2])}}
                 {:target-ids [:rgb] :blend :max :outputs {:red (field :number 1 [-0.1])}}
                 {:target-ids [:rgb] :outputs {:red (field :number 1 [Double/NaN])}}
                 {:target-ids [:rgb] :outputs {:focus (field :number 1 [0.1])}}]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/resolve-batches [rgb] [batch] {:include-values? false}))))
  (is (thrown? clojure.lang.ExceptionInfo
               (frame/resolve-batches [rgb] [{:target-ids [:rgb] :outputs {:red (field :number 1 [0.8])}}
                                            {:target-ids [:rgb] :blend :add :outputs {:red (field :number 1 [0.8])}}]
                                      {:include-values? false}))))

(deftest mixed-contributions-preserve-interleaved-precedence
  (let [fixtures [{:id :p :universe 1 :address 1 :position [0 0 0]
                   :channels {:red 1 :green 2 :blue 3 :focus 4}}]
        batch (fn [level blend] {:kind :batch :batch {:target-ids [:p] :blend blend
                                                     :outputs {:red {:type :number :components 1 :values (double-array [level])}}}})
        blocks [(batch 0.2 :replace)
                {:kind :assignments :assignments [{:target-id :p :attribute :red :value 0.1 :blend :add}]}
                (batch 0.5 :max)
                {:kind :assignments :assignments [{:target-id :p :attribute :red :value 0.1 :blend :add}]}]
        expected (frame/resolve-frame fixtures [{:target-id :p :attribute :red :value 0.6}])]
    (doseq [options [{} {:include-values? false} {:include-values? false :compact-values? true}]]
      (is (= (mapv vec (vals (:universes expected)))
             (mapv vec (vals (:universes (frame/resolve-contributions fixtures blocks options)))))))
    (is (= 0.6 (get-in (frame/resolve-contributions fixtures blocks) [:values :p :channels :red])))
    (doseq [bad [nil [{:kind :unknown}] [{:kind :assignments :assignments nil}]
                 [{:kind :batch :batch {:target-ids [:missing] :outputs {}}}]]]
      (is (thrown? clojure.lang.ExceptionInfo (frame/resolve-contributions fixtures bad))))))

(deftest compact-history-survives-target-reordering-and-portable-save
  (let [head {:id :head :position [0 0 0] :universe 1 :address 1
              :calibration {:pan {:min-deg -540 :max-deg 540}}
              :channels {:pan [1 2] :tilt 3 :dimmer 4}}
        other (assoc head :id :other :address 10)
        initial (frame/resolve-frame [head other] [(assignment :head :pan 0.99) (assignment :other :pan 0.01)]
                                     {:include-values? false :compact-values? true})
        assignments [(assignment :head :direction [0 0 1]) (assignment :other :direction [0 0 1])]
        rich-history (frame/portable-frame initial)
        compact-result (frame/resolve-contributions [other head]
                                                     [{:kind :assignments :assignments assignments}]
                                                     {:previous-compact (:compact initial)})
        rich-result (frame/resolve-frame [other head] assignments {:previous-values (:values rich-history)})]
    (is (= (:values rich-result) (:values compact-result)))
    (is (> (get-in compact-result [:values :head :pan]) 0.5))
    (is (< (get-in compact-result [:values :other :pan]) 0.5))
    (is (= [:head :other] (:target-order rich-history)))
    (is (= 0.99 (get-in rich-history [:values :head :pan])))
    (is (every? #(and (integer? %) (<= 0 % 255)) (get-in rich-history [:universes 1])))
    (is (not (contains? rich-history :compact)))
    (is (= #{:head :other} (set (keys (:values (frame/portable-frame (assoc initial :values {:head {:pan 0.9}})))))))
    (is (thrown? clojure.lang.ExceptionInfo (frame/portable-frame (dissoc initial :compact))))))

(deftest packed-axis-defaults-remain-movement-history-after-zero-opacity
  (let [head {:id :head :position [0 0 0] :universe 1 :address 1
              :calibration {:pan {:min-deg -270 :max-deg 270}}
              :channels {:pan [1 2] :tilt [3 4]}}
        other (assoc head :id :other :address 10)
        aim [(assignment :head :aim [1.0 0.0 (- (Math/sqrt 3.0))])]
        before (frame/resolve-frame [head other] aim {:compact-values? true})
        off (frame/resolve-frame [head other]
                                 (conj (mapv #(assoc % :opacity 0.0) aim) (assignment :other :pan 0.98))
                                 {:previous-values (:values before) :compact-values? true})
        assignments (conj aim (assignment :other :aim [1.0 0.0 (- (Math/sqrt 3.0))]))
        rich (frame/resolve-frame [other head] assignments {:previous-values (:values off)})
        compact (frame/resolve-frame [other head] assignments {:previous-compact (:compact off)})]
    (is (not (contains? (get-in off [:values :head]) :pan)))
    (is (= 0.0 (get-in off [:values :head :channels :pan])))
    (is (= [0 0 0 0] (bytes-at off 1 1 2 3 4)))
    (is (= (:values rich) (:values compact)))
    (is (= (mapv vec (vals (:universes rich))) (mapv vec (vals (:universes compact)))))
    (is (near? (/ 1.0 9.0) (get-in rich [:values :head :pan])))
    (is (> (get-in rich [:values :other :pan]) 0.5))
    (testing "explicit top-level movement overrides channel history and compact history"
      (let [explicit (frame/resolve-frame [head] aim
                       {:previous-values {:head {:pan 0.98 :channels {:pan 0.0 :tilt 0.0}}}
                        :previous-compact (:compact off)})]
        (is (> (get-in explicit [:values :head :pan]) 0.5))))
    (testing "absent axis history retains the neutral default"
      (let [absent (frame/resolve-frame [head] aim {:previous-values {:head {:channels {:dimmer 0.0}}}})
            no-history (frame/resolve-frame [head] aim)]
        (is (= (:values no-history) (:values absent)))
        (is (> (get-in absent [:values :head :pan]) 0.5))))
    (testing "defaulted channel history still validates before geometric use"
      (is (thrown? clojure.lang.ExceptionInfo
                   (frame/resolve-frame [head] aim {:previous-values {:head {:channels {:pan Double/NaN}}}}))))))

(deftest mixed-pixel-and-moving-targets-preserve-all-contribution-orders
  (let [pixel (assoc rgb :id :pixel :address 30 :channels {:red 1 :green 2 :blue 3 :white 4}
                     :rgbw-policy :extract-min)
        head (assoc moving :address 510 :rotation-deg [0 25 0]
                    :calibration {:pan {:min-deg -540 :max-deg 540}}
                    :channels {:pan [1 2] :tilt [3 4] :focus [5 6] :zoom 7
                               :red 8 :green 9 :blue 10 :white 11 :dimmer 12})
        other (assoc pixel :id :other :address 50)
        fixtures [pixel head other]
        history (frame/resolve-frame [other head pixel] [(assignment :moving :pan 0.98)]
                                     {:include-values? false :compact-values? true})
        color-values (double-array [0.25 0.125 0.5 0.125 0.25 0.5 0.25 0.125 0.5])
        first-batch {:kind :batch :batch {:target-ids [:other :moving :pixel]
                                          :outputs {:color {:type :vec3 :components 3 :values color-values}
                                                    :white (field :number 1 [0.125 0.125 0.125])}}}
        base [{:kind :assignments :assignments [(assignment :moving :pan 0.0)]}
              first-batch
              {:kind :assignments :assignments [(assignment :pixel :red 0.5)
                                                (assignment :moving :focus 0.25)
                                                (assignment :moving :color [0.125 0.125 0.125] :add)]}
              ;; Repeated target IDs must retain each target's row order.
              {:kind :batch :batch {:target-ids [:moving :pixel :moving :pixel]
                                    :blend :add :opacity 0.5
                                    :outputs {:red (field :number 1 [0.125 0.125 0.25 0.25])}}}]
        aim [(assignment :moving :aim [2.0 1.0 5.0]) (assignment :moving :focus 0.75)]
        geometry-blocks [{:kind :assignments :assignments aim}
                         {:kind :batch :batch {:target-ids [:moving]
                                              :outputs {:aim (field :vec3 3 [2.0 1.0 5.0])
                                                        :focus (field :number 1 [0.75])}}}]]
    (doseq [geometry geometry-blocks
            blocks [(into [geometry] base) (conj base geometry)
                    (into (conj (subvec base 0 2) geometry) (subvec base 2))]
            opts [{:master 1.0} {:master 0.4} {:blackout? true}]]
      (let [options (assoc opts :compact-values? true :previous-compact (:compact history))
            expected (frame/resolve-contributions fixtures blocks options)
            actual (frame/resolve-contributions fixtures blocks (assoc options :include-values? false))]
        (is (= (buffer-values expected) (buffer-values actual)))
        (is (= (frame/project-compact (:compact expected)) (frame/project-compact (:compact actual))))
        (is (= [:pixel :moving :other] (:target-order actual)))
        (is (nil? (:values actual)))))
    (is (= [0.25 0.125 0.5 0.125 0.25 0.5 0.25 0.125 0.5] (vec color-values)))
    (is (= 0.98 (aget ^doubles (get-in history [:compact :fields :pan :values]) 1)))))

(deftest mixed-general-targets-retain-exact-arithmetic-and-zero-opacity-defaults
  (let [pixel (assoc rgb :id :pixel :address 20)
        head (assoc moving :channels {:pan [1 2] :tilt [3 4] :focus [5 6]})
        fixtures [head pixel]
        light {:kind :batch :batch {:target-ids [:pixel]
                                    :outputs {:color (field :vec3 3 [0.5 0.25 0.125])}}}]
    (doseq [[first-value second-value] [[1/10 7/10] [0.1M 0.7M]]
            master [1.0 0.5 1/3]]
      (let [blocks [light {:kind :assignments :assignments [(assignment :moving :focus first-value)]}
                    {:kind :batch :batch {:target-ids [:moving] :opacity 1/2
                                          :outputs {:pan (field :number 1 [0.75])}}}
                    {:kind :assignments :assignments [(assignment :moving :focus second-value :add)]}]
            expected (frame/resolve-contributions fixtures blocks {:master master :compact-values? true})
            actual (frame/resolve-contributions fixtures blocks {:master master :include-values? false :compact-values? true})]
        (is (= [204 204] (bytes-at actual 1 5 6)))
        (is (= (buffer-values expected) (buffer-values actual)))
        (is (= (frame/project-compact (:compact expected)) (frame/project-compact (:compact actual))))))
    (let [blocks [light {:kind :assignments :assignments [(assoc (assignment :moving :aim [1 2 4]) :opacity 0)]}]
          expected (frame/resolve-contributions fixtures blocks {:compact-values? true})
          actual (frame/resolve-contributions fixtures blocks {:include-values? false :compact-values? true})
          saved (buffer-values actual)
          next-frame (frame/resolve-contributions fixtures [] {:include-values? false :compact-values? true})]
      (is (= (buffer-values expected) saved))
      (is (= (frame/project-compact (:compact expected)) (frame/project-compact (:compact actual))))
      (is (not (contains? (first (frame/project-compact (:compact actual))) :aim)))
      (aset-byte ^bytes (get-in next-frame [:universes 1]) 19 (byte 42))
      (aset-double ^doubles (get-in next-frame [:compact :fields :intensity :values]) 1 0.125)
      (is (= saved (buffer-values actual)))
      (is (= 1.0 (aget ^doubles (get-in actual [:compact :fields :intensity :values]) 1))))))

(deftest mixed-general-and-dense-inputs-validate-both-partitions
  (let [fixtures [moving (assoc rgb :address 20)]
        geometry {:kind :assignments :assignments [(assignment :moving :aim [1 2 4])]}]
    (doseq [bad [{:kind :batch :batch {:target-ids [:rgb] :outputs {:red (field :number 1 [Double/NaN])}}}
                {:kind :batch :batch {:target-ids [:moving] :outputs {:focus (field :number 1 [1.01])}}}
                {:kind :batch :batch {:target-ids [:moving] :outputs {:direction (field :vec3 3 [Double/NaN 1 1])}}}
                {:kind :assignments :assignments [(assignment :unknown :direction [1 0 0])]}
                {:kind :assignments :assignments [(assignment :rgb :red 1.1)]}
                {:kind :assignments :assignments [(assignment :moving :focus 0.8) (assignment :moving :focus 0.8 :add)]}]]
      (doseq [options [{} {:include-values? false} {:include-values? false :compact-values? true}]]
        (is (thrown? clojure.lang.ExceptionInfo (frame/resolve-contributions fixtures [geometry bad] options)))))))

(deftest general-typed-rows-preserve-first-error-and-opacity-rules
  (let [fixtures [(assoc moving :id :left) (assoc moving :id :right :address 30)]
        patch (frame/compile-patch fixtures)
        geometry {:kind :assignments :assignments [(assignment :left :aim [1 2 4])
                                                    (assignment :right :aim [2 3 5])]}
        render #(frame/resolve-contributions patch [geometry %1]
                                            {:include-values? %2 :compact-values? true})
        batch (fn [ids opacity outputs]
                {:kind :batch :source source-a
                 :batch {:target-ids ids :blend :replace :opacity opacity :outputs outputs}})]
    (doseq [[focus expected-attribute] [[[0.5 1.5 0.7] :pan] [[1.5 0.5 0.7] :focus]]]
      ;; Scalar zero opacity still validates a write. The first row wins over a
      ;; lexically earlier column at a later row.
      (let [block (batch [:right :left :right] 0.0
                         {:pan (field :number 1 [1.25 0.5 0.5])
                          :focus (field :number 1 focus)})
            reference (caught-exception #(render block true))
            error (caught-exception #(render block false))]
        (is (= (ex-message reference) (ex-message error)))
        (is (= (ex-data reference) (ex-data error)))
        (is (= (ex-data (ex-cause reference)) (ex-data (ex-cause error))))
        (is (identical? source-a (:effect-source (ex-data error))))
        (is (= {:target-id :right :attribute expected-attribute :blend :replace
                :value (if (= expected-attribute :pan) 1.25 1.5) :opacity 0.0}
               (:assignment (ex-data error))))))
    (let [block (assoc (batch [:right :left] 1.0 {:focus (field :number 1 [1.5 0.75])})
                       :native-layer {:id :mask :member 0 :target-weights {:right 0.0 :left 0.5}})
          reference (render block true)
          actual (render block false)]
      ;; A zero row mask excludes its assignment before value validation.
      (is (= (buffer-values reference) (buffer-values actual)))
      (is (= (frame/project-compact (:compact reference)) (frame/project-compact (:compact actual))))
      (is (= 0.375 (:focus (first (frame/project-compact (:compact actual)))))))))

(deftest explicit-physical-footprints-reserve-sparse-and-cross-universe-gaps
  (let [sparse {:id :sparse :universe 1 :address 1 :channels {:dimmer [1 4]}}
        gap {:id :gap :universe 1 :address 2 :channels {:dimmer 1}}
        crossing {:id :crossing :universe 1 :address 511 :footprint 4 :channels {:dimmer 1}}
        reserved {:id :reserved :universe 2 :address 2 :channels {:dimmer 1}}]
    (is (empty? (frame/validate-patch [sparse gap])) "Absent footprint preserves actual-channel ownership")
    (is (seq (frame/validate-patch [(assoc sparse :footprint 4) gap])))
    (is (seq (frame/validate-patch [crossing reserved])) "Unmapped bytes in next universe remain physically owned")
    (is (empty? (frame/validate-patch [crossing (assoc reserved :address 3)])))
    (doseq [footprint [nil 0 -1 2.5 3]]
      (is (seq (frame/validate-patch [(assoc sparse :footprint footprint)]))))
    (is (seq (frame/validate-patch [(assoc crossing :universe Integer/MAX_VALUE)])))
    (is (empty? (frame/validate-patch [(assoc crossing :address 1 :footprint Integer/MAX_VALUE)]))
        "Reservation validation uses intervals, not a per-channel allocation")))


(deftest empty-physical-frame-has-a-portable-save-shape
  (is (= {:target-order [] :values {} :universes {}}
         (frame/portable-frame (frame/resolve-frame [] [] {:include-values? false})))))

(deftest compositing-opacity-respects-blend-precedence-and-zero-skips-attributes
  (let [base [(assignment :rgb :color [0.8 0.4 0.2])]
        lower (frame/resolve-frame [rgb] base)
        hidden (frame/resolve-frame [rgb] (conj base (assoc (assignment :rgb :color [0 1 1]) :opacity 0)))
        mixed (frame/resolve-frame [rgb] (conj base (assoc (assignment :rgb :color [0 0.8 1]) :opacity 0.25)))
        maxed (frame/resolve-frame [rgb] (conj base (assoc (assignment :rgb :color [0 0.8 1] :max) :opacity 0.25)))
        added (frame/resolve-frame [rgb] (conj base (assoc (assignment :rgb :color [0.8 0.4 0.4] :add) :opacity 0.25)))]
    (is (= (:values lower) (:values hidden)))
    (is (every? true? (map near? [0.6 0.5 0.4] (get-in mixed [:values :rgb :emitted-color]))))
    (is (every? true? (map near? [0.8 0.5 0.4] (get-in maxed [:values :rgb :emitted-color]))))
    (is (every? true? (map near? [1.0 0.5 0.3] (get-in added [:values :rgb :emitted-color]))))
    (doseq [opacity [-1 2 Double/NaN nil]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (frame/resolve-frame [rgb] [(assoc (assignment :rgb :red 1) :opacity opacity)]))))))

(deftest typed-and-map-opacity-match-general-and-dense-rendering-with-owned-buffers
  (let [source (double-array [0.2 0.8 0.4])
        batch {:target-ids [:rgb] :opacity 0.5 :blend :replace
               :outputs {:color {:type :vec3 :components 3 :values source}}}
        blocks [{:kind :assignments :assignments [(assignment :rgb :color [0.6 0.2 0.4])]}
                {:kind :batch :batch batch}
                {:kind :assignments :assignments [(assoc (assignment :rgb :color [0.8 0 0] :add) :opacity 0.25)]}]
        rich (frame/resolve-contributions [rgb] blocks)
        dense (frame/resolve-contributions [rgb] blocks {:include-values? false :compact-values? true})
        exact (frame/resolve-contributions [rgb] (assoc-in blocks [1 :batch :opacity] 1/2)
                                           {:include-values? false})]
    (is (= [153 128 102] (bytes-at rich 1 1 2 3)))
    (is (= (bytes-at rich 1 1 2 3) (bytes-at dense 1 1 2 3) (bytes-at exact 1 1 2 3)))
    (is (= [0.2 0.8 0.4] (vec source)))
    (is (= [153 128 102] (bytes-at (frame/resolve-frame [rgb]
                                                     [(assignment :rgb :color [0.6 0.2 0.4])
                                                      (assoc (assignment :rgb :color [0.2 0.8 0.4]) :opacity 0.5)
                                                      (assoc (assignment :rgb :color [0.8 0 0] :add) :opacity 0.25)]
                                                     {:include-values? false}) 1 1 2 3)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/resolve-batches [rgb] [(assoc batch :opacity Double/NaN)])))
    (is (= [0 0 0] (bytes-at (frame/resolve-batches [rgb] [(assoc batch :opacity 0)]
                                                 {:include-values? false}) 1 1 2 3)))))

(deftest geometry-opacity-blends-world-targets-and-zero-does-not-change-aim
  (let [base [(assignment :moving :aim [1 2 7])]
        blended (frame/resolve-frame [moving] (conj base (assoc (assignment :moving :aim [3 2 7]) :opacity 1/2)))
        expected (frame/resolve-frame [moving] [(assignment :moving :aim [2 2 7])])
        hidden (frame/resolve-frame [moving] (conj base (assoc (assignment :moving :aim [3 2 7]) :opacity 0)))]
    (is (= (:values expected) (:values blended)))
    (is (= (:values (frame/resolve-frame [moving] base)) (:values hidden)))))

(deftest projected-pose-uses-committed-axes-at-mechanical-stops
  (let [fixture {:id :hung :universe 1 :address 1 :channels {:pan [1 2] :tilt [3 4]}
                 :rotation-deg [0 0 180] :calibration {:pan {:min-deg -30 :max-deg 30}
                                                       :tilt {:min-deg -20 :max-deg 20}}}
        frame (frame/resolve-frame [fixture] [(assignment :hung :aim [-1 -1 0])]
                                   {:compact-values? true})
        rich (get-in frame [:values :hung])
        compact (first (frame/project-compact (:compact frame)))
        pose (frame/fixture-pose fixture rich)
        expected [-0.46984631039295416 -0.3420201433256687 0.8137976813493738]]
    (is (false? (:aim-reachable? rich)))
    (is (near? 90 (:pan-deg rich)))
    (is (near? 45 (:tilt-deg rich)))
    (is (every? true? (map near? expected (:direction pose))))
    (is (= [30.0 20.0] ((juxt :pan-deg :tilt-deg) pose)))
    (is (= pose (frame/fixture-pose fixture compact)))
    (is (= pose (frame/fixture-pose fixture (select-keys rich [:channels]))))
    (is (nil? (frame/fixture-pose fixture {:pan 1.0 :aim [-1 -1 0]})))))

(deftest projected-pose-keeps-multi-turn-and-reversed-calibration
  (let [fixture {:id :wide :universe 1 :address 1 :channels {:pan 1 :tilt 2}
                 :calibration {:pan {:min-deg -270 :max-deg 270} :tilt [127.5 -127.5]}}
        angle (Math/toRadians -170.0)
        aim [(Math/sin angle) 0 (Math/cos angle)]
        rich (get-in (frame/resolve-frame [fixture] [(assignment :wide :direction aim)]
                                         {:previous-values {:wide {:pan 0.95}}}) [:values :wide])
        pose (frame/fixture-pose fixture rich)]
    (is (near? -170.0 (:pan-deg rich)))
    (is (near? 190.0 (:pan-deg pose)))
    (is (every? true? (map near? aim (:direction pose))))
    (is (near? -180.0 (:tilt-deg (frame/fixture-pose fixture {:pan 0.5 :tilt 1.0}))))))

(deftest numeric-work-is-owned-by-the-frame-and-preserved-on-effect-isolation
  (let [calls (atom [])
        good-plan (ir/compile-batch {:color {:op :param :key :wash :type :vec3}})
        evaluate (fn [group env]
                   (swap! calls conj group)
                   (if (= group :wash)
                     (ir/evaluate-batch good-plan env [[1 2 3]])
                     (throw (ex-info "Numeric dispatch failed" {:detail :test}))))
        realize (fields/frame-evaluator evaluate)
        request {:group :wash :env {:params {:wash [0.8 0.4 0.2]}} :scales {:color 0.5}}
        good {:kind :batch :source :wash-effect :batch {:target-ids [:rgb] :field-request request :opacity 0.5}}
        bad {:kind :batch :source :faulty-effect :batch {:target-ids [:rgb] :field-request {:group :bad :env {}}}}
        base {:kind :assignments :assignments [(assignment :rgb :color [0.0 0.0 1.0])]}
        retry-blocks [base good]]
    (is (empty? @calls))
    (try
      (realize [base good bad])
      (is false "Expected failure from the second effect")
      (catch clojure.lang.ExceptionInfo e
        (is (= {:detail :test :effect-source :faulty-effect} (ex-data e)))
        (is (= "Numeric dispatch failed" (.getMessage (.getCause e))))))
    (let [[unchanged materialized :as blocks] (realize retry-blocks)
          values (get-in materialized [:batch :outputs :color :values])]
      (is (identical? base unchanged))
      (is (= {:source :wash-effect :kind :batch} (select-keys materialized [:kind :source])))
      (is (= [0.4 0.2 0.1] (vec values)))
      (is (nil? (get-in materialized [:batch :field-request])))
      (is (= [51 26 140] (bytes-at (frame/resolve-contributions [rgb] blocks) 1 1 2 3)))
      (is (= [:wash :bad] @calls))
      (let [next-blocks ((fields/frame-evaluator evaluate) retry-blocks)]
        (is (not (identical? values (get-in next-blocks [1 :batch :outputs :color :values]))))
        (is (= [:wash :bad :wash] @calls))))
    (is (= request (get-in good [:batch :field-request])))))

(deftest bad-field-envelopes-and-mismatched-rigs-are-attributed
  (doseq [[ids scales] [[[:rgb] {:color Double/NaN}] [[:rgb] {:missing 0.5}] [[:rgb :extra] {}]]]
    (let [compute (fields/frame-evaluator
                   (fn [_ _] {:count 1 :outputs {:color {:type :vec3 :components 3 :values (double-array 3)}}}))
          block {:kind :batch :source :instance :batch {:target-ids ids
                                                       :field-request {:group :x :env {} :scales scales}}}]
      (try (compute [block]) (is false "Expected an attributed field error")
           (catch clojure.lang.ExceptionInfo e (is (= :instance (:effect-source (ex-data e)))))))))

(deftest named-emitters-use-dimmer-and-master-once-in-rich-and-dense-output
  (doseq [[attribute tint] {:amber [1.0 0.55 0.0] :warm-white [1.0 0.8 0.62]
                            :cold-white [0.82 0.9 1.0] :cool-white [0.82 0.9 1.0]
                            :cyan [0.0 1.0 0.8] :lime [0.55 1.0 0.06] :uv [0.0 0.0 0.0]}
          dimmer? [false true]
          blackout? [false true]]
    (let [fixture {:id :cell :address 1 :universe 0
                   :channels (cond-> {attribute 1 :gobo 2} dimmer? (assoc :dimmer 3))}
          rows [(assignment :cell attribute 0.8) (assignment :cell :dimmer 0.5) (assignment :cell :gobo 1)]
          options {:master 0.5 :blackout? blackout? :compact-values? true}
          rich (frame/resolve-frame [fixture] rows options)
          dense (frame/resolve-frame [fixture] rows (assoc options :include-values? false))
          expected (mapv #(* % (if blackout? 0.0 0.2)) tint)
          ;; A hardware dimmer receives the combined master and dimmer.
          expected-byte (cond blackout? 0 dimmer? 204 :else 51)
          compact-color (:emitted-color (first (frame/project-compact (:compact dense))))]
      (is (= [expected-byte 255 (if (and dimmer? (not blackout?)) 64 0)]
             (bytes-at rich 0 1 2 3) (bytes-at dense 0 1 2 3)))
      (is (== 0.8 (get-in rich [:values :cell :emitter-values attribute])))
      (is (every? true? (map near? expected (get-in rich [:values :cell :emitted-color]))))
      (is (every? true? (map near? expected compact-color))))))

(deftest supplemental-tints-add-to-rgbw-before-saturation-and-dimming
  (let [fixture (assoc rgb :channels {:red 1 :green 2 :blue 3 :white 4 :amber 5 :cold-white 6})
        rows [(assignment :rgb :color [0.7 0.0 0.2]) (assignment :rgb :white 0.2)
              (assignment :rgb :amber 0.6) (assignment :rgb :cold-white 0.2)]
        opts {:master 0.5 :compact-values? true}
        rich (frame/resolve-frame [fixture] rows opts)
        dense (frame/resolve-frame [fixture] rows (assoc opts :include-values? false))]
    (is (= (bytes-at rich 1 1 2 3 4 5 6) (bytes-at dense 1 1 2 3 4 5 6)))
    (doseq [row [(get-in rich [:values :rgb]) (first (frame/project-compact (:compact dense)))]]
      (is (every? true? (map near? [0.5 0.355 0.3] (:emitted-color row)))))))

(deftest typed-target-indices-handle-prefix-then-repeated-and-reordered-rows
  (let [patch (frame/compile-patch (mapv #(assoc rgb :id %1 :address %2) [:a :b :c] [1 4 7]))
        target-ids [:a :b :a :c :b]
        levels [0.2 0.4 0.6 0.8 1.0]
        batch {:target-ids target-ids :outputs {:red (field :number 1 levels)}}
        expected (frame/resolve-frame patch (mapv #(assignment %1 :red %2) target-ids levels))
        actual (frame/resolve-batches patch [batch] {:include-values? false})]
    (is (= (buffer-values expected) (buffer-values actual)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown batch target"
                         (frame/resolve-batches patch [(update batch :target-ids assoc 2 :missing)])))))


(deftest compact-reader-shares-only-selected-current-frame-values
  (let [fixtures [{:id :lamp :universe 1 :address 1 :channels {:red 1 :green 2 :blue 3}}
                  {:id :dimmer :universe 1 :address 4 :channels {:dimmer 1}}]
        frame (fn [color] (:compact (frame/resolve-frame fixtures [{:target-id :lamp :attribute :color :value color}]
                                                        {:include-values? false :compact-values? true})))
        first-frame (frame [1.0 0.0 0.0])
        plan (frame/compact-index (:target-order first-frame))
        read-first (frame/compact-reader plan first-frame [:emitted-color :aim])
        read-next (frame/compact-reader plan (frame [0.0 0.0 1.0]) [:emitted-color :aim])
        rows (frame/project-compact first-frame)]
    (is (= (mapv #(select-keys % [:id :emitted-color :aim]) rows) (mapv read-first [:lamp :dimmer])))
    (is (identical? (read-first :lamp) (read-first :lamp)))
    (is (= {:id :lamp :emitted-color [0.0 0.0 1.0]} (read-next :lamp)))
    (is (= [1.0 0.0 0.0] (:emitted-color (read-first :lamp))))
    (is (nil? (read-first :missing)))
    (is (thrown? clojure.lang.ExceptionInfo
          (frame/compact-reader (frame/compact-index [:dimmer :lamp]) first-frame [:aim])))))

(deftest covered-prefixes-retain-partial-target-fields-and-fault-order
  (let [rig (frame/compile-patch (mapv #(assoc rgb :id %1 :address %2) [:a :b :c] [1 4 7]))
        typed (fn [source ids attr values]
                {:kind :batch :source source
                 :batch {:target-ids ids :outputs {attr (field :number 1 values)}}})
        lower (typed source-a [:a :b :c] :red [0.1 0.2 0.3])
        other (typed source-a [:a :b :c] :blue [0.8 0.7 0.6])
        upper (typed source-b [:a :b] :red [0.45 0.5])
        draw #(frame/resolve-contributions rig % {:include-values? false :compact-values? true})
        prefixes (atom [])
        plan coverage/plan
        observe (fn [blocks] (let [result (plan blocks)]
                               (reset! prefixes (mapv #(get-in % [:compiled :columns 0 ::coverage/validate-prefix]) result))
                               result))
        sample (fn [blocks] (with-redefs [coverage/plan observe] (draw blocks)))
        blocks [lower other upper]
        expected (with-redefs [coverage/plan identity] (draw blocks))
        actual (sample blocks)]
    (is (= [2 nil nil] @prefixes))
    (is (= (buffer-values expected) (buffer-values actual)))
    (is (= (frame/project-compact (:compact expected)) (frame/project-compact (:compact actual))))
    (is (= [115 0 204 128 0 179 77 0 153] (apply bytes-at actual 1 (range 1 10))))
    (doseq [barrier [(assoc-in upper [:batch :opacity] 0.5)
                     (assoc-in upper [:batch :blend] :add)
                     (assoc-in upper [:batch :blend] :max)
                     (assoc-in upper [:batch :target-ids] [:b :a])]]
      (let [scene [lower barrier]]
        (is (= (buffer-values (with-redefs [coverage/plan identity] (draw scene)))
               (buffer-values (sample scene))))
        (is (every? nil? @prefixes))))
    ;; An intervening add may overflow even if a later replace hides the result.
    (let [overflow (typed source-b [:a] :red [1.0])
          scene [lower (assoc-in overflow [:batch :blend] :add) upper]]
      (is (= source-b (:effect-source (ex-data (caught-exception #(sample scene))))))
      (is (every? nil? @prefixes)))
    (let [bad (typed source-a [:a :b :c] :red [Double/NaN 0.2 0.3])
          fault (caught-exception #(sample [bad upper]))]
      (is (= source-a (:effect-source (ex-data fault))))
      (is (= 0 (:row (ex-data fault)))))
    ;; Removing/reordering the cover exposes the lower contribution immediately.
    (is (= [26 51 77] (bytes-at (sample [upper lower]) 1 1 4 7)))
    (is (= [26 51 77] (bytes-at (sample [lower]) 1 1 4 7)))))

(deftest uniform-native-tuples-and-expanded-arrays-paint-identical-fixtures
  (let [ids [:left 42 "right"]
        rig (frame/compile-patch
             (mapv (fn [i id] {:id id :universe 0 :address (inc (* i 8))
                               :position [i 2 1] :channels {:red 1 :green 2 :blue 3 :pan 4 :tilt 5 :focus 6}})
                   (range) ids))
        input (fn [uniform? targets attribute tuple]
                (let [n (count targets)
                      width (count tuple)
                      data {:type (if (= width 1) :number :vec3) :components width
                            :values (double-array (if uniform? tuple (mapcat identity (repeat n tuple))))}
                      field (if uniform? (fields/map->UniformField data) data)]
                  {:kind :batch :source source-a :batch {:target-ids targets :outputs {attribute field}}}))
        draw (fn [uniform? targets general? weights]
               (let [color (-> (input uniform? targets :color [1.2 0.25 0.15])
                               (assoc :native-layer {:id :mask :member 0 :opacity 0.8 :target-weights weights}))
                     scene (cond-> [color (input uniform? ids :focus [0.75])]
                             general? (conj (input uniform? [42] :aim [0.75 0.0 0.25])))]
                 (frame/resolve-contributions rig scene {:hdr {} :compact-values? true})))]
    (doseq [targets [ids ["right" 42 42 :left] [:left]] general? [true false]
            weights [{:left 0.0 42 0.5 "right" 1.0} (zipmap ids (repeat 1.0))]]
      (let [expanded (draw false targets general? weights)
            uniform (draw true targets general? weights)]
        (is (= (frame/portable-frame expanded) (frame/portable-frame uniform)))
        (is (= (frame/project-compact (:compact expanded)) (frame/project-compact (:compact uniform))))))
    (let [hidden (input true ids :red [Double/NaN])
          cover (input true [:left 42] :red [0.5])
          error (caught-exception #(frame/resolve-contributions rig [hidden cover] {:include-values? false}))]
      (is (= source-a (:effect-source (ex-data error))))
      (is (= 0 (:row (ex-data error)))))
    (let [field-path [:batch :outputs :red]
          ordinary (input false ids :red [0.5])
          compact (input true ids :red [0.5])]
      (doseq [invalid [(assoc-in ordinary (conj field-path :values) (double-array [0.5]))
                       (assoc-in compact (conj field-path :values) (double-array [0.1 0.2]))]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid typed batch"
                              (frame/resolve-contributions rig [invalid])))))))

(deftest scoped-emission-gains-scale-the-intended-uniform-field-rows
  (let [ids [:a :b :c] rig (frame/compile-patch (mapv #(assoc rgb :id %1 :address %2) ids [1 4 7]))
        rgb-tuple [0.25 0.125 0.0625]
        compact (fields/->UniformField :vec3 3 (double-array rgb-tuple))
        expanded (field :vec3 3 (mapcat identity (repeat 3 rgb-tuple)))
        draw (fn [field targets gain-options intrinsic?]
               (let [block (cond-> {:kind :batch :source source-a
                                    :batch {:target-ids ids :outputs {:color field}}}
                             intrinsic? (assoc :emission-gain 2.0))]
                 (frame/resolve-contributions rig [block] {:compact-values? true
                                                          :hdr (assoc gain-options :fixture-ids targets)})))]
    (doseq [targets [ids [:a] [:b] [:a :c] []]
            [settings intrinsic?] [[{:cue-gains {:left 2.0}} false]
                                   [{:instance-gains {"a" 2.0}} false]
                                   [{} true]]]
      (let [after (draw compact targets settings intrinsic?)
            before (draw expanded targets settings intrinsic?)]
        (is (= (frame/portable-frame before) (frame/portable-frame after)))
        (is (= (mapv #(if (some #{%} targets) 128 64) ids) (bytes-at after 1 1 4 7)))))
    (let [dimmer {:kind :assignments :source source-a
                  :assignments [(assignment :b :dimmer 0.5)]}
          paint (fn [field] {:kind :batch :source source-a :batch {:target-ids ids :outputs {:color field}}})
          render #(frame/resolve-contributions rig [dimmer (paint %)] {:hdr {:instance-gains {"a" 2.0}}})]
      (is (= (frame/portable-frame (render expanded)) (frame/portable-frame (render compact))))
      (is (= [128 64 128] (bytes-at (render compact) 1 1 4 7))))
    (is (= rgb-tuple (vec (:values compact))))))
