(ns afterglow.render.frame-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.render.ir :as ir]
            [afterglow.render.frame :as frame]))

(def rgb {:id :rgb :position [1 2 3] :universe 1 :address 1
          :channels {:red 1 :green 2 :blue 3}})
(defn assignment [id attribute value & [blend]]
  {:target-id id :attribute attribute :value value :blend (or blend :replace)})
(defn bytes-at [result universe & offsets]
  (let [buffer (get-in result [:universes universe])]
    (mapv #(bit-and 255 (aget ^bytes buffer (dec %))) offsets)))
(defn near? [a b] (< (Math/abs (double (- a b))) 1.0e-9))

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

(deftest multi-universe-coarse-fine-and-inversion
  (let [fixture {:id :head :position [0 0 0] :universe 2 :address 512
                 :channels {:pan [1 2] :dimmer {:offset 3 :inverted-from 0}}}
        half (frame/resolve-frame [fixture] [(assignment :head :pan 0.5)
                                            (assignment :head :dimmer 0.25)])
        full (frame/resolve-frame [fixture] [(assignment :head :pan 1.0)])]
    (is (= [127] (bytes-at half 2 512)))
    (is (= [128 191] (bytes-at half 3 1 2)))
    (is (= [255] (bytes-at full 2 512)))
    (is (= [0] (bytes-at full 3 1)))
    (is (= [2 3] (vec (keys (:universes half)))))))

(deftest invalid-patches-and-assignments-are-rejected
  (doseq [fixtures [[rgb rgb]
                    [(assoc rgb :address 0)]
                    [(assoc rgb :universe -1)]
                    [(assoc rgb :position [0 Double/NaN 0])]
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
    (is (= [127 128 127 128] (bytes-at forward 1 1 2 3 4)))
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
    (is (= [169 128] (bytes-at calibrated 1 1 2)))))

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
