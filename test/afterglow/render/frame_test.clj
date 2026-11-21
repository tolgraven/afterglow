(ns afterglow.render.frame-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.render.ir :as ir]
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
        (is (= [204 0] (bytes-at actual 1 5 6)))
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
