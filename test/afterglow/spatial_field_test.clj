(ns afterglow.spatial-field-test
  (:require [afterglow.render.frame :as frame]
            [clojure.test :refer [deftest is]]
            [afterglow.spatial :as spatial]
            [afterglow.spatial.field :as field]
            [afterglow.spatial.geometry :as geometry]
            [afterglow.spatial.shape :as shape]))

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

(deftest packed-position-admission-retains-inclusive-x-ranked-rows
  (let [a [0.0 -0.0 1.0]
        b [0.0 0.0 -1.0]
        fixtures [{:id :tie :position a}
                  {:id :x-max :position [1.0 0.0 0.0]}
                  {:id :z-after :position [0.0 0.0 (Math/nextUp 1.0)]}
                  {:id :x-min :position [-1.0 -0.0 -1.0]}
                  {:id :tie :position b}
                  {:id :y-before :position [0.0 (Math/nextDown -0.0) 0.0]}
                  {:id :y-after :position [0.0 (Math/nextUp 0.0) 0.0]}
                  {:id :x-before :position [(Math/nextDown -1.0) 0.0 0.0]}
                  {:id :x-after :position [(Math/nextUp 1.0) 0.0 0.0]}
                  {:id :z-before :position [0.0 0.0 (Math/nextDown -1.0)]}]
        bounds {:min [-1.0 -0.0 -1.0] :max [1.0 0.0 1.0]}
        rig (geometry/prepare-rig fixtures)
        large 9007199254740992N
        large-rig (geometry/prepare-rig [{:id :next :position [(inc large) 0.0 0.0]}
                                         {:id :edge :position [large 0.0 0.0]}
                                         {:id :outside :position [(+ large 2) 0.0 0.0]}])
        large-edge [(double large) 0.0 0.0]]
    (with-redefs [geometry/candidates (fn [& _] (throw (ex-info "Expected packed positions" {})))]
      (let [rows (geometry/reduce-box-candidates rig bounds conj [])]
        (is (= [:x-min :tie :tie :x-max] (mapv first rows)))
        (is (identical? a (second (nth rows 1))))
        (is (identical? b (second (nth rows 2)))))
      (is (= :x-min (geometry/reduce-box-candidates rig bounds (fn [_ [id]] (reduced id)) nil)))
      ;; The X index stores doubles, including the large integer that rounds to the edge.
      (is (= [:edge :next]
             (mapv first (geometry/reduce-box-candidates large-rig {:min large-edge :max large-edge} conj [])))))))

(deftest packed-position-weights-agree-with-an-older-unpacked-rig
  (let [later [0.5 0.25 0.0]
        fixtures [{:id :tie :position [0.5 0.0 0.0]}
                  {:id :other :position [-0.25 0.0 -0.0]}
                  {:id :tie :position later}
                  {:id :outside :position [4.0 0.0 0.0]}]
        {:keys [ids rows xs directional] :as rig} (geometry/prepare-rig fixtures)
        unpacked (geometry/->Rig ids rows xs directional)
        sphere {:shape :sphere :position [0.0 0.0 0.0] :radius 0.5 :strength 0.8
                :falloff {:inner-m 0.25 :outer-m 0.75 :curve :smoothstep}}
        box {:shape :rounded-box :position [0.0 0.0 0.0] :size [2.0 2.0 2.0] :rounding 0.3}
        bits (fn [volume rig]
               (update-vals (:weights (field/positions volume rig))
                            #(Double/doubleToRawLongBits (double %))))]
    (doseq [volume [sphere (assoc sphere :scale [2.0 0.5 1.0] :translation [0.25 0.0 0.0])
                    {:shape :difference :parts [box (assoc sphere :radius 0.25)]}]]
      (is (= (bits volume unpacked) (bits volume rig))))
    (is (= ((:weight-at (field/prepare sphere)) later)
           (get-in (field/positions sphere rig) [:weights :tie])))))

(deftest positional-admission-falls-back-for-mixed-coordinates-and-unsupported-boxes
  (let [fixtures [{:id :plain :position [0.0 0.0 0.0]}]
        sphere {:shape :sphere :position [0.0 0.0 0.0] :radius 1.0}
        mixed (into fixtures [{:id :mixed :position [0.0 1/2 0.25M]}])
        unbounded {:shape :polyhedron :planes [{:normal [1 0 0] :distance 1}]}
        disjoint {:shape :intersection :parts [sphere (assoc sphere :position [3.0 0.0 0.0])]}
        extreme (assoc sphere :scale [1.0 Double/MIN_VALUE 1.0])
        candidates geometry/candidates
        calls (atom 0)]
    (with-redefs [geometry/candidates (fn [rig bounds] (swap! calls inc) (candidates rig bounds))]
      (is (= {:plain 1.0 :mixed 1.0} (:weights (field/positions sphere mixed))))
      (is (= {:plain 1.0} (:weights (field/positions unbounded fixtures))))
      (is (empty? (:weights (field/positions disjoint fixtures))))
      (is (empty? (:weights (field/positions extreme fixtures))))
      (is (= 4 @calls)))))

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

(deftest prepared-observations-read-only-needed-optical-rows
  (let [spot {:id :spot :position [0 0 0] :direction [0 0 1] :beam-angle 12 :channels {:red 1}}
        rig (spatial/prepare-rig [spot])
        read-ids (atom [])
        observations (assoc (field/prepare-observations {:range-m 9}) :values
                            (fn [id] (swap! read-ids conj id) {:emitted-color [0.5 0 0]}))
        volume {:shape :sphere :radius 0.1 :position [0 0 3]}]
    (is (= {} (:weights (field/sample volume rig observations))))
    (is (empty? @read-ids))
    (is (= {:spot 0.5} (:weights (field/sample (assoc volume :selection #{:beam}) rig observations))))
    (is (= [:spot] @read-ids))))

(deftest frame-sampler-shares-emissions-and-keeps-frame-and-selection-boundaries
  (let [spot {:id :spot :position [0 0 0] :direction [0 0 1] :beam-angle 12 :channels {:red 1}}
        mover {:id :mover :position [1 0 0] :channels {:red 1 :pan 2 :tilt 3}}
        fixtures [spot mover]
        rig (field/prepare-rig fixtures)
        volume {:shape :sphere :position [0 0 3] :radius 0.4}
        values {:spot {:emitted-color [0.7 0.2 0]} :mover {:emitted-color [0 0 0]}}
        reads (atom [])
        settings (field/prepare-observations {:range-m 8 :extinction-per-m 0.04})
        sample (field/sampler rig (assoc settings :values #(do (swap! reads conj %) (get values %))))]
    (is (= (field/positions volume rig) (sample volume)))
    (is (empty? @reads))
    (doseq [selection [#{:beam} #{:aimable :beam} #{:position :beam}]]
      (let [field (assoc volume :selection selection)]
        (is (= (field/sample field rig (assoc settings :values values)) (sample field)))))
    (is (= [:spot :mover] @reads))
    (let [dark (field/sampler rig (assoc settings :values {}))
          field (assoc volume :selection #{:beam})]
      (is (pos? (get-in (sample field) [:weights :spot])))
      (is (empty? (:weights (dark field)))))))

(deftest compact-observations-share-real-frame-emission-by-fixture-id
  (let [fixed {:id :fixed :universe 1 :address 1 :channels {:red 1}
               :direction [0 0 1] :position [0 0 0] :beam-angle 20}
        moving (assoc fixed :id :moving :address 10 :channels {:red 1 :pan 2 :tilt 3})
        gated (assoc fixed :id :gated :address 20 :channels {:red 1 :shutter 2})
        fixtures [fixed moving gated]
        rows (mapv (fn [id v] {:target-id id :attribute :red :value v})
                   [:fixed :moving :gated] [0.25 0.5 0.75])
        compact (:compact (frame/resolve-frame (vec (reverse fixtures)) rows {:compact-values? true}))
        index (frame/compact-index (:target-order compact))
        volume {:shape :sphere :position [0 0 3] :radius 0.5}
        reads (atom [])
        reader frame/compact-reader
        tracked (fn [index compact attributes]
                  (let [get-row (reader index compact attributes)]
                    (fn [id] (swap! reads conj id) (get-row id))))
        opts (with-redefs [frame/compact-reader tracked] (field/compact-observations {} index compact))
        rig (field/prepare-rig fixtures)
        sample (field/sampler rig opts)
        full (field/sampler rig {:values (reader index compact (keys (:fields compact)))})]
    (sample (assoc volume :selection #{:position}))
    (is (empty? @reads))
    (doseq [mode [#{:beam} #{:aimable} #{:beam :position :aimable}]]
      (let [field (assoc volume :selection mode)]
        (is (= (full field) (sample field)))))
    (is (= [:moving :gated] @reads))
    (is (= 0.25 (get-in (sample (assoc volume :selection #{:beam})) [:weights :fixed])))
    ;; Replacing the source on the next frame must discard the previous compact reader.
    (is (empty? (:weights ((field/sampler rig (assoc opts :values {}))
                           (assoc volume :selection #{:beam})))))))

(deftest rig-range-certificate-uses-compact-emission-at-the-inclusive-boundary
  (let [lamp {:id :lamp :universe 1 :address 1 :channels {:red 1}
              :position [0.0 0.0 0.0] :direction [0 0 1] :lens-radius-m 0.0}
        compact (:compact (frame/resolve-frame [lamp] [{:target-id :lamp :attribute :red :value 0.75}]
                                               {:compact-values? true}))
        index (frame/compact-index (:target-order compact))
        options (field/compact-observations {:range-m 4.0} index compact)
        sample (field/sampler [lamp] options)
        volume {:shape :sphere :position [0.0 0.0 5.0] :radius 1.0 :selection #{:beam}}
        range-check (ns-resolve 'afterglow.spatial.beam 'within-range-of-box?)
        calls (atom 0)
        ordinary (var-get range-check)]
    (with-redefs-fn {range-check (fn [origin bounds range-m]
                                   (swap! calls inc)
                                   (ordinary origin bounds range-m))}
      #(do (is (= {:lamp 0.75} (:weights (sample volume))))
           (is (zero? @calls))
           (is (empty? (:weights (sample (assoc volume :position [0.0 0.0 5.000000001])))))
           (is (= 1 @calls))))))

(deftest rig-range-certificate-leaves-unsupported-apertures-to-ordinary-selection
  (let [lamp {:id :lamp :channels {:red 1} :position [0 0 0] :direction [0 0 1]}
        volume {:shape :sphere :position [0 0 5] :radius 1 :selection #{:beam}}
        options {:range-m 4.0 :values {:lamp {:emitted-color [0.75 0 0]}}}
        sample (field/sampler [(assoc lamp :lens-radius-m -0.5)] options)
        bogus [(assoc lamp :lens-radius-m "invalid")]]
    (is (empty? (:weights (sample volume))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid beam angle or lens radius"
                          (sample (assoc volume :position [0 0 2]))))
    (is (empty? (:weights ((field/sampler bogus (dissoc options :values)) volume))))
    (is (thrown? ClassCastException ((field/sampler bogus options) volume)))))

(deftest compact-emission-falls-back-to-per-frame-direction-and-deferred-validation
  (let [fixture {:id :lamp :universe 1 :address 1 :channels {:red 1}
                 :position [0 0 0] :direction [0 0 1] :beam-angle 20}
        compact (:compact (frame/resolve-frame [fixture] [{:target-id :lamp :attribute :red :value 1}]
                                               {:compact-values? true}))
        fields (:fields compact)
        index (frame/compact-index (:target-order compact))
        volume {:shape :sphere :position [0 0 1] :radius 0.2 :selection #{:beam}}
        from (fn [patch compact] (field/sampler [patch] (field/compact-observations {:range-m 2} index compact)))
        lamp (fn [compact] (get-in ((from fixture compact) volume) [:weights :lamp]))
        bad (assoc fixture :beam-angle 180)
        update-field (fn [key values] (assoc-in compact [:fields key :values] (double-array values)))
        no-rgb (assoc-in compact [:fields :emitted-color :valid] (boolean-array [false]))]
    (is (= 1.0 (lamp compact)))
    (is (nil? (lamp no-rgb)))
    (is (nil? (lamp (update-field :emitted-color [0.25 ##NaN 0.5]))))
    (is (= 1.0 (lamp (update-field :emitted-color [2.0 -0.2 0.5]))))
    (let [different (assoc-in (update-field :direction [1 0 0]) [:fields :direction :valid] (boolean-array [true]))
          without-zoom (assoc compact :fields (dissoc fields :zoom))]
      (is (nil? (lamp different)))
      (is (= (lamp compact) (lamp without-zoom))))
    (is (empty? (:weights ((from bad no-rgb) volume))))
    (is (empty? (:weights ((from bad compact) (assoc volume :position [0 0 4])))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid beam angle" ((from bad compact) volume)))))

(deftest observing-a-frame-keeps-invalid-unlit-or-distant-optics-lazy
  (let [fixture {:id :bad :position [0 0 0] :channels {:green 1} :beam-angle 180}
        volume {:shape :sphere :position [0 0 3] :selection #{:beam} :radius 0.25}
        lit (field/sampler [fixture] {:range-m 2 :values {:bad {:emitted-color [0 1 0]}}})
        dark (field/sampler [fixture] {:values {}})]
    (is (empty? (:weights (lit volume))))
    (is (empty? (:weights (dark volume))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid beam angle"
                          (lit (assoc volume :position [0 0 1]))))))

(deftest clipped-and-occluded-radial-maxima-match-field-membership
  (let [lamp {:id :lamp :position [0 0 0] :direction [0 0 1] :beam-angle 30 :lens-radius-m 0.05 :channels {:red 1}}
        volume {:shape :sphere :position [1.4 0 4] :radius 0.7
                :selection #{:beam} :falloff {:inner-m 0.2 :outer-m 0.2}}
        lit {:values {:lamp {:emitted-color [1 0 0]}}}
        weight #(get-in (field/sample volume [lamp] (merge lit %)) [:weights :lamp])]
    (is (pos? (weight {})))
    (is (nil? (weight {:range-m 1})))
    (is (nil? (weight {:surfaces [{:id :wall :point [0 0 2] :normal [0 0 1]}]})))))

(deftest receiver-planes-preserve-contacts-on-edges-and-through-openings
  (let [fixture {:id :spot :position [0 1 0] :direction [0 0 1]
                 :beam-angle 12 :lens-radius-m 0.12 :channels {:red 1}}
        volume {:shape :sphere :radius 0.15 :position [0 1 4] :selection #{:beam}}
        wall {:id :panel :point [0 1 2] :normal [0 0 -2] :size [2 2]}
        weight (fn [surfaces]
                 (let [observe (field/prepare-observations
                                {:surfaces surfaces :values {:spot {:emitted-color [0.8 0 0]}}})]
                   (get-in ((field/sampler [fixture] observe) volume) [:weights :spot])))]
    (doseq [clear [[] [(assoc wall :point [0 1 0])] [(assoc wall :point [0 1 5])]
                   [(assoc wall :point [3 1 2])]
                   [(assoc wall :point [-3 1 2]) (assoc wall :point [3 1 2])]]]
      (is (= 0.8 (weight clear)) (str clear)))
    (doseq [blocked [[wall] [(assoc wall :normal [1.0e-7 0 -1])]
                     [(assoc wall :point [6 1 2]) wall]
                     [(assoc wall :point [0 1 0]) wall (assoc wall :point [0 1 5])]]]
      (is (nil? (weight blocked)) (str blocked)))))

(deftest scaled-feather-bounds-contain-every-positive-sampled-distance
  (let [sphere {:shape :sphere :position [0 0 0] :radius 1 :scale [3 1 1]}
        outer {:falloff {:outer-m 1.0} :selection #{:position :beam}}
        nested {:shape :union :parts [sphere] :scale [2 1 1]}
        ray {:id :ray :position [4.5 0 -2] :direction [0 0 1] :beam-angle 0.01 :channels {:red 1}}
        fixture {:id :inside-feather :position [4.5 0 0]}
        pair [fixture ray]]
    (doseq [[where volume] [[[4.5 0 0] sphere] [[9 0 0] nested]
                            [[9 1 0] {:shape :ball :position [0 1 0] :radius 0.1 :geometry nested}]]]
      (let [v (merge volume outer)
            {weight :weight-at} (field/prepare v)]
        (is (= 0.5 (weight where)))
        (is (= {:inside-feather 0.5} (:weights (field/positions v [(assoc fixture :position where)]))))))
    (let [v (merge sphere outer)
          result (field/sample v pair {:values {:ray {:emitted-color [1.0 0 0] :direction [0 0 1]}}})]
      (is (pos? (get-in result [:weights :ray] 0.0))))))

(deftest all-visible-native-emitter-channels-support-default-beam-selection
  (let [housing {:id :lamp :position [0 0 0] :universe 0 :address 1}
        volume {:shape :sphere :position [0 0 2] :radius 0.2 :selection #{:beam}}]
    (doseq [attr [:green :blue :white :amber :warm-white :cold-white :cool-white :cyan :lime]]
      (let [fixture (assoc housing :channels {attr 1})
            output (frame/resolve-frame [fixture] [{:target-id :lamp :attribute attr :value 1.0}])]
        (is (pos? (get-in (field/sample volume [fixture] output) [:weights :lamp] 0)) (name attr))))
    (is (empty? (:directional (spatial/prepare-rig [(assoc housing :channels {:uv 1})]))))))

(deftest profiled-gates-use-committed-coarse-dmx-in-rich-and-compact-frames
  (let [volume {:shape :sphere :position [0 0 2] :radius 0.2 :selection #{:beam}}
        closed [{:type :shutter-closed :start 0 :end 10}]]
    (doseq [gate [:shutter :strobe]
            [spec closed-level open-level] [[{:offset 2 :functions closed} 0.0 0.5]
                                            [{:offset 2 :inverted-from 0 :functions closed} 1.0 0.0]
                                            [{:offset 2 :fine-offset 3 :functions closed} (/ 10.7 255) 0.5]]]
      (let [lamp {:id :lamp :position [0 0 0] :universe 0 :address 1 :channels {:green 1 gate spec}}
            rig (spatial/prepare-rig [lamp])]
        (doseq [[open? value] [[false closed-level] [true open-level]]]
          (let [rows [{:target-id :lamp :attribute :green :value 1.0}
                      {:target-id :lamp :attribute gate :value value}]
                full (frame/resolve-frame [lamp] rows)
                lean (frame/resolve-contributions [lamp] [{:kind :assignments :assignments rows}]
                                                  {:include-values? false :compact-values? true})
                compact (:compact lean)
                reader (frame/compact-reader (frame/compact-index (:target-order compact)) compact [:emitted-color gate])]
            (is (pos? (second (get-in full [:values :lamp :emitted-color]))))
            (doseq [values [(:values full) {:lamp (first (frame/project-compact compact))} reader]]
              (is (= open? (contains? (:weights (field/sample volume rig {:values values})) :lamp))
                  (pr-str [gate spec value])))))))))

(deftest fixed-mount-retains-live-directivity-and-zoom
  (let [spot {:id :strip :position [0 0 0] :direction [0 0 1] :channels {:red 1}
              :zoom-range-deg [4 80] :lens-radius-m 0.05}
        rig (spatial/prepare-rig [spot])
        volume {:shape :sphere :radius 0.1 :position [2 0 4] :selection #{:beam}}
        red {:emitted-color [0.8 0 0]}
        weight (fn [frame] (get-in (field/sample volume rig {:values {:strip frame}}) [:weights :strip]))]
    (is (identical? rig (spatial/prepare-rig rig)))
    (is (nil? (weight red)))
    (is (= 0.8 (weight (assoc red :zoom 1.0))))
    (is (= 0.8 (weight (assoc red :channels {:zoom 1.0}))))
    (is (= 0.8 (weight (assoc red :pose {:direction [2 0 4]}))))
    (is (= 0.8 (weight (assoc red :direction [2 0 4]))))
    (is (nil? (weight (assoc red :direction [2 0 4] :shutter-open? false))))
    (is (nil? (weight red)))))

(deftest fixed-mount-beam-errors-occur-only-when-lit
  (let [rig (spatial/prepare-rig [{:id :bad :channels {:red 1} :beam-angle 180}])
        volume {:shape :sphere :position [0 0 2] :radius 1 :selection #{:beam}}]
    (is (empty? (:weights (field/sample volume rig {}))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid beam angle"
                          (field/sample volume rig {:values {:bad {:emitted-color [1 1 1]}}})))))

(deftest compiled-sphere-distances-agree-with-the-inverse-transform
  (doseq [kind [:sphere :ball]
          scale [[1 1 1] [2.5 2.5 2.5] [1/8 2 1.25]]
          radius [0 2.25]]
    (let [local {:shape kind :radius radius :position [1.5M -2 3]}
          world (assoc local :scale scale :translation [1/4 3.0 -1.0])
          sphere (shape/prepare local)
          transform (shape/coordinates world (:bounds sphere))
          projected (shape/prepare world)
          at-edge ((:forward transform) [(+ 1.5 radius) -2 3])
          points [[0 0 0] [2/3 1M -5] at-edge
                  (update at-edge 0 #(Math/nextDown (double %)))
                  (update at-edge 0 #(Math/nextUp (double %)))]]
      (doseq [p points]
        (let [original ((:inverse transform) p)]
          (is (== (* (:min-scale transform) ((:distance sphere) original))
                  ((:distance projected) p)))
          (is (= ((:inside? sphere) original) ((:inside? projected) p))))))))

(deftest decimal-points-at-a-transformed-hard-edge
  (let [volume {:shape :sphere :radius 0.1M :position [0.3M 0 0]}
        scaled (assoc volume :scale [1 1 1])
        local (shape/prepare volume)
        world (shape/prepare scaled)
        inverse (:inverse (shape/coordinates scaled (:bounds local)))]
    (is ((:inside? local) [0.4M 0 0]))
    (doseq [x [0.3999999999999999M 0.4M 0.4000000000000001M]]
      (let [point [x 0 0]
            local-point (inverse point)]
        (is (== ((:distance local) local-point) ((:distance world) point)))
        (is (= ((:inside? local) local-point) ((:inside? world) point)))))))

(deftest spherical-samples-retain-distance-and-falloff-precision
  (let [center [0.25 -0.5 1.75]
        radius 2.25
        distances [0.0 (Math/nextDown 1.75) 1.75 (Math/nextUp 1.75)
                   2.1 2.25 (Math/nextDown 3.0) 3.0 (Math/nextUp 3.0)]
        points (into [[1/3 1/7 2/9] [0.125M 1.25M 2.3M] [2 1 1]]
                     (map (fn [d] [(+ 0.25 d) -0.5 1.75])) distances)]
    (doseq [curve [:linear :smoothstep]
            [inner outer] [[0.0 0.0] [0.5 0.75] [0.0 0.75] [1/2 3/4]]
            strength [0.8 -0.0]
            :let [spec {:shape :sphere :radius radius :strength strength :position center
                        :falloff {:curve curve :inner-m inner :outer-m outer}}
                  sphere (field/prepare spec)
                  ;; A one-child union exercises the general signed-distance evaluator.
                  generic (field/prepare (assoc spec :shape :union :parts [spec]))]]
      (doseq [point points]
        (is (= (Double/doubleToRawLongBits ((:weight-at generic) point))
               (Double/doubleToRawLongBits ((:weight-at sphere) point)))
            (str [curve inner outer strength point])))
      (doseq [d distances
              :let [delta (- d radius)
                    phase (cond (<= delta (- inner)) 1.0 (>= delta outer) 0.0
                                :else (/ (- outer delta) (+ outer inner)))
                    expected (* strength (if (= :smoothstep curve) (* phase phase (- 3 (* 2 phase))) phase))]]
        (is (= (Double/doubleToRawLongBits expected)
               (Double/doubleToRawLongBits ((get-in sphere [:radial :by-distance]) d)))))))
  ;; Exact subtraction before conversion to double matters at a large integral centre.
  (let [b 9007199254740992N
        spec {:shape :sphere :position [b 0 0] :radius 1.0}
        weights (:weights (field/positions spec [{:id :edge :position [(inc b) 0 0]}
                                                 {:id :outside :position [(+ b 2) 0 0]}]))]
    (is (= {:edge 1.0} weights))))
