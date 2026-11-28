(ns afterglow.render.hdr-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.hdr :as hdr]
            [clojure.test :refer [deftest is testing]]))

(defn rgb-head [id address xyz]
  {:id id :address address :universe 1 :position xyz :channels {:red 1 :green 2 :blue 3}})

(def rig (frame/compile-patch [(rgb-head :source 1 [0 0 0]) (rgb-head :near 4 [0 0.5 0])
                               (rgb-head :far 7 [0 0.9 0]) (rgb-head :outside 10 [0 0 2])
                               {:id :lamp :address 13 :universe 1 :position [10 0 0] :channels {:dimmer 1}}
                               {:id :utility :address 14 :universe 1 :position [0 0 0] :channels {:fog 1 :dimmer 2}}]))

(defn row [id field v] {:target-id id :attribute field :value v})

(defn block [& rows] {:kind :assignments :assignments (vec rows)})

(defn bytes-of [f] (mapv #(bit-and 255 %) (take 15 (get-in f [:universes 1]))))

(defn batch [id field values]
  (let [w (if (= field :color) 3 1)]
    {:kind :batch :batch {:target-ids [id] :outputs {field {:type (if (= w 3) :vec3 :number)
                                                        :components w :values (double-array values)}}}}))

(defn native-and-rich [blocks opts]
  (let [render #(frame/resolve-contributions rig blocks (merge opts %))
        rich (render {}) compact (render {:include-values? false :compact-values? true})
        rows (frame/project-compact (:compact compact))]
    (is (= (bytes-of rich) (bytes-of compact)))
    (is (= (mapv #(get-in rich [:values % :emitted-color]) (:target-order rig)) (mapv :emitted-color rows)))
    (bytes-of rich)))

(deftest true-excess-falls-off-with-distance-and-stays-in-the-scope
  (doseq [b [(block (row :source :color [1.21 0 0])) (batch :source :color [1.21 0 0])]]
    (let [hdr {:spill 1 :radius 1 :white-mix 0 :spill-white-mix 0 :fixture-ids [:source :near :far]}
          out (native-and-rich [b] {:hdr hdr})]
      ;; Excess is 0.21. At half a metre with linear falloff the received red is 0.105.
      (is (= [255 0 0 27 0 0 5 0 0 0 0 0 0 0 0] out))
      (is (= 13 (nth (native-and-rich [b] {:hdr (assoc hdr :falloff :quadratic)}) 3)))
      (is (= 13 (nth (native-and-rich [b] {:hdr (assoc hdr :max-excess 0.1)}) 3)))
      (is (= 0 (nth (native-and-rich [b] {:hdr (assoc hdr :fixture-ids [:source])}) 3)))
      (is (every? zero? (native-and-rich [b] {:hdr hdr :blackout? true}))))))

(deftest whitening-defaults-and-independent-tint-controls
  (let [b (block (row :source :color [0.7 0 0]) (row :near :color [0 0 0.5]))
        settings {:gain 2 :spill 1}
        render #(subvec (native-and-rich [b] {:hdr (merge settings %)}) 0 6)]
    (is (= [255 102 102 92 51 255]
           (render {}) (render {:white-mix 1 :spill-white-mix 1})))
    (is (= [255 0 0 92 51 255] (render {:white-mix 0})))
    (is (= [255 102 102 51 0 255] (render {:spill-white-mix 0})))
    (is (= [255 0 0 51 0 255] (render {:white-mix 0 :spill-white-mix 0})))
    (is (= [255 0 0 0 0 0]
           (subvec (native-and-rich [(block (row :source :color [1.4 0 0]))] {:hdr {}}) 0 6)))))

(deftest cue-gain-is-independent-of-opacity-and-applies-once
  (let [tag #(assoc % :source {:cue-id :cue :instance-id 99})
        base (tag (batch :source :color [0.6 0 0])) dim (tag (block (row :source :dimmer 0.5)))
        b [base dim (block (row :lamp :dimmer 0.6) (row :utility :dimmer 0.4) (row :utility :fog 0.8))]
        opts {:hdr {:gain 1 :source-gains {:lamp 2.0} :instance-gains {99 2.0}}}]
    (is (= [153 0 0] (subvec (native-and-rich b opts) 0 3)))
    (is (= [255 204 102] (subvec (native-and-rich b opts) 12)))
    (is (= 255 (nth (native-and-rich b {:hdr {:fixture-ids [:source] :source-gains {:lamp 2.0}}}) 12)))
    (is (= [0.6 0.0 0.0] (vec (get-in base [:batch :outputs :color :values]))))
    (is (= [255 51 51] (subvec (native-and-rich [base] {:hdr {:cue-gains {:cue 2.0}}}) 0 3)))
    (is (= [153 0 0] (subvec (native-and-rich [base] {:hdr {:cue-gains {:cue 2.0} :fixture-ids [:near]}}) 0 3)))
    (is (= [153 0 0] (subvec (native-and-rich [base] {}) 0 3))))
  (let [a (row :source :red 0.7)
        b (assoc (row :source :red 0.6) :blend :add)]
    (is (thrown? Exception (frame/resolve-frame rig [a b])))
    (is (= [255 76 76 71] (subvec (bytes-of (frame/resolve-frame rig [a b] {:hdr {:spill 1 :radius 1}})) 0 4)))
    (is (= 0 (nth (bytes-of (frame/resolve-frame rig [a b (row :source :red 0.2)] {:hdr {:spill 1}})) 3)))))

(deftest hdr-does-not-relax-other-channel-ranges
  (doseq [field [:fog :dimmer] b [(block (row :utility field 1.2)) (batch :utility field [1.2])]
          rich? [true false]]
    (is (thrown? Exception (frame/resolve-contributions rig [b] {:hdr {} :include-values? rich?}))))
  (doseq [v [-0.1 ##NaN ##Inf]]
    (is (thrown? Exception (frame/resolve-frame rig [(row :source :red v)] {:hdr {}}))))
  (doseq [s [{:radius -1} {:falloff :bad} {:gain ##NaN} {:spill 3} {:max-excess -1} {:cue-gains {:a -2}}]]
    (is (thrown? Exception (hdr/validate! s)))))

(deftest native-color-modifier-and-prepared-packing-see-the-same-highlight-once
  (let [base (assoc (block (row :source :color [0.7 0.0 0.0])) :native-layer {:id :compound :member 0})
        change (assoc (block) :native-layer {:id :compound :member 1 :targets :previous
                                              :transforms [{:attribute :color :value {:op :multiply :args [{:op :previous :attribute :color} 2.0]}}]})
        expected (native-and-rich [base change] {:hdr {:spill 1 :radius 1}})
        pending (frame/prepare-movement-frame rig [base change] {:hdr {:spill 1 :radius 1} :compact-values? true})]
    (is (= [255 102 102 92] (subvec expected 0 4)))
    (is (= expected (bytes-of ((:pack pending) {})) (bytes-of ((:pack pending) {}))))))

(deftest profiled-shutter-gates-highlight-and-rgbw-extracts-after-mapping
  (let [source (-> (rgb-head :source 1 [0 0 0])
                   (assoc :rgbw-policy :extract-min)
                   (assoc-in [:channels :white] 4)
                   (assoc-in [:channels :shutter] {:offset 5 :functions [{:type :shutter-closed :start 0 :end 10}]}))
        p (frame/compile-patch [source (rgb-head :neighbor 6 [0 0 0])])
        values [(row :source :color [1.2 0.5 0.5])]
        render (fn [rows] (subvec (bytes-of (frame/resolve-frame p rows {:hdr {:spill 1 :white-mix 0 :spill-white-mix 0}})) 0 8))]
    (is (= [128 0 0 128 0 0 0 0] (render values)))
    (is (= [128 0 0 128 255 51 0 0] (render (conj values (row :source :shutter 1)))))))

(deftest layered-native-overrides-and-large-gains-agree-across-storage-paths
  (doseq [source [(block (row :source :color [1.4 0.4 0]) (row :source :red 0.5))
                  (block (row :source :red 0.5) (row :source :blue 0.7) (row :source :dimmer 0.8))]
          gain [0 0.3 1 1.6]]
    (native-and-rich [source] {:hdr {:gain gain :radius 2 :white-mix 1.0 :spill 1.0 :spill-white-mix 0.5}}))
  (is (= [255 255 255] (subvec (native-and-rich [(block (row :source :color [2.0 0.0 0.0]))]
                                    {:hdr {:gain Double/MAX_VALUE :max-excess 1.0 :white-mix 1.0}})
                              0 3))))

(deftest one-bounce-and-patch-order-independence
  (let [fixtures [(rgb-head :a 510 [0 0 0]) (rgb-head :b 4 [0 0.5 0]) (rgb-head :c 7 [0 1.2 0])]
        rows [(row :a :color [4 0 0])]
        opts {:hdr {:radius 1 :spill 1 :max-excess 3} :master 0.5}
        run (fn [rig] (-> (frame/resolve-frame rig rows opts) :universes (update-vals vec)))
        bytes (run fixtures)]
    (is (= bytes (run (vec (reverse fixtures)))))
    (is (= 128 (bit-and 255 (nth (get bytes 1) 3))))
    ;; B is saturated from incident light and lies within range of C. Only A casts spill.
    (is (zero? (nth (get bytes 1) 6)))))

(deftest native-transform-only-cue-can-overdrive-a-prior-layer
  (let [base (assoc (block (row :source :color [0.4 0 0])) :native-layer {:id :scene :member 0})
        modifier (assoc (block) :source {:cue-id :lift}
                        :native-layer {:id :scene :member 1 :targets :previous
                                       :transforms [{:attribute :color :value {:op :previous :attribute :color}}]})
        bytes (native-and-rich [base modifier] {:hdr {:cue-gains {:lift 3.0} :spill 1 :radius 1}})]
    (is (= [255 51 51 48] (subvec bytes 0 4)))))

(deftest suppressed-edge-followers-neither-cast-spill-nor-light-up-from-it
  (let [opts {:hdr {:spill 1.0 :radius 2.0} :edge-tracking [{:leader :missing :follower :source}]}
        hidden (native-and-rich [(block (row :source :color [3.0 0 0]))] opts)
        incoming (native-and-rich [(block (row :near :color [3.0 0 0]))] opts)]
    (is (every? zero? hidden))
    (is (= [0 0 0 255] (subvec incoming 0 4)))))

(deftest packed-physical-rgbw-matches-the-reference-emitter-mix
  (doseq [policy [:none :extract-min]]
    (let [rgbw (assoc-in (rgb-head :source 1 [0 0 0]) [:channels :white] 4)
          patch (frame/compile-patch [(assoc rgbw :rgbw-policy policy)
                                      (assoc-in (rgb-head :neighbor 5 [0 0 0]) [:channels :white] 4)])
          render (fn [rows options]
                   (let [rich (frame/resolve-frame patch rows options)
                         compact (frame/resolve-frame patch rows (assoc options :include-values? false :compact-values? true))]
                     (is (= (bytes-of rich) (bytes-of compact)))
                     (is (= (mapv #(get-in rich [:values % :emitted-color]) (:target-order patch))
                            (mapv :emitted-color (frame/project-compact (:compact compact)))))
                     (bytes-of compact)))]
      (is (= [0 0 0 255 102 102 102 0]
             (subvec (render [(row :source :white 1.4)] {:hdr {:spill 1.0 :radius 1.0 :white-mix 0 :spill-white-mix 0}}) 0 8)))
      (doseq [primary [(row :source :red 0.8) (row :source :white 0.35) (row :source :white 1.7)]
              gain [0.0 0.35 1.6]
              options [{} {:master 0.7} {:blackout? true}]]
        (render [(row :source :color [1.6 0.8 0.35]) primary (row :source :dimmer 0.6)
                 (row :neighbor :color [0.2 0.4 0.6]) (row :neighbor :white 0.15)]
                (assoc options :hdr {:gain gain :white-mix 0.7 :spill-white-mix 0.8 :spill 0.9 :radius 1.0}))))))

(deftest observed-excess-has-an-independent-lifetime-from-colored-spill
  (let [p (frame/compile-patch [(rgb-head :red 1 [0 0 0])
                                (rgb-head :near 4 [0.5 0 0])
                                {:id :mirror :position [0.5 0 0] :universe 1 :address 7 :channels {:pan 1 :tilt 2}}
                                (rgb-head :outside 9 [1.01 0 0])])
        source (block (row :red :color [1.4 0 0]))
        check (fn [blocks opts]
                (let [rich (frame/resolve-contributions p blocks opts)
                      compact (frame/resolve-contributions p blocks (assoc opts :include-values? false :compact-values? true))]
                  (is (= (bytes-of rich) (bytes-of compact)))
                  (is (= (:hdr-contacts rich) (:hdr-contacts compact)))
                  rich))]
    (is (nil? (:hdr-contacts (check [source] {:hdr {}}))))
    (let [observed (check [source] {:observe-hdr? true})]
      (is (= #{:near :mirror} (set (keys (get-in observed [:hdr-contacts :red])))))
      (is (< (abs (- 0.2 (get-in observed [:hdr-contacts :red :mirror]))) 1e-8))
      (is (= [255 0 0 0 0 0] (subvec (bytes-of observed) 0 6)))
      (doseq [spill [0 0.5 1]]
        (let [opts {:hdr {:spill spill :falloff :linear}}
              enabled (check [source] (assoc opts :observe-hdr? true))]
          (is (= (:hdr-contacts observed) (:hdr-contacts enabled)))
          (is (= (bytes-of enabled) (bytes-of (check [source] opts)))))))
    (is (= {} (:hdr-contacts (check [] {:observe-hdr? true}))))
    (is (= {} (:hdr-contacts (check [source] {:hdr {} :observe-hdr? true :master 0}))))
    (is (= {} (:hdr-contacts (check [source] {:hdr {} :observe-hdr? true :blackout? true}))))
    (let [gain [(assoc (block (row :red :color [0.7 0 0])) :emission-gain 2)]]
      (is (= (bytes-of (check gain {})) (bytes-of (check gain {:observe-hdr? true})))))
    (is (= (:hdr-contacts (frame/resolve-contributions p [source] {:observe-hdr? true}))
           (:hdr-contacts ((:pack (frame/prepare-movement-frame p [source] {:observe-hdr? true})) {}))))))

(deftest closed-shutter-cannot-drive-a-spatial-event
  (let [p (frame/compile-patch [(assoc-in (rgb-head :red 1 [0 0 0]) [:channels :shutter]
                                         {:offset 4 :functions [{:type :shutter-closed :start 0 :end 30}]})
                                (rgb-head :near 5 [0.2 0 0])])
        run #(frame/resolve-frame p [(row :red :color [2 0 0]) (row :red :shutter %)] {:observe-hdr? true})]
    (is (empty? (:hdr-contacts (run 0))))
    (is (< (abs (- 0.8 (get-in (run 1) [:hdr-contacts :red :near]))) 1e-8))))

(deftest authored-falloff-curves-are-portable-validated-data
  (testing "a two-point ramp is the linear preset, bit for bit"
    (is (== 0.375 (.invokePrim (hdr/falloff-weight [[0 1] [1 0]]) 0.625)))
    (doseq [u [0.0 0.1 0.25 0.5 0.9 0.999]]
      (is (== (.invokePrim (hdr/falloff-weight :linear) u)
              (.invokePrim (hdr/falloff-weight [[0 1] [1 0]]) u)))))
  (testing "piecewise-linear interpolation between monotone distance fractions"
    (let [f (hdr/falloff-weight [[0 1] [0.4 1] [0.6 0.25] [1 0]])]
      (doseq [[u w] [[0.0 1.0] [0.2 1.0] [0.4 1.0] [0.5 0.625] [0.6 0.25] [0.9 0.0625] [1.0 0.0]]]
        (is (< (abs (- w (.invokePrim f u))) 1e-12) (str u)))
      (is (instance? clojure.lang.IFn$DD f))))
  (testing "64 points and exact Ratio points are accepted"
    (let [stairs (vec (for [i (range 64)] [(/ i 63) (- 1 (/ i 63))]))
          f (hdr/falloff-weight stairs)]
      (is (= 64 (count stairs)))
      (is (= {:falloff stairs} (hdr/validate! {:falloff stairs})))
      (doseq [u [0.0 0.25 0.5 0.75 0.99]]
        (is (< (abs (- (- 1.0 u) (.invokePrim f u))) 1e-12))))
    (let [f (hdr/falloff-weight [[0 1] [1/3 1/2] [1 0]])]
      (is (< (abs (- 0.75 (.invokePrim f (/ 1.0 6)))) 1e-12))
      (is (< (abs (- 0.25 (.invokePrim f (/ 2.0 3)))) 1e-12))))
  (testing "rejected before any frame renders"
    (doseq [bad [[[0 1]] [[0.1 1] [1 0]] [[0 1] [0.9 0]] [[0 1] [0.5 2] [1 0]]
                 [[0 1] [0.5 0.5] [0.5 0.4] [1 0]] [[0 1] [0.6 0.5] [0.4 0.4] [1 0]]
                 [[0 ##NaN] [1 0]] [[0 1] [1 -0.1]] [[0 1 2] [1 0]] '([0 1] [1 0]) [[0 1] [1 :x]]
                 (vec (for [i (range 65)] [(/ i 64.0) 1])) [[0 1] [1/2 3/2] [1 0]]]]
      (is (thrown? Exception (hdr/validate! {:falloff bad})) (pr-str bad))
      (is (thrown? Exception (frame/resolve-frame rig [(row :source :red 1.0)] {:hdr {:falloff bad}}))))))

(deftest authored-falloff-spills-by-distance-through-rich-and-dense-paths
  (doseq [b [(block (row :source :color [1.21 0 0])) (batch :source :color [1.21 0 0])]]
    (let [hdr {:spill 1 :radius 1 :white-mix 0 :spill-white-mix 0 :fixture-ids [:source :near :far]}]
      (is (= (native-and-rich [b] {:hdr hdr})
             (native-and-rich [b] {:hdr (assoc hdr :falloff [[0 1] [1 0]])})))
      ;; Excess 0.21. Near is 0.5 of the radius away: weight 0.625, red 0.13125.
      ;; Far is 0.9 away: weight 0.0625, red 0.013125.
      (is (= [255 0 0 33 0 0 3 0 0 0 0 0 0 0 0]
             (native-and-rich [b] {:hdr (assoc hdr :falloff [[0 1] [0.4 1] [0.6 0.25] [1 0]])})))
      (is (= [255 0 0 0 0 0 5 0 0 0 0 0 0 0 0]
             (native-and-rich [b] {:hdr (assoc hdr :falloff [[0 0] [0.7 0] [0.8 0.1] [1 0.1]])}))))))

(defn- strip-pixel [i]
  (rgb-head (keyword (str "px-" i)) (inc (* 3 i)) [(* 0.1 i) 0 0]))

(deftest excess-spills-to-neighbouring-strip-pixels-by-distance
  (let [strip (frame/compile-patch (mapv strip-pixel (range 9)))
        hot (block (row :px-4 :color [1.21 0 0]))
        red #(vec (take-nth 3 (mapv (fn [b] (bit-and 255 b)) (take 27 (get-in % [:universes 1])))))
        render (fn [opts]
                 (let [rich (frame/resolve-contributions strip [hot] opts)
                       dense (frame/resolve-contributions strip [hot] (assoc opts :include-values? false :compact-values? true))]
                   (is (= (red rich) (red dense)))
                   (red rich)))
        hdr {:spill 1 :radius 0.35 :white-mix 0 :spill-white-mix 0}]
    ;; Linear weights at 0.1, 0.2 and 0.3 m are 5/7, 3/7 and 1/7 of the 0.21
    ;; excess: 0.15, 0.09 and 0.03 of red. The pixel at 0.4 m is outside.
    (is (= [0 8 23 38 255 38 23 8 0] (render {:hdr hdr})))
    (is (= [0 0 0 0 255 0 0 0 0] (render {:hdr (assoc hdr :spill 0)})))
    (is (= [0 0 0 0 255 0 0 0 0] (render {:hdr {}})) "neutral HDR only clamps")
    (testing "quadratic and authored curves fall off faster or hold at the source"
      ;; Squared weights 25/49, 9/49 and 1/49.
      (is (= [0 1 10 27 255 27 10 1 0] (render {:hdr (assoc hdr :falloff :quadratic)})))
      ;; Authored weights 1, 0.819 and 0.286: full strength out to 0.3 of the radius.
      (is (= [0 15 44 54 255 54 44 15 0]
             (render {:hdr (assoc hdr :falloff [[0 1] [0.3 1] [0.6 0.8] [1 0]])}))))
    (testing "scope limits receivers to the selected segment"
      (is (= [0 0 0 38 255 38 0 0 0]
             (render {:hdr (assoc hdr :fixture-ids [:px-3 :px-4 :px-5])}))))))

(defn- unique-curve [i] [[0 1] [(/ (inc i) 2000.0) 0.5] [1 0]])

(deftest curve-cache-is-bounded-and-a-hit-skips-revalidation
  (let [cache @#'hdr/compiled-curves
        fresh (unique-curve 999)]
    (testing "a miss at capacity evicts one curve rather than emptying the cache"
      (doseq [i (range (+ 40 hdr/max-compiled-curves))] (hdr/falloff-weight (unique-curve i)))
      (is (<= (.size cache) hdr/max-compiled-curves))
      (hdr/falloff-weight fresh)
      (is (= hdr/max-compiled-curves (.size cache)))
      (is (.containsKey cache fresh)))
    (testing "a compiled curve is valid without walking its points again"
      (with-redefs [hdr/falloff-curve? (fn [_] (throw (ex-info "structural check repeated" {})))]
        (is (= {:falloff fresh} (hdr/validate! {:falloff fresh})))
        (is (identical? (.get cache fresh) (hdr/compile! {:falloff fresh})))))))

(deftest a-frame-compiles-its-falloff-once-and-carries-it-to-every-receiver
  (let [curve [[0 1] [0.4 1] [0.6 0.25] [1 0]]
        calls (atom 0)
        weight hdr/falloff-weight
        blocks [(block (row :source :color [1.21 0 0]) (row :near :color [1.3 0 0]) (row :far :color [1.1 0 0]))]
        opts {:hdr {:spill 1 :radius 1 :falloff curve :white-mix 0 :spill-white-mix 0}}
        expected (bytes-of (frame/resolve-contributions rig blocks opts))]
    (with-redefs [hdr/falloff-weight (fn [f] (swap! calls inc) (weight f))]
      (doseq [o [opts (assoc opts :include-values? false :compact-values? true)]]
        (reset! calls 0)
        (is (= expected (bytes-of (frame/resolve-contributions rig blocks o))))
        (is (= 1 @calls) "three spilling sources share the falloff compiled at validation"))
      (reset! calls 0)
      (is (= expected (bytes-of ((:pack (frame/prepare-movement-frame rig blocks (assoc opts :compact-values? true))) {}))))
      (is (= 1 @calls)))))

(deftest blacked-out-heads-stay-dark-after-composition-and-spill
  (let [base (block (row :source :color [1.6 0 0]) (row :near :color [0 0 0.5]) (row :far :color [0 0.4 0]))
        later (block (row :near :dimmer 1.0) (row :near :color [0 1 0]))
        hdr {:spill 1 :radius 1 :white-mix 0 :spill-white-mix 0}]
    (testing "without the mask, a later write and spilled light reach the near head"
      (is (not-every? zero? (subvec (native-and-rich [base later] {:hdr hdr}) 3 6))))
    (testing "a blacked-out head is dark whatever was composed or spilled onto it"
      (let [out (native-and-rich [base later] {:hdr hdr :blackout-ids #{:near}})]
        (is (= [0 0 0] (subvec out 3 6)))
        (is (= (subvec (native-and-rich [base later] {:hdr hdr}) 0 3) (subvec out 0 3)) "The source is untouched")
        (is (pos? (nth out 7)) "The far head still receives spill")))
    (testing "a physical dimmer and its emitters both close, on the plain path too"
      (let [p (frame/compile-patch [{:id :par :address 1 :universe 1 :channels {:dimmer 1 :red 2 :green 3 :blue 4 :white 5 :strobe 6}}])
            rows [(row :par :dimmer 1.0) (row :par :color [0.5 0.4 0.3]) (row :par :white 0.6) (row :par :strobe 0.3)]
            render #(mapv (fn [b] (bit-and 255 b)) (take 6 (get-in (frame/resolve-frame p rows %) [:universes 1])))]
        (is (= [0 0 0 0 0 77] (render {:blackout-ids [:par]})) "Strobe is not emission")
        (is (= (render {}) (render {:blackout-ids [:elsewhere]})) "An unknown ID is ignored")
        (is (= (render {:blackout-ids [:par]}) (render {:blackout-ids [:par] :include-values? false})))
        (is (thrown? clojure.lang.ExceptionInfo (frame/resolve-frame p rows {:blackout-ids :par})))))))
