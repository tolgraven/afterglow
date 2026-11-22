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
