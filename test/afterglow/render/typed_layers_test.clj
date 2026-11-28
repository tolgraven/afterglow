(ns afterglow.render.typed-layers-test
  "The typed colour layer path against the general native layer path
  (tolgraven/tolglow#908): the same bytes, values and faults on every frame."
  (:require [afterglow.render.fields :as fields]
            [afterglow.render.frame :as frame]
            [afterglow.render.typed-layers :as typed]
            [clojure.test :refer [deftest is testing]]
            [thi.ng.color.core :as color])
  (:import [java.util Arrays Random]))

(def ^:private pixel-count 18)

(def fixtures
  "RGB pixels, an RGBW par with a dimmer, then two white-only heads that a
  colour filter must skip."
  (let [pixels (mapv (fn [i] {:id (keyword (str "p" i)) :universe 1 :address (inc (* 3 i))
                              :channels {:red 1 :green 2 :blue 3}}) (range pixel-count))]
    (conj pixels
          {:id :par :universe 2 :address 1 :channels {:red 1 :green 2 :blue 3 :white 4 :dimmer 5}}
          {:id :w0 :universe 2 :address 10 :channels {:white 1}}
          {:id :w1 :universe 2 :address 11 :channels {:white 1}})))

(def patch (frame/compile-patch fixtures))

(def colour-ids (conj (mapv #(keyword (str "p" %)) (range pixel-count)) :par))

(defn- color-batch [ids values & {:as options}]
  {:kind :batch :source {:effect-id (:source options :lower)}
   :batch (merge {:target-ids ids
                  :outputs {:color {:type :vec3 :components 3 :values (double-array values)}}}
                 (dissoc options :source))})

(defn- previous [& [default]] (cond-> {:op :previous :attribute :color} default (assoc :default default)))

(def ^:private incoming {:op :incoming :attribute :color})

(def ^:private field {:op :field :attribute :color})

(defn- step [value] {:attribute :color :value value})

(def programs
  "Colour-only transform programs, including chains, literal operands,
  defaults and a read without a default that faults when nothing is beneath."
  [[(step {:op :multiply :args [(previous [0.0 0.0 0.0]) incoming]})]
   [(step {:op :rotate-hue :args [(previous [0.0 0.0 0.0]) 1/6]})]
   [(step {:op :rotate-hue :args [(previous [0.0 0.0 0.0]) -0.3]})]
   [(step {:op :rotate-hue :args [field 2.5]})]
   [(step {:op :color-grade :args [(previous [0.0 0.0 0.0]) incoming]})]
   [(step {:op :color-guard :args [(previous [0.0 0.0 0.0]) incoming]})]
   [(step {:op :color-grade :args [field [0.3 0.5 0.1]]})]
   [(step {:op :color-guard :args [(previous [0.0 0.0 0.0]) incoming]})
    (step {:op :rotate-hue :args [field 0.25]})]
   [(step {:op :multiply :args [incoming 0.5]})
    (step {:op :color-grade :args [(previous [0.0 0.0 0.0]) field]})]
   [(step {:op :multiply :args [(previous) incoming]})]
   [(step {:op :multiply :args [(color/rgba 0.5 1.0 0.25) (previous [0 0 0])]})]
   ;; A literal subexpression folds through the general evaluator.
   [(step {:op :color-guard :args [(previous [0.0 0.0 0.0]) {:op :multiply :args [[0.6 0.4 0.2] 0.5]}]})]
   [(step {:op :multiply :args [{:op :multiply :args [(previous [1.0 1.0 1.0]) 0.5]} incoming]})]])

(defn- uniform-values [^Random rng n high?]
  (vec (repeatedly (* 3 n) #(let [x (.nextDouble rng)]
                              (cond (< x 0.08) 0.0
                                    (and high? (< x 0.25)) (* 3.0 x)
                                    :else x)))))

(defn- shuffled [^Random rng xs]
  (let [l (java.util.ArrayList. ^java.util.Collection xs)]
    (java.util.Collections/shuffle l rng)
    (vec l)))

(defn- pick [^Random rng xs] (nth xs (.nextInt rng (count xs))))

(defn- scenario
  "One seeded frame: lower writes, an optional direct compound, the colour
  modifier and an optional later write, with random opacities, weights,
  explicit targets, HDR gain, blackout heads and master."
  [seed]
  (let [rng (Random. seed)
        hdr? (< (.nextDouble rng) 0.4)
        n (count colour-ids)
        lower [(color-batch colour-ids (uniform-values rng n hdr?)
                            :blend :replace :opacity (pick rng [1 1 1.0 0.7]))]
        lower (cond-> lower
                (< (.nextDouble rng) 0.4)
                (conj (let [ids (vec (take 8 (shuffled rng colour-ids)))]
                        (color-batch ids (mapv #(* 0.3 %) (uniform-values rng 8 false))
                                     :blend (pick rng [:add :max :replace]) :opacity (pick rng [0.5 1 0.25]) :source :sprinkle)))
                (< (.nextDouble rng) 0.3)
                (conj {:kind :assignments :source {:effect-id :explicit}
                       :assignments [{:target-id :p2 :attribute :color :value [1/2 1/4 0] :opacity 3/4}
                                     {:target-id :p3 :attribute :color :value [0.1 0.9 0.2] :blend :max}
                                     {:target-id :par :attribute :dimmer :value 0.8}]})
                (< (.nextDouble rng) 0.3)
                (conj (assoc (color-batch (vec (take 5 (shuffled rng colour-ids))) (uniform-values rng 5 false) :source :compound)
                             :native-layer {:id :compound :member 0})))
        program (pick rng programs)
        transform-only? (< (.nextDouble rng) 0.15)
        member-ids (if (< (.nextDouble rng) 0.5) colour-ids (vec (take 12 (shuffled rng colour-ids))))
        descriptor (cond-> {:id :modifier :member 0 :transforms program
                            :member-opacity (pick rng [1 1 1.0 0.6 0 1/3])
                            :opacity (pick rng [1 1 0.8 1.0])}
                     transform-only? (assoc :target-ids (into member-ids [:w0 :w1]))
                     (and (not transform-only?) (< (.nextDouble rng) 0.3)) (assoc :target-ids (into member-ids [:w0]))
                     (< (.nextDouble rng) 0.3)
                     (assoc :target-weights (into {} (map (fn [id] [id (pick rng [0 0.5 1 1.0 0.25])])) colour-ids)))
        modifier (if transform-only?
                   {:kind :assignments :assignments [] :source {:effect-id :modifier :instance-id :m}
                    :native-layer descriptor}
                   (cond-> (assoc (color-batch member-ids (uniform-values rng (count member-ids) false)
                                               :source :modifier :opacity (pick rng [1 1 0.5 0]))
                                  :native-layer descriptor :source {:effect-id :modifier :instance-id :m})
                     (and hdr? (< (.nextDouble rng) 0.3)) (assoc :emission-gain 1.5)))
        later (when (< (.nextDouble rng) 0.3)
                [(color-batch [:p0 :p1] [0.2 0.3 0.4 0.9 0.8 0.7] :source :later)])
        options (cond-> {:master (pick rng [1.0 1.0 0.5])}
                  hdr? (assoc :hdr {})
                  (< (.nextDouble rng) 0.3) (assoc :blackout-ids #{:p4 :par :elsewhere}))]
    {:contributions (-> lower (conj modifier) (into later)) :options options}))

(defn- uniform-batch [ids triple source & {:as options}]
  {:kind :batch :source {:effect-id source}
   :batch (merge {:target-ids ids :outputs {:color (fields/->UniformField :vec3 3 (double-array triple))}} options)})

(defn- extended-modifier
  "A modifier with a random program, opacities, weights and member blend,
  sometimes a uniform (stride 0) batch or a transform-only member."
  [^Random rng id hdr? member-ids]
  (let [transform-only? (< (.nextDouble rng) 0.2)
        descriptor (cond-> {:id id :member 0 :transforms (pick rng programs)
                            :member-opacity (pick rng [1 1.0 0.6 0.3 1/3])
                            :opacity (pick rng [1 1.0 0.8 0.4])}
                     transform-only? (assoc :target-ids (into member-ids [:w0]))
                     (< (.nextDouble rng) 0.4)
                     (assoc :target-weights (into {} (map (fn [i] [i (pick rng [0 0.5 1 1.0 0.25 0.9])])) colour-ids)))]
    (if transform-only?
      {:kind :assignments :assignments [] :source {:effect-id id} :native-layer descriptor}
      (cond-> (assoc (if (< (.nextDouble rng) 0.2)
                       (uniform-batch member-ids [(.nextDouble rng) (.nextDouble rng) (.nextDouble rng)] id
                                      :blend (pick rng [:replace :add :max]) :opacity (pick rng [1 0.5 0.7]))
                       (color-batch member-ids (mapv #(* 0.5 %) (uniform-values rng (count member-ids) false))
                                    :source id :blend (pick rng [:replace :add :max]) :opacity (pick rng [1 0.5 0.7 0])))
                     :native-layer descriptor :source {:effect-id id})
        (and hdr? (< (.nextDouble rng) 0.4)) (assoc :emission-gain (pick rng [1.5 0.5 2.0]))))))

(defn- extended-scenario
  "The review probe's shapes (tolgraven/afterglow#175): member :add and :max
  blends, two stacked typed groups with an optional write between them,
  uniform batches, a wash over part of the rig, weighted translucent direct
  compounds of batches and assignments, lower :add writes with Ratio values
  and opacity, and a non-colour group that forces the general path."
  [seed]
  (let [rng (Random. (long seed))
        hdr? (< (.nextDouble rng) 0.4)
        wash-ids (if (< (.nextDouble rng) 0.3) (vec (take 10 (shuffled rng colour-ids))) colour-ids)
        lower [(if (< (.nextDouble rng) 0.2)
                 (uniform-batch wash-ids [0.3 0.6 0.1] :wash :opacity (pick rng [1 0.7]))
                 (color-batch wash-ids (uniform-values rng (count wash-ids) hdr?) :source :wash :opacity (pick rng [1 0.7 1.0])))]
        lower (cond-> lower
                (< (.nextDouble rng) 0.5)
                (conj (let [ids (vec (take 9 (shuffled rng colour-ids)))]
                        (color-batch ids (mapv #(* 0.3 %) (uniform-values rng 9 false)) :source :sprinkle
                                     :blend (pick rng [:add :max :replace]) :opacity (pick rng [0.5 1 0.25]))))
                (< (.nextDouble rng) 0.4)
                (conj {:kind :assignments :source {:effect-id :explicit}
                       :assignments [{:target-id :p2 :attribute :color :value [1/10 1/3 0] :opacity 1/3 :blend :add}
                                     {:target-id :p5 :attribute :color :value [0.1 0.2 0.3] :blend :add}
                                     {:target-id :p6 :attribute :color :value [0.7 0.2 0.3] :blend :max :opacity 0.4}
                                     {:target-id :par :attribute :dimmer :value 0.8}]})
                (< (.nextDouble rng) 0.1)
                (conj {:kind :assignments :source {:effect-id :dim}
                       :assignments [{:target-id :par :attribute :dimmer :value 0.5}]
                       :native-layer {:id :dim :member 0
                                      :transforms [{:attribute :dimmer
                                                    :value {:op :multiply :args [{:op :previous :attribute :dimmer :default 1.0} 0.5]}}]}})
                (< (.nextDouble rng) 0.3)
                (conj (let [ids (vec (take 5 (shuffled rng colour-ids)))
                            descriptor (cond-> {:id :compound :member 0}
                                         (< (.nextDouble rng) 0.6)
                                         (assoc :opacity (pick rng [1 0.7 1.0 0.3])
                                                :target-weights (into {} (map (fn [i] [i (pick rng [0 0.5 1 1.0])])) colour-ids)))]
                        (if (< (.nextDouble rng) 0.4)
                          {:kind :assignments :source {:effect-id :compound} :native-layer descriptor
                           :assignments (mapv (fn [i] {:target-id i :attribute :color :value [(.nextDouble rng) 0.25 0.5]}) ids)}
                          (assoc (color-batch ids (uniform-values rng 5 false) :source :compound) :native-layer descriptor)))))
        ids-a (if (< (.nextDouble rng) 0.5) colour-ids (vec (take 12 (shuffled rng colour-ids))))
        ids-b (if (< (.nextDouble rng) 0.5) colour-ids (vec (take 11 (shuffled rng colour-ids))))
        a (extended-modifier rng :mod-a hdr? ids-a)
        stack? (< (.nextDouble rng) 0.6)
        b (when stack? (extended-modifier rng :mod-b hdr? ids-b))
        between (when (and stack? (< (.nextDouble rng) 0.4))
                  [(color-batch (vec (take 4 (shuffled rng colour-ids))) (uniform-values rng 4 false) :source :between
                                :blend (pick rng [:add :max :replace]) :opacity (pick rng [0.5 1]))])
        later (when (< (.nextDouble rng) 0.3) [(color-batch [:p0 :p1] [0.2 0.3 0.4 0.9 0.8 0.7] :source :later)])
        options (cond-> {:master (pick rng [1.0 1.0 0.5])}
                  hdr? (assoc :hdr {})
                  (< (.nextDouble rng) 0.3) (assoc :blackout-ids #{:p4 :par :elsewhere}))]
    {:contributions (cond-> (conj lower a) between (into between) b (conj b) true (into later))
     :options options}))

(defn- outcome [contributions options]
  (try
    (let [result (frame/resolve-contributions patch contributions options)]
      {:universes (into (sorted-map) (map (fn [[u ^bytes b]] [u (vec b)])) (:universes result))
       :values (:values result)
       :compact (when-let [compact (:compact result)] (frame/project-compact compact))})
    (catch clojure.lang.ExceptionInfo e
      {:error (ex-message e) :data (ex-data e)})))

(defn- typed? [contributions options]
  (try
    (let [[patch _ blocks] (#'frame/prepare-contributions patch contributions options)]
      (boolean (::typed/typed (meta (#'frame/compose-layers patch blocks true)))))
    (catch Exception _ false)))

(deftest typed-colour-layers-match-the-general-path-on-every-frame
  (let [engaged (volatile! 0) faults (volatile! 0) frames 600]
    (doseq [seed (range frames)
            :let [{:keys [contributions options]} (scenario seed)]
            dense? [true false]
            :let [options (assoc options :include-values? (not dense?) :compact-values? dense?)
                  typed-result (outcome contributions options)
                  general (outcome contributions (assoc options :typed-layers? false))]]
      (when (and dense? (typed? contributions options)) (vswap! engaged inc))
      (when (:error general) (vswap! faults inc))
      (is (= general typed-result) (str "seed " seed (when dense? " dense"))))
    (testing "the scenarios exercise the typed path and its fallbacks"
      (is (< (* 0.4 frames) @engaged frames) (str @engaged " typed frames"))
      (is (pos? @faults) "some frames fault, and fault identically"))))

(deftest typed-colour-layers-match-the-general-path-for-the-review-shapes
  (let [engaged (volatile! 0) stacked (volatile! 0) frames 600]
    (doseq [seed (range frames)
            :let [{:keys [contributions options]} (extended-scenario seed)]
            dense? [true false]
            :let [options (assoc options :include-values? (not dense?) :compact-values? dense?)]]
      (when (and dense? (typed? contributions options))
        (vswap! engaged inc)
        (when (some #(= :mod-b (get-in % [:native-layer :id])) contributions) (vswap! stacked inc)))
      (is (= (outcome contributions (assoc options :typed-layers? false)) (outcome contributions options))
          (str "seed " seed (when dense? " dense"))))
    (is (< (* 0.25 frames) @engaged) (str @engaged " typed frames"))
    (is (pos? @stacked) "Two typed groups compose in one frame")))

(defn- transform-only [program hdr?]
  {:contributions [{:kind :assignments :assignments [] :source {:effect-id :m}
                    :native-layer {:id :m :member 0 :target-ids [:p0 :p1] :transforms [(step program)]}}]
   :options (cond-> {} hdr? (assoc :hdr {}))})

(deftest nested-literal-products-stay-exact
  (testing "a default times two literals is exact on the general path, so the typed path defers to it"
    (doseq [[program hdr?] [[{:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) 2]} 5/12]} true]
                            [{:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) 3]} 1/10]} true]
                            [{:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) 3]} 1/10]} false]
                            [{:op :multiply :args [{:op :multiply :args [(previous [5 5 5]) {:op :incoming :attribute :color :default [1 1 1]}]} 1/3]} true]]
            dense? [true false]
            :let [{:keys [contributions options]} (transform-only program hdr?)
                  options (assoc options :include-values? (not dense?) :compact-values? dense?)]]
      (is (= (outcome contributions (assoc options :typed-layers? false)) (outcome contributions options))
          (pr-str program))))
  (testing "the 2.0 * 5/12 repro sends 212, not 213"
    (let [{:keys [contributions options]} (transform-only {:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) 2]} 5/12]} true)]
      (is (= [-44 -44 -44] (take 3 (get-in (outcome contributions options) [:universes 1]))))))
  (testing "every k * m/n under one, with HDR"
    (doseq [k (range 2 9) n (range 2 30) m (range 1 n)
            :let [r (/ m n)] :when (and (ratio? r) (<= (* k r) 1))
            :let [{:keys [contributions options]}
                  (transform-only {:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) k]} r]} true)
                  general (outcome contributions (assoc options :typed-layers? false))
                  typed-result (outcome contributions options)]
            :when (not= general typed-result)]
      (is (= general typed-result) (str k " * " r)))))

(deftest frames-report-how-their-layers-composed
  (let [wash (color-batch colour-ids (repeat (* 3 (count colour-ids)) 0.5))
        modifier (fn [program] (assoc (color-batch colour-ids (repeat (* 3 (count colour-ids)) 0.25) :source :modifier)
                                      :native-layer {:id :m :member 0 :transforms [(step program)]}))
        render (fn [program & [options]]
                 (meta (frame/resolve-contributions patch [wash (modifier program)]
                                                    (merge {:include-values? false :compact-values? true} options))))]
    (is (= {::typed/typed true} (render {:op :multiply :args [(previous [0.0 0.0 0.0]) incoming]})))
    (is (= {::typed/fallback :program} (render {:op :add :args [(previous [0.0 0.0 0.0]) incoming]}))
        "A group outside the typed subset names why the frame took the general path")
    (is (nil? (render {:op :multiply :args [(previous [0.0 0.0 0.0]) incoming]} {:typed-layers? false})))
    (is (nil? (meta (frame/resolve-contributions patch [wash] {}))) "No native layer, nothing to report")))

(deftest typed-colour-layers-carry-one-owned-batch-at-the-layer-position
  (let [wash (color-batch colour-ids (repeat (* 3 (count colour-ids)) 0.5))
        modifier (assoc (color-batch colour-ids (repeat (* 3 (count colour-ids)) 0.25) :source :modifier)
                        :native-layer {:id :m :member 0
                                       :transforms [(step {:op :multiply :args [(previous [0.0 0.0 0.0]) incoming]})]})
        later (color-batch [:p0] [1.0 0.0 0.0] :source :later)
        [p _ blocks] (#'frame/prepare-contributions patch [wash modifier later] {})
        composed (#'frame/compose-layers p blocks true)
        _ (is (::typed/typed (meta composed)))
        [_ out _] composed
        values ^doubles (get-in out [:compiled :columns 0 :values])]
    (is (= [:lower :modifier :later] (mapv #(get-in % [:source :effect-id] (:source %)) composed)))
    (is (= 0.125 (aget values 0) (aget values 5)))
    (is (not (identical? values (get-in modifier [:batch :outputs :color :values]))) "The output array is the call's own")
    (testing "a second call returns a fresh array and leaves inputs untouched"
      (let [again (get-in (nth (#'frame/compose-layers p blocks true) 1) [:compiled :columns 0 :values])]
        (is (not (identical? values again)))
        (is (Arrays/equals ^doubles values ^doubles again))
        (is (every? #(== 0.25 %) (get-in modifier [:batch :outputs :color :values])))))))

(deftest unsupported-programs-and-groups-take-the-general-path
  (let [fold identity]
    (is (nil? (typed/program [{:attribute :aim :value (previous)}] fold)) "Only colour")
    (is (nil? (typed/program [(step {:op :add :args [(previous) incoming]})] fold)) "Only the colour operators")
    (is (nil? (typed/program [(step {:op :previous :attribute :dimmer})] fold)) "Only colour reads")
    (is (nil? (typed/program [(step {:op :multiply :args [(previous [1/3 0 0]) [3 1 1]]})] fold))
        "A default meeting a literal would multiply exactly")
    (is (nil? (typed/program [(step {:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) 2]} 5/12]})] fold))
        "A literal product carries its exact value into the next multiply")
    (is (some? (typed/program [(step {:op :multiply :args [{:op :multiply :args [(previous [1 1 1]) 2]} 0.25]})] fold)))
    (is (some? (typed/program [(step {:op :rotate-hue :args [(previous [0.0 0.0 0.0]) 1/6]})] fold)))))
