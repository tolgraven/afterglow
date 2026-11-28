(ns afterglow.render.layers-test
  (:require [afterglow.control.model :as control]
            [afterglow.render.frame :as frame]
            [afterglow.render.layers :as layers]
            [afterglow.runtime.engine :as engine]
            [afterglow.runtime.keyframes :as keyframes]
            [clojure.test :refer [deftest is testing]]
            [thi.ng.color.core :as color]))

(def patch (frame/compile-patch [{:id :head :address 1 :universe 0 :channels
                                  {:red 1 :green 2 :blue 3 :dimmer 4 :pan [5 6] :tilt [7 8] :focus 9}}]))

(defn row [attr value] {:target-id :head :attribute attr :value value})

(defn block [& rows] {:kind :assignments :assignments (vec rows)})

(defn layer [member opacity transforms block]
  (assoc block :native-layer {:id :compound :member member :opacity opacity :transforms transforms}
               :source {:instance-id member}))

(defn field [op attr] {:op op :attribute attr})

(defn expr [op & args] {:op op :args (vec args)})

(def transforms
  [{:attribute :beat-ratio :value (expr :divide 1 3)}
   {:attribute :color :value (expr :rotate-hue (field :previous :color) (field :field :beat-ratio))}
   {:attribute :aim :value (expr :add (field :previous :aim)
                                 (expr :multiply [1 -1 4] (field :field :beat-ratio)))}
   {:attribute :focus :value (expr :multiply (field :incoming :focus) (field :field :beat-ratio))}])

(deftest native-layer-composes-typed-inputs-before-physical-packing
  (let [base (layer 0 1 [] (block (row :color (color/hsva 0 1 1))
                                   (row :aim [-3 1 4])))
        modify (layer 1 1 transforms
                      {:kind :batch :batch {:target-ids [:head]
                                           :outputs {:focus {:type :number :components 1 :values (double-array [0.75])}}}})
        background (block (row :dimmer 0.8))
        ;; The modifier has a lower normal cue priority. It still sees slot 0.
        result (frame/resolve-contributions patch [modify background base] {:compact-values? true})
        compact (frame/resolve-contributions patch [modify background base] {:include-values? false :compact-values? true})
        v (get-in result [:values :head])]
    (is (= [-8/3 2/3 16/3] (:aim v)))
    (is (ratio? (first (:aim v))))
    (is (= 0.25 (get-in v [:channels :focus])))
    (is (= [0.0 0.8 0.0] (:emitted-color v)))
    (is (not (contains? (:channels v) :beat-ratio)))
    (is (= (vec (get-in result [:universes 0])) (vec (get-in compact [:universes 0]))))
    (is (= [0.0 0.8 0.0] (:emitted-color (first (frame/project-compact (:compact compact))))))))

(deftest two-opacity-boundaries-mix-with-the-current-backdrop
  (let [raw (block (row :focus 1/2))
        lower (block (row :focus 1/4))
        levels (fn [outer inner]
                 (let [a (layer 1 outer [{:attribute :focus :value (expr :multiply (field :previous :focus) 2)}]
                                raw)
                       b (layer 0 outer [] raw)
                       a (assoc-in a [:native-layer :member-opacity] inner)
                       out (frame/resolve-contributions patch [a lower b])]
                   (get-in out [:values :head :channels :focus])))]
    (is (== 1/4 (levels 0 1)))
    (is (== 1/2 (levels 1 0)))
    (is (== 1 (levels 1 1)))
    (is (== 1/2 (levels 1/2 1/2)))))

(deftest sources-and-members-remain-independent
  (let [b (block (row :aim [-2 0 5]))
        rotate {:attribute :aim :value (expr :rotate-y (field :previous :aim) (/ Math/PI 2))}
        result (frame/resolve-contributions patch [(layer 0 1 [] b) (layer 1 1 [rotate] b)])
        xyz (get-in result [:values :head :aim])]
    (is (< (abs (- (first xyz) 5)) 1.0e-9))
    (is (< (abs (- (last xyz) 2)) 1.0e-9))
    (let [error (try (frame/resolve-contributions patch [(layer 1 1 [rotate] b)]) nil
                     (catch clojure.lang.ExceptionInfo cause cause))]
      (is (= {:instance-id 1} (:effect-source (ex-data error)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (layers/validate-transforms! [{:attribute :focus :value {:op :imaginary}}])))))

(deftest target-weight-checks-preserve-number-types-and-fault-sources
  (let [render (fn [opacity weights]
                 (let [member (assoc-in (layer 0 opacity [] (block (row :focus 1)))
                                        [:native-layer :target-weights] weights)]
                   (frame/resolve-contributions patch [member])))]
    (doseq [weight [0 1 (float 0.5) 1/3 0.25M]]
      (is (== weight (get-in (render 1 (sorted-map :head weight)) [:values :head :channels :focus]))))
    (doseq [invalid [nil Double/NaN Double/POSITIVE_INFINITY -1/7 1.000000000000000000001M]]
      (let [fault (try (render 0 (array-map :head 1 :unpatched invalid)) nil
                       (catch clojure.lang.ExceptionInfo ex (ex-data ex)))]
        (is (= {:instance-id 0} (:effect-source fault)))))))

(deftest launch-source-retains-a-stable-slot-order-through-parallel-evaluation
  (let [model (control/new-show {:registry {:effects {:base {:id :base :version 1 :params {}}
                                                     :mod {:id :mod :version 1 :params {}}}
                                            :cues {:base {:id :base :version 1 :effect-id :base :priority 100}
                                                   :mod {:id :mod :version 1 :effect-id :mod :priority 2}}}})
        launch (fn [model id descriptor]
                 (:model (control/apply-command model {:command-id (name id) :show-id (:show-id model)
                                                       :epoch (:epoch model) :op :cue/launch :cue-id id :time-ms 0
                                                       :source {:native-layer descriptor}})))
        model (-> model
                  (launch :base {:id "live" :member 0})
                  (launch :mod {:id "live" :member 1 :transforms
                                [{:attribute :focus :value (expr :multiply (field :previous :focus) 2)}]}))
        compile-step (fn [d] #(update % :assignments conj (row :focus (if (= :base (:id d)) 0.25 0.1))))
        a (engine/advance model {:time-ms 0} compile-step)
        b (engine/advance model {:time-ms 0} compile-step (fn [f xs] (reverse (doall (map f xs)))))]
    (is (nil? (:assignments a)))
    (is (= (:contributions a) (:contributions b)))
    (is (== 0.5 (get-in (frame/resolve-contributions patch (:contributions a)) [:values :head :channels :focus])))))

(deftest a-live-reorder-moves-the-rendered-compound-without-relaunching-members
  (let [effect {:id :dimmer :version 1 :params {:level {:type :number :default 1}}}
        model (control/new-show {:registry {:effects {:dimmer effect}
                                            :cues {:dimmer {:id :dimmer :version 1 :effect-id :dimmer}}}})
        apply-command (fn [model op fields]
                        (control/apply-command model (merge {:command-id (str (:revision model))
                                                            :show-id (:show-id model) :epoch (:epoch model)
                                                            :time-ms (:time-ms model) :source {:adapter :test}
                                                            :op op} fields)))
        launch (fn [model level layer]
                 (:model (apply-command model :cue/launch
                                        (cond-> {:cue-id :dimmer :launch {:params {:level level}}}
                                          layer (assoc :source {:adapter :test :native-layer layer})))))
        show (-> model (launch 0.25 {:id :layer :member 0})
                 (launch 0.1 {:id :layer :member 1 :transforms
                              [{:attribute :dimmer :value (expr :multiply (field :previous :dimmer) 2)}]})
                 (launch 1 nil))
        compile-step (fn [_] (fn [ctx]
                               (-> ctx (update-in [:state :frames] (fnil inc 0))
                                   (update :assignments conj (row :dimmer (get-in ctx [:instance :params :level]))))))
        render (fn [result] (frame/resolve-contributions patch (:contributions result)))
        initial (engine/advance show {:time-ms 10} compile-step)
        current (:model initial)
        result (apply-command current :instance/move-after {:instance-id "0:1" :after-instance-id "0:3"})
        moved (:model result)
        live-frame (engine/advance moved {:time-ms 20} compile-step
                                   (fn [f xs] (reverse (mapv f xs))))]
    (is (= :accepted (get-in result [:ack :status])))
    (is (= ["0:3" "0:1" "0:2"] (get-in result [:ack :instance-ids])))
    (is (= (:instances current) (update-vals (:instances moved) #(dissoc % :render-order))))
    (is (= {"0:1" 2 "0:2" 2 "0:3" 2}
           (update-vals (get-in live-frame [:model :instances]) #(get-in % [:state :frames]))))
    (is (= [255 128] (mapv #(bit-and 255 (aget ^bytes (get-in (render %) [:universes 0]) 3))
                           [initial live-frame])))
    (let [reverse-move (apply-command (:model live-frame) :instance/move-after
                                      {:instance-id "0:3" :after-instance-id "0:1"})
          reversed (engine/advance (:model reverse-move) {:time-ms 30} compile-step)]
      (is (= ["0:1" "0:2" "0:3"] (get-in reverse-move [:ack :instance-ids])))
      (is (= 255 (bit-and 255 (aget ^bytes (get-in (render reversed) [:universes 0]) 3)))))))

(deftest standalone-cross-tier-reorder-preserves-bright-output-through-release
  (let [effect {:id :dimmer :version 1 :params {:level {:type :number :default 1}}}
        model (control/new-show {:registry {:effects {:dimmer effect}
                                            :cues {:dimmer {:id :dimmer :version 1 :effect-id :dimmer}}}})
        apply! (fn [model op fields]
                 (let [result (control/apply-command model
                                (merge {:command-id (str (:revision model)) :show-id (:show-id model)
                                        :epoch (:epoch model) :time-ms (:time-ms model) :source :test :op op}
                                       fields))]
                   (is (= :accepted (get-in result [:ack :status])))
                   (:model result)))
        show (-> model
                 (apply! :cue/launch {:cue-id :dimmer :launch {:params {:level 0.8}
                                                               :system {:release {:ms 50}}}})
                 (apply! :cue/launch {:cue-id :dimmer :launch {:priority 10}}))
        compile-step (fn [_] #(update % :assignments conj (row :dimmer (get-in % [:instance :params :level]))))
        advance (fn [model time]
                  (engine/advance model {:time-ms time} compile-step
                                  (fn [f xs] (reverse (mapv f xs)))))
        first-frame (advance show 0)
        moved (apply! (:model first-frame) :instance/move-after {:instance-id "0:1" :after-instance-id "0:2"})
        moved-frame (advance moved 10)
        released (apply! (:model moved-frame) :instance/end {:instance-id "0:1"})
        release-frame (advance released 35)
        final-frame (advance (:model release-frame) 60)
        dmx (fn [result]
              (bit-and 255 (aget ^bytes (get-in (frame/resolve-contributions patch (:contributions result))
                                                [:universes 0]) 3)))]
    (is (= [255 204 230 255] (mapv dmx [first-frame moved-frame release-frame final-frame])))
    (is (= ["0:2" "0:1"] (mapv #(get-in % [:source :instance-id]) (:contributions release-frame))))
    (is (= #{"0:2"} (set (keys (get-in final-frame [:model :instances])))))))

(deftest muted-members-without-an-upstream-dont-change-the-frame
  (let [b (layer 0 1 [{:attribute :focus :value (field :previous :focus)}] (block (row :focus 0.5)))]
    (doseq [stream [[(assoc-in b [:native-layer :opacity] 0)]
                    [(assoc-in b [:native-layer :member-opacity] 0)]]]
      (is (= (vec (get-in (frame/resolve-frame patch []) [:universes 0]))
             (vec (get-in (frame/resolve-contributions patch stream) [:universes 0])))))))

(deftest modifier-only-members-can-inherit-heads-without-dummy-channels
  (let [leader (layer 0 1 [] (block (row :focus 1/3)))
        modifier (assoc-in (layer 1 1 [{:attribute :focus
                                       :value (expr :multiply (field :previous :focus) 2)}] (block))
                           [:native-layer :targets] :previous)]
    (is (== 2/3 (get-in (frame/resolve-contributions patch [leader modifier]) [:values :head :channels :focus])))))

(deftest standalone-transform-only-definition-reads-lower-live-fields
  (let [base {:id :base :version 1 :params {}}
        modifier {:id :adjust :version 1 :params {}
                  :layer {:targets :previous
                          :transforms [{:attribute :focus :value (expr :multiply (field :previous :focus) 2)}]}}
        show (control/new-show {:registry {:effects {:base base :adjust modifier}
                                           :cues {:base {:id :base :version 1 :effect-id :base}
                                                  :adjust {:id :adjust :version 1 :effect-id :adjust}}}})
        launch (fn [m id]
                 (:model (control/apply-command m {:op :cue/launch :cue-id id :command-id (name id) :source {:adapter :test}
                                                    :show-id (:show-id m) :epoch (:epoch m) :time-ms 0})))
        advance (fn [m finish?]
                  (engine/advance m {:time-ms 0}
                                  (fn [d] (if (= :base (:id d)) #(update % :assignments conj (row :focus 1/4))
                                              #(assoc % :done? finish?)))))
        m (-> show (launch :base) (launch :adjust))]
    (doseq [finish? [false true]]
      (is (== 1/2 (get-in (frame/resolve-contributions patch (:contributions (advance m finish?)))
                           [:values :head :channels :focus]))))))

(deftest an-unavailable-native-member-leaves-its-inherited-targets-alone
  (let [base {:id :base :version 1 :params {}}
        modifier {:id :adjust :version 1 :params {}
                  :layer {:targets :previous :transforms [{:attribute :dimmer :value 0.75}]}}
        show (control/new-show {:registry {:effects {:base base :adjust modifier}
                                           :cues {:base {:id :base :version 1 :effect-id :base}
                                                  :adjust {:id :adjust :version 1 :effect-id :adjust}}}})
        launch (fn [m id]
                 (:model (control/apply-command m {:op :cue/launch :cue-id id :command-id (name id) :source :test
                                                    :show-id (:show-id m) :epoch (:epoch m) :time-ms 0})))
        show (-> show (launch :base) (launch :adjust))
        calls (atom [])
        step (keyframes/dependency-driven {:inputs [:level]}
                                          (fn [{:keys [level]}] (swap! calls conj level) {}))
        compile-step (fn [definition]
                       (if (= :adjust (:id definition)) step
                           #(update % :assignments conj (row :dimmer 0.25))))
        tick (fn [previous time inputs]
               (engine/advance (or (:model previous) show)
                               {:time-ms time :reactive-inputs inputs :keyframes (:keyframes previous)}
                               compile-step))
        missing (tick nil 0 {})
        present (tick missing 1 {:level nil})
        lost (tick present 2 {})
        regained (tick lost 3 {:level 0.5})
        samples [missing present lost regained]]
    (is (= [nil 0.5] @calls))
    (is (= [1 2 1 2] (mapv #(count (:contributions %)) samples)))
    (is (= [0.25 0.75 0.25 0.75]
           (mapv #(get-in (frame/resolve-contributions patch (:contributions %)) [:values :head :dimmer]) samples)))))

(deftest opaque-replacements-remain-typed-blocks-at-their-group-anchor
  (let [prepared {:kind :batch :compiled {:target-ids [:head] :columns [{:attribute :focus}]
                                          :blend :replace :opacity 1.0}}
        last-slot (layer 1 1 [] (block (row :focus 0.75)))
        first-slot (layer 0 1 [] prepared)
        background (block (row :focus 0.25))
        no-rows (fn [& _] (throw (ex-info "Opaque layers must retain typed buffers" {})))
        arranged (layers/compose [last-slot background first-slot] no-rows no-rows no-rows)]
    (is (= [background (dissoc first-slot :native-layer) (dissoc last-slot :native-layer)] arranged))
    (is (identical? (:compiled prepared) (:compiled (second arranged))))
    (let [actual (assoc (dissoc first-slot :compiled)
                        :batch {:target-ids [:head] :outputs {:focus {:type :number :components 1
                                                                     :values (double-array [0.5])}}})
          full (frame/resolve-contributions patch [last-slot background actual])
          compact (frame/resolve-contributions patch [last-slot background actual] {:include-values? false})]
      (is (== 0.75 (get-in full [:values :head :channels :focus])))
      (is (= (vec (get-in full [:universes 0])) (vec (get-in compact [:universes 0])))))))

(deftest later-native-modifier-sees-the-reordered-opaque-group
  (let [late (layer 1 1 [] (block (row :focus 0.25)))
        first (layer 0 1 [] (block (row :focus 0.75)))
        other (assoc-in (layer 0 1 [{:attribute :focus :value (expr :multiply (field :previous :focus) 2)}]
                               (block (row :focus 0))) [:native-layer :id] :second-group)]
    (is (== 0.5 (get-in (frame/resolve-contributions patch [late first other]) [:values :head :channels :focus])))))

(deftest opaque-groups-still-handle-scratch-fields-native-colors-and-source-errors
  (let [special (layer 0 1 [] (block (row :beat-ratio 1/3) (row :color (color/hsva 0 1 1))))
        out (get-in (frame/resolve-contributions patch [special]) [:values :head])]
    (is (= [1.0 0.0 0.0] (:emitted-color out)))
    (is (not (contains? (:channels out) :beat-ratio))))
  (let [member (layer 1 1 [] (block (row :focus 0.5)))
        invalid (assoc-in member [:native-layer :targets] :previous)
        error (try (frame/resolve-contributions patch [member invalid]) nil
                   (catch clojure.lang.ExceptionInfo cause cause))]
    (is (= (:source member) (:effect-source (ex-data error))))))

(deftest spatial-weights-blend-the-completed-scene-once
  (let [ids [:inside :edge :outside :zero]
        rig (frame/compile-patch (mapv (fn [i id] {:id id :universe 1 :address (inc i)
                                                   :channels {:focus 1}}) (range) ids))
        batch {:kind :batch :batch {:target-ids ids :outputs {:focus {:type :number :components 1 :values (double-array (repeat 4 0.6))}}}}
        background (apply block (map #(assoc (row :focus 0.2) :target-id %) ids))
        mask {:inside 1.0 :edge 0.5 :zero 0.0}
        weighted (fn [member transforms input]
                   (assoc-in (layer member 0.5 transforms input) [:native-layer :target-weights] mask))
        transform [{:attribute :focus :value (expr :add (field :previous :focus) 0.4)}]
        modifier (assoc-in (weighted 1 transform (block)) [:native-layer :targets] :previous)
        result (frame/resolve-contributions rig [background (weighted 0 [] batch) modifier])
        values (mapv #(get-in result [:values % :channels :focus]) ids)]
    (is (every? #(< (abs %) 1e-8) (map - values [0.6 0.4 0.2 0.2])))
    (is (= [153 102 51 51] (mapv #(bit-and 255 %) (take 4 (get-in result [:universes 1])))))
    (is (thrown? Exception (frame/resolve-contributions rig
                            [(assoc-in (weighted 0 [] batch) [:native-layer :target-weights :edge] 2)])))
    (is (thrown? Exception (frame/resolve-contributions rig
                            [(weighted 0 [] batch) (assoc-in modifier [:native-layer :target-weights] {})])))))

(deftest dense-spatial-replacements-retain-their-typed-columns
  (let [values (double-array [0.7 0.9 0.1])
        ids [42 :moving/head "floor"]
        column {:attribute :focus :components 1 :values values}
        compiled {:target-ids ids :columns [column] :opacity 1.0 :blend :replace}
        mask (assoc-in (layer 0 0.8 [] {:kind :batch :compiled compiled})
                       [:native-layer :target-weights] {42 0.5 "floor" 1.0})
        background (block (assoc (row :focus 0.3) :target-id 42))
        no-fold (fn [& _] (throw (ex-info "Unexpected per-fixture backdrop fold" {})))
        result-single (layers/compose [background mask] no-fold no-fold no-fold)]
    (is (identical? values (get-in (last result-single) [:compiled :columns 0 :values])))
    (is (= [0.4 0.0 0.8] (vec (get-in (last result-single) [:compiled ::layers/opacities]))))
    (is (= background (first result-single)))))

(deftest native-mask-direct-and-general-packing-agree
  (let [ids [:moving/head 42 "floor"]
        rig (frame/compile-patch (mapv (fn [i id]
                                        {:id id :universe 0 :address (+ 1 (* i 8))
                                         :channels {:red 1 :green 2 :blue 3 :pan 4 :tilt 5 :focus 6}})
                                      (range) ids))
        base (apply block (map #(hash-map :target-id % :attribute :color :value [0.1 0.3 0.8]) ids))
        mask {:moving/head 0.0 42 0.375 "floor" 1.0}
        sculpt (fn [member input] (assoc-in (layer member 0.5 [] input) [:native-layer :target-weights] mask))
        batch (fn [ids field width values]
                {:kind :batch :batch {:target-ids ids :outputs {field {:components width :type (if (= width 3) :vec3 :number)
                                                                       :values (double-array values)}}}})
        paint (sculpt 0 (batch (vec (reverse ids)) :color 3 [1.5 0.4 0.1  0.4 1.4 0.1  8 8 8]))
        focus (sculpt 1 (batch ids :focus 1 [Double/NaN 0.5 1.0]))
        aim (block {:target-id 42 :attribute :aim :value [1/2 1 3]})
        scalar (sculpt 0 (block {:target-id 42 :attribute :color :value [0.4 1.4 0.1]}
                                {:target-id "floor" :attribute :color :value [1.5 0.4 0.1]}))
        repeated (sculpt 1 (batch [42 "floor" 42] :focus 1 [0.2 0.8 0.5]))
        scalar-repeat (sculpt 1 (block {:target-id 42 :attribute :focus :value 0.2}
                                       {:target-id 42 :attribute :focus :value 0.5}))]
    (doseq [program [[paint focus] [scalar focus] [paint repeated] [scalar scalar-repeat]
                     [scalar paint] [paint (assoc-in focus [:native-layer :id] :second)]]
            compact? [false true]]
      (let [slow (mapv #(assoc-in % [:native-layer :transforms] [{:attribute :beat-ratio :value 1/3}]) program)
            opts {:hdr {} :include-values? (not compact?) :compact-values? compact?}
            render #(frame/resolve-contributions rig (into [base aim] %) opts)
            fast (render program)
            reference (render slow)]
        (is (= (:values reference) (:values fast)))
        (is (= (vec (get-in reference [:universes 0])) (vec (get-in fast [:universes 0]))))
        (when compact?
          (is (= (frame/project-compact (:compact reference)) (frame/project-compact (:compact fast)))))))))

(defn- near? [a b] (every? #(< (abs %) 1.0e-9) (map - a b)))

(deftest color-grade-dims-desaturates-and-turns-hue-from-one-coefficient-triple
  (testing "zero coefficients leave any colour, including overrange light, unchanged"
    (doseq [c [[0.8 0.3 0.1] [1.0 1.0 1.0] [0.0 0.0 0.0] [2.5 0.4 0.0]]]
      (is (= c (layers/color-grade c [0 0 0])))))
  (is (= [0.0 0.0 0.0] (layers/color-grade [0.8 0.3 0.1] [1 0 0])) "Full dim is black")
  (is (near? [0.4 0.15 0.05] (layers/color-grade [0.8 0.3 0.1] [0.5 0 0])))
  (let [lum (+ (* 0.2126 0.8) (* 0.7152 0.3) (* 0.0722 0.1))]
    (is (near? [lum lum lum] (layers/color-grade [0.8 0.3 0.1] [0 1 0]))
        "Full desaturation keeps the colour's own luminance"))
  (is (= [1.0 1.0 1.0] (layers/color-grade [1.0 1.0 1.0] [0 0.7 0])) "White stays exactly white")
  (is (near? [0.0 1.0 0.0] (layers/color-grade [1.0 0.0 0.0] [0 0 1/3])) "A third of a turn takes red to green")
  (is (near? [0.0 0.0 0.0] (layers/color-grade [0.6 0.2 0.9] [2 -1 0])) "Dim and desaturation clamp to [0,1]")
  (testing "overrange light keeps its value through a hue turn"
    (is (near? [0.0 2.5 0.0] (layers/color-grade [2.5 0.0 0.0] [0 0 1/3])))))

(defn- saturation-of [c] (second (layers/rgb->hsv c)))

(deftest color-guard-lifts-muddy-mixes-and-holds-hue-to-the-palette-arc
  (testing "no floor and no restriction is the identity"
    (doseq [c [[0.8 0.3 0.1] [0.5 0.5 0.5] [1.0 0.0 0.6]]]
      (is (near? c (layers/color-guard c [0 0 0.3])))))
  (testing "a muddy mix rises to the floor and keeps its hue and value"
    (let [mud [0.6 0.45 0.3]
          [h _ v] (layers/rgb->hsv mud)
          guarded (layers/color-guard mud [0.8 0 0])
          [h2 s2 v2] (layers/rgb->hsv guarded)]
      (is (< (saturation-of mud) 0.8))
      (is (< (abs (- h h2)) 1.0e-9))
      (is (< (abs (- v v2)) 1.0e-9))
      (is (< 0.6 s2 0.8))
      (is (near? [0.8 0.8 0.4] (layers/color-guard [0.8 0.8 0.4] [0.5 0 0])) "At the floor a colour is already guarded")))
  (testing "white and faint tints stay close to white"
    (is (= [1.0 1.0 1.0] (layers/color-guard [1.0 1.0 1.0] [0.9 0 0])))
    (is (< (saturation-of (layers/color-guard [1.0 0.97 0.95] [0.9 0 0])) 0.06)))
  (testing "saturation maps monotonically and continuously onto [floor, 1]"
    (let [mapped (mapv #(saturation-of (layers/color-guard [1.0 (- 1.0 %) (- 1.0 %)] [0.6 0 0]))
                       (map #(/ % 100.0) (range 101)))]
      (is (apply <= mapped))
      (is (every? #(< % 0.05) (map - (rest mapped) mapped)))
      (is (every? #(>= % (- 0.6 1.0e-9)) (drop 60 mapped)))))
  (testing "hues outside the allowed arc move to its nearest edge"
    ;; Allow the quarter turn centred on orange (0.08): 0.08 +/- 0.125.
    (let [guard #(first (layers/rgb->hsv (layers/color-guard (layers/hsv->rgb [% 1.0 1.0]) [0 0.75 0.08])))]
      (is (< (abs (- 0.1 (guard 0.1))) 1.0e-9) "Inside the arc")
      (is (< (abs (- 0.205 (guard 0.4))) 1.0e-9) "Past the warm edge")
      (is (< (abs (- 0.955 (guard 0.8))) 1.0e-9) "Past the cool edge, across zero")))
  (is (near? [1.0 0.5 0.0] (layers/color-guard [0.0 0.0 1.0] [0 1 1/12])) "Full restriction locks the hue")
  (is (near? [0.5 0.5 0.5] (layers/color-guard [0.5 0.5 0.5] [0 1 0.6])) "A grey has no hue to move")
  (is (near? [3.0 1.5 0.0] (layers/color-guard [0.0 0.0 3.0] [0 1 1/12])) "Overrange value is kept"))

(deftest color-operators-read-their-settings-from-the-member-and-pack-identically
  (let [base (block (row :color [0.6 0.45 0.3]) (row :dimmer 1.0))
        grade {:attribute :color :value (expr :color-grade (assoc (field :previous :color) :default [0 0 0])
                                              (field :incoming :color))}
        guard {:attribute :color :value (expr :color-guard (field :previous :color) [0.8 0 0])}
        render (fn [options transforms settings]
                 (frame/resolve-contributions
                  patch [(layer 0 1 [] base) (layer 1 1 transforms (block (row :color settings)))] options))]
    (is (= [grade guard] (layers/validate-transforms! [grade guard])))
    (testing "the member's colour output carries the grade, then the guard reads the graded colour"
      (let [rich (render {:compact-values? true} [grade] [0.5 0 0])
            packed (render {:include-values? false :compact-values? true} [grade] [0.5 0 0])]
        (is (near? [0.3 0.225 0.15] (get-in rich [:values :head :emitted-color])))
        (is (= (vec (get-in rich [:universes 0])) (vec (get-in packed [:universes 0]))))
        (is (= [77 57 38 255] (take 4 (map #(bit-and % 0xff) (get-in rich [:universes 0])))))))
    (let [both (render {} [grade (assoc guard :value (expr :color-guard (field :field :color) [0.8 0 0]))] [0 0 0])]
      (is (< 0.6 (saturation-of (get-in both [:values :head :emitted-color])) 0.8)))
    (testing "bad settings fault the member with its source"
      (let [error (try (render {} [(assoc guard :value (expr :color-guard (field :previous :color) 0.5))] [0 0 0]) nil
                       (catch clojure.lang.ExceptionInfo cause cause))]
        (is (= {:instance-id 1} (:effect-source (ex-data error))))))))
