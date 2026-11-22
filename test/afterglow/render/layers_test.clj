(ns afterglow.render.layers-test
  (:require [afterglow.control.model :as control]
            [afterglow.render.frame :as frame]
            [afterglow.render.layers :as layers]
            [afterglow.runtime.engine :as engine]
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
