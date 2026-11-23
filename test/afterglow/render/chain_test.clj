(ns afterglow.render.chain-test
  (:require [afterglow.render.chain :as chain]
            [afterglow.render.fields :as fields]
            [afterglow.render.frame :as frame]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]]))

(defn- lit [n] {:op :const :value n})
(defn- plus [& xs] {:op :add :args (vec xs)})
(defn- parameter [key] {:op :param :key key})
(def default-env {:params {:level 0.2} :elapsed-beats 3.0 :beat 4.0 :elapsed-ms 420.0})
(def ids [:left :right])
(def positions [[0.15 0 0] [0.73 0 0]])
(def fixtures (mapv (fn [id i p] {:id id :position p :universe 1 :address (+ 1 (* 4 i))
                                   :channels {:focus 1 :red 2 :green 3 :blue 4}})
                    ids (range) positions))

(defn- prepare [outputs positions plan uvs]
  {:expressions outputs :positions positions :surface-uvs uvs :cpu-plan plan})

(defn- block [outputs blend opacity env]
  {:kind :batch :source {:instance-id (name blend)}
   :batch {:target-ids ids :blend blend :opacity opacity
           :field-request {:group (prepare outputs positions (ir/compile-batch outputs) nil) :env env}}})

(defn- oracle [blocks]
  (let [fields ((fields/frame-evaluator
                 (fn [{:keys [cpu-plan positions surface-uvs]} env]
                   (ir/evaluate-batch cpu-plan env positions surface-uvs))) blocks)]
    (frame/portable-frame (frame/resolve-contributions (frame/compile-patch fixtures) fields))))

(defn- shader [blocks] (get-in (first blocks) [:batch :field-request :group :expressions]))

(deftest mix-stage-order-native-opacity-envelopes-positions-and-independent-clocks
  (let [source {:op :position :axis :x}
        clock {:op :clamp :args [{:op :divide :args [{:op :beat} (lit 8)]} (lit 0) (lit 1)]}
        base (block {:focus (lit 0.1) :color (lit [0.2 0.45 0.55])} :replace 1 default-env)
        mid (block {:focus (parameter :level) :color (lit [0.1 0.35 0.3])} :add 0.5 default-env)
        ;; Both clocks resolve from the supplying instance at this frame.
        last-stage (block {:focus clock :color {:op :vec3 :args [source (parameter :level) clock]}}
                          :max 0.2 (assoc default-env :elapsed-beats 6.0 :params {:level 0.65}))
        stages [base (assoc-in mid [:batch :field-request :scales] {:color 0.8}) last-stage]
        result (chain/fuse (chain/create-cache) prepare stages)]
    (is (= 1 (count result)))
    (let [expected (oracle stages) actual (oracle result)]
      (is (= (:universes expected) (:universes actual)))
      (doseq [id ids field [:emitted-color :focus]]
        (let [a (get-in expected [:values id field]) b (get-in actual [:values id field])]
          (is (every? #(< (abs %) 1.0e-12) (if (vector? a) (map - a b) [(- a b)]))))))
    (is (= :replace (get-in result [0 :batch :blend])))
    (is (= (set (keys (shader result))) #{:focus :color}))
    (is (seq (:uniforms (ir/emit-glsl-batch (shader result)))))))

(deftest fully-opaque-writes-elide-spatial-work-and-cache-programs-across-parameter-changes
  (let [old (block {:focus {:op :clamp :args [{:op :sin :args [{:op :position :axis :x}]} (lit 0) (lit 1)]}}
                   :replace 1 default-env)
        new (block {:focus (parameter :level)} :replace 1 default-env)
        cache (chain/create-cache)
        draw #(chain/fuse cache prepare [old %])
        result (draw new)
        revised (draw (assoc-in new [:batch :field-request :env :params :level] 0.8))]
    (is (= 1 (count result)))
    (is (not (re-find #"\bsin\(" (:source (ir/emit-glsl-batch (shader result))))))
    (is (identical? (get-in result [0 :batch :field-request :group]) (get-in revised [0 :batch :field-request :group])))
    (is (not= (oracle result) (oracle revised)))
    (is (not= (shader result) (shader (draw (block {:focus (lit 0.5)} :replace 1 default-env)))))
    (is (= [old] (chain/fuse cache prepare [old])))))

(deftest barriers-leave-selection-source-validation-and-unproven-intermediate-ranges-intact
  (let [cache (chain/create-cache) f #(chain/fuse cache prepare %)
        base (block {:focus (lit 0.9)} :replace 1 default-env)
        tail (block {:focus (lit 0.1)} :replace 1 default-env)
        illegal (block {:focus (lit 0.9)} :add 1 default-env)
        uv-a (assoc-in base [:batch :field-request :group :surface-uvs] [[0 0] [1 1]])
        uv-b (assoc-in tail [:batch :field-request :group :surface-uvs] [[0 1] [1 0]])]
    (doseq [stages [[(assoc base :native-layer {:id :compound :member 0}) tail]
                    [base (assoc tail :emission-gain 1.2)]
                    [base (assoc-in tail [:batch :target-ids] [:right :left])]
                    [base (assoc-in tail [:batch :field-request :group :positions] (vec (reverse positions)))]
                    [uv-a uv-b]
                    [base illegal]
                    [(assoc-in base [:batch :opacity] 0.4) tail]
                    [base {:kind :assignments :assignments []} tail]]]
      (is (identical? stages (f stages))))
    (let [missing (block {:focus (parameter :unknown)} :replace 1 default-env)]
      (is (identical? missing (first (f [missing tail])))))))

(deftest fusion-keeps-one-coherent-surface-chart-and-clocks-per-instance
  (let [uv {:op :surface-uv :axis :v}
        curves {:op :clamp :args [(plus uv (parameter :level)) (lit 0) (lit 1)]}
        chart [[0.25 0.75] [0.5 0.25]]
        add-chart #(assoc-in % [:batch :field-request :group :surface-uvs] chart)
        stages [(add-chart (block {:focus curves} :replace 1 default-env))
                (add-chart (block {:focus curves} :max 0.5 (assoc default-env :params {:level 0.1})))]
        result (chain/fuse (chain/create-cache) prepare stages)]
    (is (= 1 (count result)))
    (is (= (oracle stages) (oracle result)))
    (is (re-find #"layout\(location = 1\) in vec2" (:source (ir/emit-glsl-batch (shader result) {:surface-uv? true}))))))


(deftest full-compatible-chain-remains-one-program-beyond-eight-effects
  (let [base (block {:dimmer (lit 0.25)} :replace 1 default-env)
        sweep (fn [i] (block {:dimmer (lit (/ (double i) 32))} :replace 0.25 default-env))
        stages (into [base] (map sweep) (range 1 25))
        fused (chain/fuse (chain/create-cache) prepare stages)]
    (is (= 1 (count fused)))
    (is (= 24 (count (re-seq #"mix\(" (:source (ir/emit-glsl-batch (shader fused)))))))
    (is (= (:universes (oracle stages)) (:universes (oracle fused))))))

(deftest repeated-fixture-rows-and-illegal-geometry-blends-retain-stage-order
  (let [cache (chain/create-cache)
        base (block {:focus (lit 0.2)} :replace 1 default-env)
        addition (block {:focus (lit 0.1)} :add 1 default-env)
        stages [base addition]
        repeated (mapv #(assoc-in % [:batch :target-ids] [:left :left]) stages)]
    (is (= 1 (count (chain/fuse cache prepare stages))))
    (is (identical? repeated (chain/fuse cache prepare repeated)))
    (is (< (abs (- 0.4 (get-in (oracle repeated) [:values :left :channels :focus]))) 1e-12))
    (doseq [attribute [:aim :direction] blend [:max :add]]
      (let [field {attribute (lit [1 1 1])}
            invalid [(block field :replace 1 default-env) (block field blend 1 default-env)]]
        (is (identical? invalid (chain/fuse cache prepare invalid)))))))

(deftest opaque-replacement-keeps-earlier-typed-field-errors-observable
  (doseq [[attr wrong right] [[:focus [0.2 0.3 0.4] 0.5] [:color 0.3 [0.2 0.3 0.4]]]]
    (let [stages [(block {attr (lit wrong)} :replace 1 default-env)
                  (block {attr (lit right)} :replace 1 default-env)]
          result (chain/fuse (chain/create-cache) prepare stages)]
      (is (identical? stages result))
      (is (thrown? clojure.lang.ExceptionInfo (oracle result))))))
