(ns afterglow.render.ir-corpus
  "Expression families shared by the batch evaluator oracle and the GLSL golden
  test. The research families come from Tolglow's spatial level-of-detail
  harness (tolgraven/tolglow#822, `dev/tolglow/perf/led_lod.clj`); the palette
  gradient follows the lowering of `tolglow.compiler.gradient`."
  (:require [afterglow.render.ir :as ir]))

(defn op [operation & args] {:op operation :args (vec args)})

(defn c [value] {:op :const :value value})

(def x {:op :position :axis :x})

(def y {:op :position :axis :y})

(def z {:op :position :axis :z})

(def beat {:op :beat})

(def level {:op :param :key :level})

(defn- smooth [w] (op :multiply w w (op :subtract (c 3.0) (op :multiply (c 2.0) w))))

(defn sphere
  "Weight of a sphere whose centre sweeps a matrix of `rows` rows. Its moving
  centre appears twelve times in the tree, as the authoring DSL builds it."
  [rows radius band]
  (let [cx (op :add (c 50.0) (op :multiply (c 40.0) (op :sin (op :multiply (c 1.5) beat))))
        cz (op :add (c (* 0.5 rows)) (op :multiply (c (* 0.3 rows)) (op :cos (op :multiply (c 1.1) beat))))
        dx (op :subtract x cx)
        dz (op :subtract z cz)
        distance (op :sqrt (op :add (op :multiply dx dx) (op :multiply dz dz)))]
    (smooth (op :clamp (op :divide (op :subtract (c (+ radius band)) distance) (c (* 2.0 band))) (c 0.0) (c 1.0)))))

(def palette-stops 8)

(defn- stop-param [stop field type] {:op :param :key (keyword "palette" (str field "-" stop)) :type type})

(defn gradient
  "An eight-stop gradient lowered as Tolglow lowers {:op :gradient}: each stop
  mixes towards its colour by a clamped fraction of the same position term."
  [position]
  (let [t (op :fract (op :multiply position (c 1.0)))
        colour (reduce (fn [colour stop]
                         (op :mix colour (stop-param stop "color" :vec3)
                             (op :clamp (op :multiply (op :subtract t (stop-param stop "start" :number))
                                            (stop-param stop "scale" :number))
                                 (c 0.0) (c 1.0))))
                       (stop-param 0 "color" :vec3)
                       (range 1 palette-stops))]
    (op :clamp colour (c 0.0) (c 1.0))))

(def palette-params
  (let [colours [[1.0 0.0 0.0] [1.0 0.5 0.0] [1.0 1.0 0.0] [0.0 1.0 0.0]
                 [0.0 1.0 1.0] [0.0 0.0 1.0] [0.5 0.0 1.0] [1.0 0.0 0.5]]]
    (into {} (mapcat (fn [stop]
                       [[(keyword "palette" (str "color-" stop)) (nth colours stop)]
                        [(keyword "palette" (str "start-" stop)) (/ (dec stop) 7.0)]
                        [(keyword "palette" (str "scale-" stop)) 7.0]]))
          (range palette-stops))))

(defn families
  "Research families on a matrix with `rows` rows, each a map of named outputs."
  [rows]
  (let [soft (sphere rows 12.0 6.0)]
    [{:id :sine-wash
      :outputs {:color (op :vec3 (op :multiply (c 0.5) (op :add (c 1.0) (op :sin (op :add (op :multiply (c 0.05) x) {:op :bar}))))
                           level (c 0.25))
                :white (c 0.1)}}
     {:id :saw-chase
      :outputs {:color (op :vec3 (op :multiply level (op :fract (op :add (op :multiply (c 0.5) beat) (op :multiply (c 0.02) x))))
                           (c 0.1) level)}}
     {:id :plasma
      :outputs {:color (op :vec3
                           (op :add (c 0.5) (op :multiply (c 0.25) (op :sin (op :add (op :multiply (c 0.11) x) beat)))
                               (op :multiply (c 0.25) (op :sin (op :subtract (op :multiply (c 0.07) z) (op :multiply (c 0.5) beat)))))
                           (op :add (c 0.5) (op :multiply (c 0.25) (op :sin (op :add (op :multiply (c 0.05) x) (op :multiply (c 0.09) z)
                                                                                    (op :multiply (c 0.7) beat))))
                               (op :multiply (c 0.25) (op :cos (op :subtract (op :multiply (c 0.13) z) beat))))
                           (op :add (c 0.5) (op :multiply (c 0.5) (op :sin (op :add (op :multiply (c 0.03) x) (op :multiply (c -0.04) z)
                                                                                   (op :multiply (c 0.3) beat))))))}}
     {:id :soft-sphere
      :outputs {:color (op :vec3 (op :multiply level soft) (op :multiply (c 0.3) soft) (c 0.1))}}
     {:id :palette-gradient
      :outputs {:color (op :multiply (gradient (op :add (op :multiply (c 0.01) x) (op :multiply (c 0.25) beat))) level)}}
     {:id :one-spatial-component
      :outputs {:color (op :vec3 (op :add (c 0.5) (op :multiply (c 0.5) (op :sin (op :add (op :multiply (c 1.5) x) (op :multiply (c 3.0) beat)))))
                           (op :multiply (c 0.1) (op :cos (op :multiply (c 0.5) beat)))
                           level)}}
     {:id :shared-across-fields
      :outputs {:color (op :multiply (c [1.0 0.4 0.1]) soft level)
                :white (op :multiply (c 0.5) soft)
                :dimmer (op :max (op :sin (op :multiply (c 1.5) beat)) (c 0.25))
                :aim (op :vec3 x (op :add y (op :sin (op :multiply (c 1.5) beat))) (c -1.0))}}
     {:id :vector-sphere
      ;; A vector term shared across components and fields, with broadcasts.
      :outputs {:color (op :mix (c [0.0 0.1 0.2]) {:op :param :key :tint :type :vec3}
                           (op :clamp (op :multiply soft (op :add (c 1.0) {:op :time})) (c 0.0) (c 1.0)))
                :focus (op :add (op :multiply (c 0.001) {:op :time}) (op :subtract soft))}}
     {:id :fused-max-chain
      ;; A fused chain substitutes the previous layer into the next one.
      :outputs {:color (let [base (op :vec3 (op :multiply level soft) (c 0.2) (op :multiply (c 0.5) soft))]
                         (ir/partial-max-blend base (op :multiply base (op :sin (op :multiply (c 0.02) x))) (c 0.75)))}}]))

(def environment
  "Explicit frame inputs read by every family."
  {:params (merge {:level 0.8 :tint [0.9 0.3 0.6]} palette-params)
   :beat 33.75 :elapsed-beats 1.625 :elapsed-ms 812.5 :time-ms 16875.0
   :meter {:beats-per-bar 4 :bars-per-phrase 4}})

(defn matrix
  "Positions of a `columns` wide matrix of `pixels` heads at unit pitch."
  [pixels columns]
  (mapv (fn [i] [(double (mod i columns)) 0.0 (double (quot i columns))]) (range pixels)))

(def shader-expressions
  "Existing shader test expressions, each with the coordinates it is emitted for."
  [[:typed-bindings {:op :multiply :args [{:op :param :key :color :type :vec3} {:op :param :key :gain}
                                          {:op :sin :args [{:op :time}]}]} :world]
   [:musical {:op :add :args [{:op :phrase} {:op :beat :clock :absolute}]} :world]
   [:max-blend (ir/partial-max-blend (op :multiply x (c 0.5)) (c [0.5 0.25 0.75]) level) :world]
   [:charted (op :add {:op :surface-uv :axis :u} (op :multiply (c 0.5) {:op :surface-uv :axis :v})) :surface-uv]
   [:uv-only-world (op :sin (op :multiply (c 3.0) x)) :surface-uv]])

(def shader-batches
  "Existing vertex-shader test batches, with emit options."
  [[:packed {:motion/focus (op :multiply {:op :param :key :gain} {:op :phrase})
             :aim (op :vec2 x {:op :time :clock :absolute})
             :color (op :multiply {:op :param :key :palette/red :type :vec3} {:op :param :key :gain})} {}]
   [:charted {:level (op :add {:op :surface-uv :axis :u} (op :multiply (c 0.5) x))} {:surface-uv? true}]
   [:charted-default {:level (op :add {:op :surface-uv :axis :u} (op :multiply (c 0.5) x))} {}]])
