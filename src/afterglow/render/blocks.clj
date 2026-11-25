(ns afterglow.render.blocks
  "Portable effect materials and generators. Lower once to the same numeric IR
  used by scalar effects, dense CPU fields, and GLSL transform feedback."
  (:require [afterglow.render.blocks.glsl :as glsl]
            [afterglow.render.fog-law :as fog-law]
            [afterglow.render.ir :as ir]))

(defn- fail! [path message]
  (throw (ex-info message {:path path :message message})))

(defn- expr [x] (if (map? x) x {:op :const :value x}))

(defn- op [kind & args] {:op kind :args (mapv expr args)})

(defn- input [k] {:op :input :key k})

(defn- coord [axis] {:op :coordinate :axis axis})

(def ^:private tau (* 2.0 Math/PI))

(defn- wave [phase] (op :add 0.5 (op :multiply 0.5 (op :sin (op :multiply tau phase)))))

(defn- through-water []
  ;; Two crossing wave trains travel in different directions through the field.
  (let [space #(op :multiply (coord %) (input :frequency))
        t (op :multiply (input :phase) (input :rate))
        a (wave (op :add (space :x) (op :multiply 0.31 (space :z)) t))
        b (wave (op :subtract (op :add (space :y) (op :multiply 0.73 (space :z)))
                              (op :multiply 0.61 t)))]
    {:name "Through water" :mode :multiply
     :inputs {:frequency 0.7 :rate 0.25 :depth 0.45 :phase {:op :beat}}
     :expression (op :mix 1.0 (op :multiply a b) (op :clamp (input :depth) 0.0 1.0))}))

(defn fog-optical-depth-expression
  "Dimensionless optical depth along a uniform segment of a light ray."
  [extinction density distance]
  (fog-law/optical-depth #(op :max 0.0 %) #(op :multiply %1 %2 %3)
                         extinction density distance))

(defn fog-transmission-expression
  "Fraction of unscattered light after travelling distance metres in uniform fog."
  [extinction density distance]
  (op :exp (op :subtract (fog-optical-depth-expression extinction density distance))))

(def library
  "Data-only prefab library. Each input default may be replaced by an expression.
  Phase is continuous in beats by default. A gel supplies linear RGB transmission."
  {:optics/through-water (through-water)
   :optics/fog-transmission {:name "Fog transmission" :mode :multiply
                             :inputs {:extinction 1.0 :density 0.0 :distance 1.0}
                             :expression (fog-transmission-expression
                                          (input :extinction) (input :density) (input :distance))}
   :optics/gel {:name "Color gel" :mode :multiply :inputs {:transmission [0.65 0.86 1.0]}
                :expression (op :clamp (input :transmission) 0.0 1.0)}
   :optics/ribbed-glass {:name "Ribbed glass" :mode :multiply
                         :inputs {:frequency 2.0 :transmission 0.65}
                         :glsl "mix(transmission, 1.0, 0.5 + 0.5 * sin(6.283185307179586 * position.x * frequency))"}
   :lfo/triangle {:name "Triangle" :mode :replace :inputs {:phase {:op :beat}}
                  :glsl "1.0 - abs(2.0 * fract(phase) - 1.0)"}
   :lfo/saw {:name "Saw" :mode :replace :inputs {:phase {:op :beat}} :glsl "fract(phase)"}
   :lfo/pulse {:name "Pulse" :mode :replace :inputs {:phase {:op :beat} :duty 0.5}
               :glsl "1.0 - floor(fract(phase) + (1.0 - clamp(duty, 0.0, 1.0)))"}
   :lfo/sine {:name "Sine" :mode :replace :inputs {:phase {:op :beat} :cycles 1.0 :offset 0.0}
              :expression (wave (op :add (input :offset) (op :multiply (input :cycles) (input :phase))))}})

(def ^:private axes [:x :y :z])

(defn- coordinate-nodes [mapping]
  (case mapping
    (nil :world) (mapv #(hash-map :op :position :axis %) axes)
    :surface-uv [{:op :surface-uv :axis :u} {:op :surface-uv :axis :v} (expr 0.0)]
    (do
      (when-not (and (vector? mapping) (<= 2 (count mapping) 3))
        (fail! [:coordinates] "Supply :world, :surface-uv, or two or three coordinate expressions"))
      (mapv expr (take 3 (concat mapping [0.0]))))))

(defn- substitute [tree inputs coordinates]
  (letfn [(visit [node depth]
            (when (> depth 64) (fail! [:expression] "Prefab expression exceeds 64 levels"))
            (let [{:keys [op key axis args] :as node} (expr node)]
              (case op
                :input (or (get inputs key) (fail! [:inputs key] "Undeclared prefab input"))
                :coordinate (case axis :x (coordinates 0) :y (coordinates 1) :z (coordinates 2)
                                  (fail! [:coordinates] "Coordinate axis must be x, y or z"))
                (if (contains? node :args)
                  (do (when-not (and (vector? args) (<= (count args) 64))
                        (fail! [:args] "Expected a vector of up to 64 arguments"))
                      (assoc node :args (mapv #(visit % (inc depth)) args)))
                  node))))]
    (visit tree 0)))

(defn- combine [mode before signal amount]
  (case mode
    :multiply (op :multiply before (if amount (op :mix 1.0 signal amount) signal))
    :add (op :add before (if amount (op :multiply amount signal) signal))
    :replace (if amount (op :mix before signal amount) signal)
    (fail! [:mode] "Expected :replace, :add or :multiply")))

(defn- stage [catalog prepare before {:keys [block mode inputs coordinates amount] :as spec}]
  (when-not (and (map? spec) (every? #{:block :mode :amount :coordinates :inputs} (keys spec)))
    (fail! [:stages] "Unknown stage field. Expected :block, :mode, :amount, :coordinates or :inputs"))
  (let [template (get catalog block)]
    (when-not template (fail! [:block] (str "Unknown effect block " block)))
    (when-not (and (or (nil? inputs) (map? inputs)) (every? (set (keys (:inputs template))) (keys inputs)))
      (fail! [:inputs] "Unknown prefab input"))
    (when (= (contains? template :glsl) (contains? template :expression))
      (fail! [:block block] "Supply one GLSL or IR expression per prefab"))
    (let [tree (if (contains? template :glsl) (glsl/expression (:glsl template)) (:expression template))
          bindings (update-vals (merge (:inputs template) inputs) expr)
          signal (prepare (substitute tree bindings (coordinate-nodes coordinates)))
          mode (or mode (:mode template))
          wet (when (contains? spec :amount) (prepare (expr amount)))]
      {:block block :signal signal :mode mode :amount wet :expression (combine mode before signal wet)})))

(defn plan
  "Return authored stage order and a single lowered :expression. An optional
  catalog extends the standard library with data-only prefab definitions."
  ([chain] (plan library chain))
  ([catalog chain] (plan catalog chain identity))
  ([catalog {:keys [base stages]} prepare]
   (when-not (and (some? base) (vector? stages) (<= (count stages) 32))
     (fail! [:stages] "A block chain needs a numeric base and up to 32 ordered stages"))
   (let [base (prepare (expr base))
         steps (reduce (fn [steps spec]
                         (conj steps (stage catalog prepare (or (:expression (peek steps)) base) spec)))
                       [] stages)]
     {:base base :stages steps :expression (or (:expression (peek steps)) base)})))

(defn- minus [a b]
  (cond (and (vector? a) (vector? b)) (mapv - a b)
        (vector? a) (mapv #(- % b) a)
        (vector? b) (mapv #(- a %) b)
        :else (- a b)))

(defn compile-trace
  "Compile a demand-driven inspector for a lowered, typed plan. Each stage
  evaluates its signal once and records its signed change from its own input."
  [{:keys [base stages]}]
  (let [dry (ir/compile-expression base)
        prepare (fn [{:keys [block signal mode amount expression]} before]
                  (let [previous {:op :param :key ::previous :type (ir/expression-type before)}
                        calculate (ir/compile-expression (combine mode previous signal amount))]
                    {:block block :calculate calculate :expression expression}))
        steps (mapv prepare stages (cons base (map :expression stages)))]
    (fn [env]
      (let [value (dry env)]
        (reduce (fn [{:keys [result] :as trace} {:keys [block calculate]}]
                  (let [next-value (calculate (assoc-in env [:params ::previous] result))]
                    (-> trace (assoc :result next-value)
                        (update :stages conj {:block block :offset (minus next-value result) :value next-value}))))
                {:base value :stages [] :result value} steps)))))

(defn middleware
  "Compile a chain onto a numeric context path. env-fn supplies the captured
  clock, position and parameters. The original leaf supplies the dry signal.
  Pass :vec2/3/4 for vector leaves. Writes only the resulting leaf."
  [catalog path type stages env-fn]
  (when-not (and (vector? path) (seq path)) (fail! [:path] "Supply a nonempty context path"))
  (let [base {:op :param :key ::dry :type type}
        lowered (plan catalog {:base base :stages stages})
        result-type (ir/expression-type (:expression lowered))
        evaluate (ir/compile-expression (:expression lowered))]
    (when-not (= type result-type) (fail! [:stages] "Middleware must preserve the destination type"))
    (fn [context]
      (let [env (assoc-in (env-fn context) [:params ::dry] (get-in context path))]
        (assoc-in context path (evaluate env))))))
