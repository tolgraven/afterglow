(ns afterglow.render.ir
  "Typed numeric map expressions with a CPU evaluator and GLSL ES 3 source output.

  Compilation/evaluation perform no I/O. GLSL generation does not submit GPU work
  or prove driver support. Values are finite scalars or vectors of 2–4 scalars;
  scalar arithmetic broadcasts to vectors. Time nodes return milliseconds; beat,
  bar and phrase nodes use explicit captured musical transport and meter."
  (:require [clojure.string :as str]))

(defn- invalid! [path message & [data]]
  (throw (ex-info message (merge {:type ::invalid-expression :path path :message message} data))))

(defn- finite? [x]
  (and (number? x) (Double/isFinite (double x))))

(defn- value-type [x]
  (cond (finite? x) :number
        (and (vector? x) (<= 2 (count x)) (<= (count x) 4) (every? finite? x))
        (case (count x) 2 :vec2 3 :vec3 4 :vec4)))

(defn- declared-type [x path]
  (let [t (case x (:float :scalar :number nil) :number x)]
    (when-not (#{:number :vec2 :vec3 :vec4} t)
      (invalid! path "Expected a numeric type: :number, :vec2, :vec3, or :vec4"))
    t))

(defn- width [t]
  (case t :number 1 :vec2 2 :vec3 3 :vec4 4))

(defn- common-type [types path]
  (let [vectors (set (remove #{:number} types))]
    (when (> (count vectors) 1)
      (invalid! path "Vector sizes must agree; only scalar broadcasting is supported"))
    (or (first vectors) :number)))

(defn- componentwise [f values]
  (if-let [v (first (filter vector? values))]
    (apply mapv f (map #(if (vector? %) % (repeat (count v) %)) values))
    (apply f values)))

(defn- checked [value expected path]
  (when-not (= expected (value-type value))
    (invalid! path "Expression produced a non-finite value or a value of the wrong type"
              {:expected expected :value value}))
  value)

(defn- decimal [x]
  (let [s (str (double x))]
    (str/replace s "E" "e")))

(defn- glsl-type [t] (if (= t :number) "float" (name t)))

(defn- literal [x]
  (if (vector? x)
    (str "vec" (count x) "(" (str/join ", " (map decimal x)) ")")
    (decimal x)))

(defn- cast-expression [node type]
  (if (= (:type node) type) (:glsl node)
      (str (glsl-type type) "(" (:glsl node) ")")))

(defn- fold-glsl [operator expressions function?]
  (reduce (fn [a b]
            (if function? (str operator "(" a ", " b ")")
                (str "(" a " " operator " " b ")"))) expressions))

(declare analyze)

(defn- arguments [node path depth arities]
  (let [args (:args node)]
    (when-not (and (vector? args) (arities (count args)))
      (invalid! (conj path :args) "Invalid argument count or non-vector :args"
                {:operation (:op node)}))
    (mapv (fn [i arg] (analyze arg (conj path :args i) (inc depth))) (range) args)))

(defn- collected [nodes]
  (reduce
   (fn [result node]
     (reduce-kv (fn [r k type]
                  (when (and (contains? r k) (not= (get r k) type))
                    (invalid! [] "A parameter is referenced with conflicting types" {:key k}))
                  (assoc r k type)) result (:params node))) {} nodes))

(defn- operation [node path depth]
  (let [op (:op node)
        unary? (#{:sin :cos :abs :floor :fract :sqrt} op)
        arities (cond unary? #{1}
                      (#{:clamp :mix} op) #{3}
                      (= :vec2 op) #{2}
                      (= :vec3 op) #{3}
                      (= :vec4 op) #{4}
                      (#{:divide :pow} op) #{2}
                      (= :subtract op) #{1 2}
                      :else #(<= 1 % 64))
        children (arguments node path depth arities)
        types (mapv :type children)
        type (if (#{:vec2 :vec3 :vec4} op)
               (do (when-not (every? #{:number} types)
                     (invalid! path "Vector constructors require scalar arguments")) op)
               (common-type types path))
        _ (when (and (= :mix op) (not= :number (last types)))
            (invalid! path "The mix fraction must be scalar"))
        exprs (mapv #(cast-expression % type) children)
        numeric-fn (case op
                     :add + :subtract - :multiply *
                     :divide (fn [a b] (when (zero? b) (invalid! path "Division by zero")) (/ a b))
                     :min min :max max
                     :sin #(Math/sin (double %)) :cos #(Math/cos (double %))
                     :abs #(Math/abs (double %)) :floor #(Math/floor (double %))
                     :fract #(- % (Math/floor (double %)))
                     :sqrt #(Math/sqrt (double %))
                     :pow (fn [a b]
                            ;; GLSL pow is undefined for negative bases, including
                            ;; integer exponents; keep the CPU oracle's domain aligned.
                            (when (or (neg? a) (and (zero? a) (not (pos? b))))
                              (invalid! path "Pow requires a nonnegative base and a positive exponent at zero"))
                            (Math/pow (double a) (double b)))
                     :clamp (fn [x lo hi]
                              (when (> lo hi) (invalid! path "Clamp lower bound exceeds upper bound"))
                              (min hi (max lo x)))
                     :mix (fn [a b amount] (+ (* (- 1.0 amount) a) (* amount b)))
                     nil)
        eval-fn (fn [env]
                  (let [values (mapv #((:evaluate %) env) children)]
                    (checked (if numeric-fn (componentwise numeric-fn values) values) type path)))
        expression (case op
                     :add (fold-glsl "+" exprs false)
                     :multiply (fold-glsl "*" exprs false)
                     :subtract (if (= 1 (count exprs)) (str "(-" (first exprs) ")")
                                   (fold-glsl "-" exprs false))
                     :divide (fold-glsl "/" exprs false)
                     :min (fold-glsl "min" exprs true)
                     :max (fold-glsl "max" exprs true)
                     (:vec2 :vec3 :vec4)
                     (str (name op) "(" (str/join ", " (map :glsl children)) ")")
                     :mix (str "mix(" (first exprs) ", " (second exprs) ", " (:glsl (last children)) ")")
                     (str (name op) "(" (str/join ", " exprs) ")"))]
    {:type type :evaluate eval-fn :glsl expression :params (collected children)}))

(defn- musical-value [node env path]
  (let [beat (checked (get env (if (= :absolute (:clock node :elapsed)) :beat :elapsed-beats)) :number path)
        beats-per-bar (get-in env [:meter :beats-per-bar])
        bars-per-phrase (get-in env [:meter :bars-per-phrase])]
    (when (and (#{:bar :phrase} (:op node))
               (not (and (finite? beats-per-bar) (pos? beats-per-bar))))
      (invalid! path "Musical bar/phrase requires positive finite meter beats-per-bar"))
    (when (and (= :phrase (:op node))
               (not (and (finite? bars-per-phrase) (pos? bars-per-phrase))))
      (invalid! path "Musical phrase requires positive finite meter bars-per-phrase"))
    (checked (case (:op node)
               :beat beat :bar (/ beat beats-per-bar)
               :phrase (/ (/ beat beats-per-bar) bars-per-phrase)) :number path)))

(defn- analyze [node path depth]
  (when (> depth 64) (invalid! path "Expression nesting exceeds 64 levels"))
  (when-not (map? node) (invalid! path "Expression nodes must be keyword maps"))
  (case (:op node)
    :const (let [value (:value node), type (value-type value)]
             (when-not type (invalid! (conj path :value) "Constants must be finite numbers or numeric vectors of length 2–4"))
             {:type type :evaluate (constantly value) :glsl (literal value) :params {}})
    :param (let [key (:key node), type (declared-type (:type node) (conj path :type))]
             (when-not (keyword? key) (invalid! (conj path :key) "Parameter keys must be keywords"))
             {:type type :params {key type}
              ;; Parameter placeholders are replaced with deterministic legal uniform names.
              :glsl (str "{{" (pr-str key) "}}")
              :evaluate (fn [env]
                          (when-not (contains? (:params env) key)
                            (invalid! path "Missing expression parameter" {:key key}))
                          (checked (get-in env [:params key]) type path))})
    :time (let [clock (:clock node :elapsed)]
            (when-not (#{:elapsed :absolute} clock) (invalid! path "Time :clock must be :elapsed or :absolute"))
            {:type :number :params {} :glsl (if (= clock :elapsed) "u_elapsed_ms" "u_time_ms")
             :evaluate (fn [env]
                         (checked (get env (if (= clock :elapsed) :elapsed-ms :time-ms)) :number path))})
    (:beat :bar :phrase)
    (let [clock (:clock node :elapsed)]
      (when-not (#{:elapsed :absolute} clock)
        (invalid! path "Musical :clock must be :elapsed or :absolute"))
      (let [beat (if (= clock :elapsed) "u_elapsed_beats" "u_beat")]
        {:type :number :params {}
         :glsl (case (:op node)
                 :beat beat :bar (str "(" beat " / u_beats_per_bar)")
                 :phrase (str "((" beat " / u_beats_per_bar) / u_bars_per_phrase)"))
         :evaluate (fn [env] (musical-value node env path))}))
    :position (let [axis (:axis node), index ({:x 0 :y 1 :z 2} axis)]
                (when-not index (invalid! path "Position axis must be :x, :y, or :z"))
                {:type :number :params {} :glsl (str "v_position." (name axis))
                 :evaluate (fn [env]
                             (checked (:position env) :vec3 path)
                             (nth (:position env) index))})
    (:add :subtract :multiply :divide :min :max :sin :cos :abs :floor :fract
     :sqrt :pow :clamp :mix :vec2 :vec3 :vec4)
    (operation node path depth)
    (invalid! (conj path :op) "Unknown expression operation" {:operation (:op node)})))

(defn- compile-node [expression]
  ;; Traverse first to cap total nodes independently of depth. No user code runs.
  (loop [pending [expression], count 0]
    (when (seq pending)
      (when (>= count 4096) (invalid! [] "Expression exceeds 4096 nodes"))
      (let [node (peek pending)]
        (recur (into (pop pending) (when (and (map? node) (vector? (:args node))) (:args node))) (inc count)))))
  (analyze expression [] 0))

(defn validate-expression
  "Return [] for a well-typed expression, otherwise [{:path ... :message ...}].
  Parameter types default to :number; vector parameters declare :type :vec3 etc.
  Values/domains depending on env are checked when evaluated."
  [expression]
  (try (compile-node expression) []
       (catch clojure.lang.ExceptionInfo error
         [(select-keys (ex-data error) [:path :message])])) )

(defn expression-type [expression]
  (:type (compile-node expression)))

(defn compile-expression
  "Compile a validated expression to a pure env -> finite value function.
  Env supplies :params, :position and requested :elapsed-ms/:time-ms clocks.
  Musical nodes use :beat/:elapsed-beats and :meter {:beats-per-bar b
  :bars-per-phrase p}. Bar/phrase values are continuous phases, not indices."
  [expression]
  (:evaluate (compile-node expression)))

(defn evaluate [expression env]
  ((compile-expression expression) env))

(definterface ScalarExpression
  (^double evalDouble [^doubles inputs]))

(defn- finite-result ^double [^double value path]
  (when-not (Double/isFinite value)
    (invalid! path "Expression produced a non-finite value"))
  value)

(defn- uniform-inputs
  "Frame inputs shared by every position, with source paths for diagnostics."
  [expression path]
  (case (:op expression)
    (:param :time :beat :bar :phrase)
    (let [{:keys [evaluate type]} (analyze expression path 0)]
      (for [component (range (width type))]
        [[expression component]
         (fn [env]
           (let [v (evaluate env)]
             (double (if (vector? v) (nth v component) v))))]))
    (mapcat (fn [index child] (uniform-inputs child (conj path :args index)))
            (range) (:args expression))))

(defn- scalar-component
  "Compile one float64 component without per-node value vectors or apply."
  [expression component path slots]
  (let [op (:op expression)
        value-at (fn [value] (double (if (vector? value) (nth value component) value)))]
    (case op
      :const (let [value (value-at (:value expression))]
               (reify ScalarExpression (evalDouble [_ _] value)))
      (:param :time :beat :bar :phrase)
      (let [slot (int (get slots [expression component]))]
        (reify ScalarExpression (evalDouble [_ inputs] (aget inputs slot))))
      :position (let [axis (int ({:x 0 :y 1 :z 2} (:axis expression)))]
                  (reify ScalarExpression (evalDouble [_ inputs] (aget inputs axis))))
      (:vec2 :vec3 :vec4) (scalar-component (nth (:args expression) component) 0 (conj path :args component) slots)
      (let [children (mapv (fn [index child]
                             (scalar-component child (if (= :number (expression-type child)) 0 component)
                                               (conj path :args index) slots))
                           (range) (:args expression))
            ^ScalarExpression a (nth children 0)
            ^ScalarExpression b (get children 1)
            ^ScalarExpression c (get children 2)
            n (count children)
            operation
            (case op
              (:add :multiply :min :max)
              (let [combine (case op
                              :add (fn ^double [^double x ^double y] (+ x y))
                              :multiply (fn ^double [^double x ^double y] (* x y))
                              :min (fn ^double [^double x ^double y] (min x y))
                              :max (fn ^double [^double x ^double y] (max x y)))]
                (reify ScalarExpression
                  (evalDouble [_ inputs]
                    (loop [index 1, value (.evalDouble a inputs)]
                      (if (= index n) value
                          (recur (inc index) (.invokePrim ^clojure.lang.IFn$DDD combine value
                                                          (.evalDouble ^ScalarExpression (nth children index) inputs))))))))
              :subtract (if (= n 1)
                          (reify ScalarExpression (evalDouble [_ inputs] (- (.evalDouble a inputs))))
                          (reify ScalarExpression (evalDouble [_ inputs] (- (.evalDouble a inputs) (.evalDouble b inputs)))))
              :divide (reify ScalarExpression
                        (evalDouble [_ inputs]
                          (let [x (.evalDouble a inputs), y (.evalDouble b inputs)]
                            (when (zero? y) (invalid! path "Division by zero")) (/ x y))))
              :sin (reify ScalarExpression (evalDouble [_ inputs] (Math/sin (.evalDouble a inputs))))
              :cos (reify ScalarExpression (evalDouble [_ inputs] (Math/cos (.evalDouble a inputs))))
              :abs (reify ScalarExpression (evalDouble [_ inputs] (Math/abs (.evalDouble a inputs))))
              :floor (reify ScalarExpression (evalDouble [_ inputs] (Math/floor (.evalDouble a inputs))))
              :fract (reify ScalarExpression (evalDouble [_ inputs] (let [x (.evalDouble a inputs)] (- x (Math/floor x)))))
              :sqrt (reify ScalarExpression (evalDouble [_ inputs] (Math/sqrt (.evalDouble a inputs))))
              :pow (reify ScalarExpression
                     (evalDouble [_ inputs]
                       (let [x (.evalDouble a inputs), y (.evalDouble b inputs)]
                         (when (or (neg? x) (and (zero? x) (not (pos? y))))
                           (invalid! path "Pow requires a nonnegative base and a positive exponent at zero"))
                         (Math/pow x y))))
              :clamp (reify ScalarExpression
                       (evalDouble [_ inputs]
                         (let [x (.evalDouble a inputs), lo (.evalDouble b inputs), hi (.evalDouble c inputs)]
                           (when (> lo hi) (invalid! path "Clamp lower bound exceeds upper bound"))
                           (min hi (max lo x)))))
              :mix (reify ScalarExpression
                     (evalDouble [_ inputs]
                       (let [x (.evalDouble a inputs), y (.evalDouble b inputs), amount (.evalDouble c inputs)]
                         (+ (* (- 1.0 amount) x) (* amount y))))))]
        (reify ScalarExpression
          (evalDouble [_ inputs] (finite-result (.evalDouble ^ScalarExpression operation inputs) path)))))))

(defn- validate-outputs! [outputs]
  (when-not (and (map? outputs) (seq outputs) (<= (count outputs) 64)
                 (every? keyword? (keys outputs)))
    (invalid! [] "Batch outputs must contain 1–64 named keyword expressions")))

(defn input-paths
  "Data read from env by a validated expression. Use these paths to bind pure
  calculations to captured parameters, positions and explicit musical clocks."
  [expression]
  (into []
        (comp (mapcat (fn [node]
                        (let [absolute? (= :absolute (:clock node))]
                          (case (:op node)
                            :param [[:params (:key node)]]
                            :position [[:position]]
                            :time [[(if absolute? :time-ms :elapsed-ms)]]
                            :beat [[(if absolute? :beat :elapsed-beats)]]
                            :bar [[(if absolute? :beat :elapsed-beats)] [:meter :beats-per-bar]]
                            :phrase [[(if absolute? :beat :elapsed-beats)]
                                     [:meter :beats-per-bar] [:meter :bars-per-phrase]]
                            []))))
              (distinct))
        (tree-seq #(and (map? %) (vector? (:args %))) :args expression)))

(defn- compile-field [slots {:keys [expression components] :as field}]
  (let [spatial? (some #(= :position (:op %)) (tree-seq #(vector? (:args %)) :args expression))]
    (-> field
        (dissoc :node :expression)
        (assoc :spatial? (boolean spatial?)
               :scalars (mapv #(scalar-component expression % [] slots) (range components))))))

(defn compile-batch
  "Compile named expressions to a reusable float64 CPU batch plan.

  outputs is a keyword -> expression map, for example {:color expr :aim expr
  :focus expr}. Fields retain their own type/component count, so aim and focus
  never share an overloaded RGBA buffer. Batch arithmetic converts inputs to
  float64; compare against the scalar oracle with the required application
  tolerance for exact-number inputs. This is not SIMD or GPU execution."
  [outputs]
  (validate-outputs! outputs)
  (let [nodes (mapv (fn [[attribute expression]]
                      (let [node (compile-node expression)]
                        {:attribute attribute :type (:type node) :components (width (:type node))
                         :node node :expression expression}))
                    (sort-by (comp str key) outputs))
        uniforms (vec (into {} (mapcat #(uniform-inputs (:expression %) []) nodes)))
        ;; Every invocation owns one double array. Slots 0–2 hold the current
        ;; xyz position; the remaining inputs stay fixed for the entire frame.
        slots (zipmap (map key uniforms) (iterate inc 3))]
    {:type ::batch
     :uniforms (mapv val uniforms)
     :params (collected (map :node nodes))
     :clocks (set (for [[_ expression] outputs
                        node (tree-seq #(and (map? %) (vector? (:args %))) :args expression)
                        :when (= :time (:op node))]
                    (if (= :absolute (:clock node :elapsed)) :time-ms :elapsed-ms)))
     :outputs (mapv #(compile-field slots %) nodes)}))

(def ^:private doubles-class (class (double-array 0)))

(defn- load-position!
  "Copy a finite world-space xyz triple into this evaluation's private storage."
  [positions flat? index ^doubles xyz]
  (if flat?
    (let [base (* (long index) 3)]
      (dotimes [axis 3]
        (let [value (aget ^doubles positions (+ base axis))]
          (when-not (Double/isFinite value)
            (invalid! [:positions index] "Position must contain three finite coordinates"))
          (aset xyz axis value))))
    (let [point (nth positions index)]
      (when-not (and (vector? point) (= 3 (count point)))
        (invalid! [:positions index] "Position must contain three finite coordinates"))
      (dotimes [axis 3]
        (let [value (nth point axis)]
          (when-not (finite? value)
            (invalid! [:positions index] "Position must contain three finite coordinates"))
          (aset xyz axis (double value)))))))

(defn evaluate-batch
  "Evaluate a compiled batch for ordered positions and return owned float64 fields.

  positions is either a vector of [x y z] vectors or a flat double-array of xyz
  triples. env supplies shared explicit time and parameters. The result is
  {:count n :outputs {attribute {:type t :components k :values double-array}}}.
  Each output is interleaved by head within that field and has an independent
  lifetime. No input is mutated. At most four million output components are
  allocated per invocation. The caller performs fixture conversion/DMX packing."
  [batch env positions]
  (when-not (and (map? batch) (= ::batch (:type batch)) (map? env))
    (invalid! [] "Expected a compiled batch plan and an explicit environment map"))
  (let [flat? (instance? doubles-class positions)
        count (cond flat? (do (when-not (zero? (mod (alength ^doubles positions) 3))
                               (invalid! [] "Flat batch positions must contain xyz triples"))
                             (quot (alength ^doubles positions) 3))
                    (vector? positions) (count positions)
                    :else (invalid! [] "Batch positions must be a vector of xyz vectors or a flat double-array"))
        components (reduce + (map :components (:outputs batch)))]
    (when (> (* (long count) components) 4000000)
      (invalid! [] "Batch exceeds four million output components"))
    (doseq [[key type] (:params batch)]
      (when-not (contains? (:params env) key) (invalid! [] "Missing expression parameter" {:key key}))
      (checked (get (:params env) key) type [:params key]))
    (doseq [clock (:clocks batch)] (checked (get env clock) :number [clock]))
    (let [fields (mapv (fn [output] (assoc output :values (double-array (* count (:components output))))) (:outputs batch))
          spatial-fields (filterv :spatial? fields)
          spatial-count (clojure.core/count spatial-fields)
          uniforms (:uniforms batch)
          inputs (double-array (+ 3 (clojure.core/count uniforms)))]
      ;; Whole-output expressions that depend only on time/params are shared by
      ;; every head. Compute them once instead of re-reading the same inputs N times.
      (when (pos? count)
        (dotimes [slot (clojure.core/count uniforms)]
          (aset inputs (+ slot 3) (double ((nth uniforms slot) env))))
        (doseq [{:keys [scalars components] :as field} (remove :spatial? fields)]
          (let [^doubles target (:values field), components (int components)]
            (dotimes [component components]
              (let [value (.evalDouble ^ScalarExpression (nth scalars component) inputs)]
                (if (= components 1)
                  (java.util.Arrays/fill target value)
                  (dotimes [index count]
                    (aset target (+ (* index components) component) value))))))))
      (dotimes [index count]
        (load-position! positions flat? index inputs)
        (dotimes [field-index spatial-count]
          (let [field (nth spatial-fields field-index), scalars (:scalars field)
                components (int (:components field)), base (* index components), ^doubles target (:values field)]
            (dotimes [component components]
              (aset target (+ base component)
                    (.evalDouble ^ScalarExpression (nth scalars component) inputs))))))
      {:count count
       :outputs (into {} (map (fn [field] [(:attribute field) (select-keys field [:type :components :values])]) fields))})))

(def ^:private time-inputs {:time-ms "u_time_ms" :elapsed-ms "u_elapsed_ms"})
(def ^:private numeric-contract
  {:cpu :float64 :gpu :float32 :requirements [:finite-float32-inputs :valid-operator-domains]})

(defn- shader-inputs [expressions]
  (reduce
   (fn [inputs {:keys [op clock value]}]
     (let [absolute? (= clock :absolute)]
       (case op
         :const (do (doseq [n (if (vector? value) value [value])]
                      (when (> (Math/abs (double n)) (double Float/MAX_VALUE))
                        (invalid! [] "Shader constants must fit finite float32 values" {:value n})))
                    inputs)
         :time (let [key (if absolute? :time-ms :elapsed-ms)]
                 (assoc inputs key (time-inputs key)))
         (:beat :bar :phrase)
         (cond-> (assoc inputs (if absolute? :beat :elapsed-beats)
                        (if absolute? "u_beat" "u_elapsed_beats"))
           (#{:bar :phrase} op) (assoc :beats-per-bar "u_beats_per_bar")
           (= op :phrase) (assoc :bars-per-phrase "u_bars_per_phrase"))
         :position (assoc inputs :position "v_position")
         inputs)))
   (sorted-map)
   (mapcat #(tree-seq (comp vector? :args) :args %) expressions)))

(defn- shader-uniforms [nodes]
  (into (sorted-map)
        (map-indexed (fn [index [key type]]
                       [key {:name (str "u_param_" index) :type type}]))
        (sort-by (comp str key) (collected nodes))))

(defn- bind-expression [node uniforms]
  (reduce-kv (fn [source key binding]
               (str/replace source (str "{{" (pr-str key) "}}") (:name binding)))
             (:glsl node) uniforms))

(defn- uniform-declarations [clock-inputs params]
  (str (apply str (for [[_ uniform] clock-inputs] (str "uniform float " uniform ";\n")))
       (apply str (for [[_ {:keys [name type]}] params]
                    (str "uniform " (glsl-type type) " " name ";\n")))))

(defn emit-glsl
  "Generate a complete GLSL ES 3 fragment shader and binding metadata.
  CPU doubles are the reference. Inputs and valid operator domains must also
  be representable on a float32 GPU."
  [expression]
  (let [node (compile-node expression)
        uniforms (shader-uniforms [node])
        inputs (merge (shader-inputs [expression]) time-inputs {:position "v_position"})
        source-expression (bind-expression node uniforms)
        result-type (:type node)
        result (case result-type
                 :number "vec4(vec3(value), 1.0)"
                 :vec2 "vec4(value, 0.0, 1.0)"
                 :vec3 "vec4(value, 1.0)"
                 :vec4 "value")]
    {:type result-type :expression source-expression :uniforms uniforms
     :inputs inputs :numeric-contract numeric-contract
     :source (str "#version 300 es\nprecision highp float;\n"
                  "uniform float u_time_ms;\nuniform float u_elapsed_ms;\nin vec3 v_position;\n"
                  (uniform-declarations (dissoc inputs :position :elapsed-ms :time-ms) uniforms)
                  "out vec4 fragColor;\nvoid main() {\n  " (glsl-type result-type)
                  " value = " source-expression ";\n  fragColor = " result ";\n}\n")}))

(defn emit-glsl-batch
  "Compile named fixture expressions to a vertex shader for interleaved transform
  feedback. Offsets and stride count floats. Each point is one fixture, with its
  world position at location 0. Bind the returned varying names in output order
  before linking. Compare stride to the device's interleaved component limit."
  [outputs]
  (validate-outputs! outputs)
  (let [ordered (sort-by (comp str key) outputs)
        nodes (mapv (comp compile-node val) ordered)
        inputs (shader-inputs (map val ordered))
        uniforms (shader-uniforms nodes)
        fields (mapv (fn [index [attribute _] {:keys [type]}]
                       {:attribute attribute :type type :components (width type)
                        :varying (str "out_" index)})
                     (range) ordered nodes)
        offsets (reductions + 0 (map :components fields))
        declarations (map (fn [{:keys [type varying]}]
                            (str "out " (glsl-type type) " " varying ";\n")) fields)
        assignments (map (fn [{:keys [varying]} node]
                           (str "  " varying " = " (bind-expression node uniforms) ";\n"))
                         fields nodes)]
    {:outputs (mapv #(assoc %1 :offset %2) fields offsets)
     :stride (last offsets) :inputs inputs :uniforms uniforms :numeric-contract numeric-contract
     :source (str "#version 300 es\n#ifdef GL_ES\nprecision highp float;\n#endif\n"
                  "layout(location = 0) in vec3 v_position;\n"
                  (uniform-declarations (dissoc inputs :position) uniforms)
                  (apply str declarations) "void main() {\n" (apply str assignments)
                  "  gl_Position = vec4(0.0, 0.0, 0.0, 1.0);\n}\n")}))
