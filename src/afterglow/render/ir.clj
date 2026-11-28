(ns afterglow.render.ir
  "Typed numeric map expressions with a CPU evaluator and GLSL ES 3 source output.

  Compilation/evaluation perform no I/O. GLSL generation does not submit GPU work
  or prove driver support. Values are finite scalars or vectors of 2–4 scalars;
  scalar arithmetic broadcasts to vectors. Time nodes return milliseconds; beat,
  bar and phrase nodes use explicit captured musical transport and meter."
  (:require [clojure.string :as str])
  (:import [java.util ArrayList HashMap IdentityHashMap]))

(defrecord ^:private PartialMaxBlend [op args])

(defn partial-max-blend
  "Lower a chain blend with one reference to the previous expression.
  Authored numeric expressions cannot construct this internal node."
  [previous incoming amount]
  (->PartialMaxBlend ::partial-max-blend [previous incoming amount]))

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
        unary? (#{:sin :cos :abs :floor :fract :sqrt :exp} op)
        arities (cond unary? #{1}
                      (#{:clamp :mix ::partial-max-blend} op) #{3}
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
        _ (when (and (#{:mix ::partial-max-blend} op) (not= :number (last types)))
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
                     :exp #(Math/exp (double %))
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
                     ::partial-max-blend (fn [prior highest amount] (+ prior (* amount (- highest prior))))
                     nil)
        eval-fn (if (= ::partial-max-blend op)
                  (let [[previous incoming amount] (mapv :evaluate children)]
                    (fn [env]
                      (let [prior (previous env)
                            highest (componentwise max [prior (incoming env)])]
                        (checked (componentwise numeric-fn [prior highest (amount env)]) type path))))
                  (fn [env]
                    (let [values (mapv #((:evaluate %) env) children)]
                      (checked (if numeric-fn (componentwise numeric-fn values) values) type path))))
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
                     ::partial-max-blend
                     (str "afterglow_max_blend(" (first exprs) ", " (second exprs) ", " (:glsl (last children)) ")")
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
    :surface-uv
    (let [axis (:axis node) index ({:u 0 :v 1} axis)]
      (when-not index (invalid! path "Surface coordinate axis must be :u or :v"))
      {:type :number :params {} :glsl (str "v_uv." (["x" "y"] index))
       :evaluate (fn [{:keys [surface-uv position]}]
                   (if (some? surface-uv)
                     (nth (checked surface-uv :vec2 path) index)
                     (nth (checked position :vec3 path) index)))})
    :position (let [axis (:axis node), index ({:x 0 :y 1 :z 2} axis)]
                (when-not index (invalid! path "Position axis must be :x, :y, or :z"))
                {:type :number :params {} :glsl (str "v_position." (name axis))
                 :evaluate (fn [env]
                             (checked (:position env) :vec3 path)
                             (nth (:position env) index))})
    (:add :subtract :multiply :divide :min :max :sin :cos :abs :floor :fract
     :sqrt :exp :pow :clamp :mix :vec2 :vec3 :vec4)
    (operation node path depth)
    ::partial-max-blend
    (if (instance? PartialMaxBlend node)
      (operation node path depth)
      (invalid! (conj path :op) "Unknown expression operation" {:operation (:op node)}))
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

(definterface Instruction
  (^void run [^doubles registers]))

(defmacro ^:private store!
  "Write one result to its register after the operation's own domain checks,
  failing at the expression path that produced a non-finite value."
  [registers out path value]
  `(let [value# ~value]
     (when-not (Double/isFinite value#)
       (invalid! ~path "Expression produced a non-finite value"))
     (aset ~registers ~out value#)))

(defn- uniform-inputs
  "Frame inputs shared by every position, with source paths for diagnostics."
  [expression path]
  (case (:op expression)
    (:const :position :surface-uv) []
    (:param :time :beat :bar :phrase)
    (let [{:keys [evaluate type]} (analyze expression path 0)]
      (for [component (range (width type))]
        [[expression component]
         (fn [env]
           (let [v (evaluate env)]
             (double (if (vector? v) (nth v component) v))))]))
    (mapcat (fn [index child] (uniform-inputs child (conj path :args index)))
            (range) (:args expression))))

(defmacro ^:private fold
  "Fold register values left from the first operand, in authored order."
  [operator r args n first-operand]
  `(loop [i# 1, v# (aget ~r ~first-operand)]
     (if (= i# ~n) v# (recur (inc i#) (~operator v# (aget ~r (aget ~args i#)))))))

(defn- fold-instruction
  "An :add, :multiply, :min or :max over other than two operands folds left
  in authored order and checks only its final value."
  [op ^ints args out path]
  (let [n (alength args), a (aget args 0), out (int out)]
    (case op
      :add (reify Instruction (run [_ r] (store! r out path (double (fold + r args n a)))))
      :multiply (reify Instruction (run [_ r] (store! r out path (double (fold * r args n a)))))
      :min (reify Instruction (run [_ r] (store! r out path (double (fold min r args n a)))))
      :max (reify Instruction (run [_ r] (store! r out path (double (fold max r args n a))))))))

(defn- instruction
  "One float64 operation reading its operands' registers and writing its own.
  The arithmetic and checks are those of the scalar oracle, in the same order."
  [op ^ints args out path]
  (let [n (alength args), out (int out)
        a (int (if (> n 0) (aget args 0) 0))
        b (int (if (> n 1) (aget args 1) 0))
        c (int (if (> n 2) (aget args 2) 0))]
    (case op
      (:add :multiply :min :max)
      (if (= n 2)
        (case op
          :add (reify Instruction (run [_ r] (store! r out path (+ (aget r a) (aget r b)))))
          :multiply (reify Instruction (run [_ r] (store! r out path (* (aget r a) (aget r b)))))
          :min (reify Instruction (run [_ r] (store! r out path (min (aget r a) (aget r b)))))
          :max (reify Instruction (run [_ r] (store! r out path (max (aget r a) (aget r b))))))
        (fold-instruction op args out path))
      :subtract (if (= n 1)
                  (reify Instruction (run [_ r] (store! r out path (- (aget r a)))))
                  (reify Instruction (run [_ r] (store! r out path (- (aget r a) (aget r b))))))
      :divide (reify Instruction
                (run [_ r]
                  (let [x (aget r a), y (aget r b)]
                    (when (zero? y) (invalid! path "Division by zero"))
                    (store! r out path (/ x y)))))
      :sin (reify Instruction (run [_ r] (store! r out path (Math/sin (aget r a)))))
      :cos (reify Instruction (run [_ r] (store! r out path (Math/cos (aget r a)))))
      :abs (reify Instruction (run [_ r] (store! r out path (Math/abs (aget r a)))))
      :floor (reify Instruction (run [_ r] (store! r out path (Math/floor (aget r a)))))
      :fract (reify Instruction (run [_ r] (store! r out path (let [x (aget r a)] (- x (Math/floor x))))))
      :exp (reify Instruction (run [_ r] (store! r out path (Math/exp (aget r a)))))
      :sqrt (reify Instruction (run [_ r] (store! r out path (Math/sqrt (aget r a)))))
      :pow (reify Instruction
             (run [_ r]
               (let [x (aget r a), y (aget r b)]
                 (when (or (neg? x) (and (zero? x) (not (pos? y))))
                   (invalid! path "Pow requires a nonnegative base and a positive exponent at zero"))
                 (store! r out path (Math/pow x y)))))
      :clamp (reify Instruction
               (run [_ r]
                 (let [x (aget r a), lo (aget r b), hi (aget r c)]
                   (when (> lo hi) (invalid! path "Clamp lower bound exceeds upper bound"))
                   (store! r out path (min hi (max lo x))))))
      :mix (reify Instruction
             (run [_ r]
               (let [x (aget r a), y (aget r b), amount (aget r c)]
                 (store! r out path (+ (* (- 1.0 amount) x) (* amount y))))))
      ::partial-max-blend
      (reify Instruction
        (run [_ r]
          (let [x (aget r a), highest (max x (aget r b)), amount (aget r c)]
            (store! r out path (+ x (* amount (- highest x))))))))))

(defn- type-of
  "Type of a validated subexpression, memoised by identity for one compilation."
  [^IdentityHashMap types expression]
  (or (.get types expression)
      (let [type (case (:op expression)
                   :const (value-type (:value expression))
                   :param (declared-type (:type expression) [])
                   (:vec2 :vec3 :vec4) (:op expression)
                   (:time :beat :bar :phrase :surface-uv :position) :number
                   (common-type (mapv #(type-of types %) (:args expression)) []))]
        (.put types expression type)
        type)))

(defn- intern-node!
  "Register of the node with this key, adding it after its operands if new."
  [{:keys [^HashMap index ^ArrayList nodes first-register]} key spatial? make]
  (if-let [register (.get index key)]
    register
    (let [register (long (+ (long first-register) (.size nodes)))]
      (.add nodes {:spatial? spatial? :instruction (make register)})
      (.put index key register)
      register)))

(defn- spatial-register?
  "Whether a register's value depends on the head's coordinates."
  [{:keys [^ArrayList nodes first-register coordinates]} ^long register]
  (cond (< register (long coordinates)) true
        (< register (long first-register)) false
        :else (:spatial? (.get nodes (- register (long first-register))))))

(defn- scalar-node!
  "Register holding one float64 component of a validated expression.
  Registers 0–2 hold the head's xyz and 3–4 its chart UV; frame inputs follow.
  An operation on the same operand registers as an earlier one shares its
  register, so each structurally equal subexpression is computed once. Nodes
  are added in post-order, the order the tree-walking evaluator visits them,
  and keep the path of their first occurrence for fault reports."
  [state expression component path]
  (case (:op expression)
    :const (let [v (:value expression)
                 value (double (if (vector? v) (nth v component) v))]
             ;; Raw bits keep 0.0 and -0.0 apart.
             (intern-node! state [:const (Double/doubleToRawLongBits value)] false
                           (fn [out] (let [out (int out)] (reify Instruction (run [_ r] (aset r out value)))))))
    (:param :time :beat :bar :phrase) (long (get (:slots state) [expression component]))
    :surface-uv (long ({:u 3 :v 4} (:axis expression)))
    :position (long ({:x 0 :y 1 :z 2} (:axis expression)))
    (:vec2 :vec3 :vec4) (scalar-node! state (nth (:args expression) component) 0 (conj path :args component))
    (let [op (:op expression)
          args (mapv (fn [index child]
                       (scalar-node! state child (if (= :number (type-of (:types state) child)) 0 component)
                                     (conj path :args index)))
                     (range) (:args expression))]
      (intern-node! state (into [op] args) (boolean (some #(spatial-register? state %) args))
                    (fn [out] (instruction op (int-array args) out path))))))

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
                            :surface-uv [[:surface-uv] [:position]]
                            :position [[:position]]
                            :time [[(if absolute? :time-ms :elapsed-ms)]]
                            :beat [[(if absolute? :beat :elapsed-beats)]]
                            :bar [[(if absolute? :beat :elapsed-beats)] [:meter :beats-per-bar]]
                            :phrase [[(if absolute? :beat :elapsed-beats)]
                                     [:meter :beats-per-bar] [:meter :bars-per-phrase]]
                            []))))
              (distinct))
        (tree-seq #(and (map? %) (vector? (:args %))) :args expression)))

(defn- reads-coordinates? [expression]
  (boolean (some #(#{:position :surface-uv} (:op %)) (tree-seq #(vector? (:args %)) :args expression))))

(defn compile-batch
  "Compile named expressions to a reusable float64 CPU batch plan.

  outputs is a keyword -> expression map, for example {:color expr :aim expr
  :focus expr}. Fields retain their own type/component count, so aim and focus
  never share an overloaded RGBA buffer. Batch arithmetic converts inputs to
  float64; compare against the scalar oracle with the required application
  tolerance for exact-number inputs. This is not SIMD or GPU execution.

  Every scalar component of every field compiles into one register program.
  A structurally equal subexpression, wherever it appears in the batch, is one
  instruction. Instructions that read no coordinate run once per evaluation,
  before the head loop, and a component that reads no coordinate is filled
  once. Each value still comes from the same operations on the same operands
  in the same order, so results are bit-identical to evaluating every tree at
  every head, and faults keep their message, data and the order they surface in."
  [outputs]
  (validate-outputs! outputs)
  (let [nodes (mapv (fn [[attribute expression]]
                      (let [node (compile-node expression)]
                        {:attribute attribute :type (:type node) :components (width (:type node))
                         :node node :expression expression :spatial? (reads-coordinates? expression)}))
                    (sort-by (comp str key) outputs))
        uniforms (vec (into {} (mapcat #(uniform-inputs (:expression %) []) nodes)))
        ;; Every invocation owns one double array of registers. Registers 0–2
        ;; hold the current xyz position (3–4 its chart UV); frame inputs and
        ;; then the compiled operations follow.
        chart? (boolean (some #(some #{[:surface-uv]} (input-paths %)) (vals outputs)))
        coordinates (if chart? 5 3)
        slots (zipmap (map key uniforms) (iterate inc coordinates))
        state {:index (HashMap.) :nodes (ArrayList.) :types (IdentityHashMap.) :slots slots
               :coordinates coordinates :first-register (+ coordinates (count uniforms))}
        build (fn [fields]
                (into {} (map (fn [{:keys [attribute expression components]}]
                                [attribute (mapv #(scalar-node! state expression % []) (range components))]))
                      fields))
        ;; Build in evaluation order: fields that read no coordinate are
        ;; evaluated first, as they always were, then the spatial fields.
        constant-roots (build (remove :spatial? nodes))
        prefix-count (.size ^ArrayList (:nodes state))
        spatial-roots (build (filter :spatial? nodes))
        program (vec (:nodes state))
        later (subvec program prefix-count)
        roots (merge constant-roots spatial-roots)]
    {:type ::batch :surface-uv? chart?
     :uniforms (mapv val uniforms)
     :params (collected (map :node nodes))
     :clocks (set (for [[_ expression] outputs
                        node (tree-seq #(and (map? %) (vector? (:args %))) :args expression)
                        :when (= :time (:op node))]
                    (if (= :absolute (:clock node :elapsed)) :time-ms :elapsed-ms)))
     :registers (+ (long (:first-register state)) (count program))
     ;; Operations of the frame-constant fields, then the remaining operations
     ;; that read no coordinate, then those run at every head. :first-head
     ;; replays every operation of the spatial fields in visiting order; it only
     ;; runs to raise a frame-constant fault where an unhoisted evaluation would.
     :constant-fields (mapv :instruction (subvec program 0 prefix-count))
     :hoisted (into [] (comp (remove :spatial?) (map :instruction)) later)
     :per-head (into [] (comp (filter :spatial?) (map :instruction)) later)
     :first-head (mapv :instruction later)
     :outputs (mapv (fn [{:keys [attribute] :as field}]
                      (let [registers (get roots attribute)]
                        (-> (select-keys field [:attribute :type :components :spatial?])
                            (assoc :roots registers
                                   :per-head (filterv #(spatial-register? state (nth registers %))
                                                      (range (count registers)))))))
                    nodes)}))

(def ^:private doubles-class (class (double-array 0)))

(defn- invalid-position! [index]
  (invalid! [:positions index] "Position must contain three finite coordinates"))

(defn- load-position!
  "Copy a finite world-space xyz triple into this evaluation's private storage."
  [positions flat? ^long index ^doubles xyz]
  (if flat?
    (let [base (* (long index) 3)]
      (dotimes [axis 3]
        (let [value (aget ^doubles positions (+ base axis))]
          (when-not (Double/isFinite value)
            (invalid-position! index))
          (aset xyz axis value))))
    (let [point (nth positions index)]
      (when-not (and (vector? point) (= 3 (count point)))
        (invalid-position! index))
      (dotimes [axis 3]
        (let [value (nth point axis)]
          (when-not (finite? value)
            (invalid-position! index))
          (aset xyz axis (double value)))))))

(defn validate-surface-uv-count! [uvs n]
  (when-not (or (nil? uvs)
                (and (vector? uvs) (= (count uvs) n))
                (and (instance? doubles-class uvs) (= (alength ^doubles uvs) (* 2 (long n)))))
    (invalid! [:surface-uvs] "Supply one optional [u v] per head or a flat double-array of UV pairs")))

(defn- load-uv! [uvs flat? ^long index ^doubles inputs]
  (if flat?
    (let [base (* (long index) 2)]
      (dotimes [axis 2]
        (let [v (aget ^doubles uvs (+ base axis))]
          (when-not (Double/isFinite v) (invalid! [:surface-uvs index] "Expected finite UV coordinates"))
          (aset inputs (+ 3 axis) v))))
    (let [uv (when uvs (nth uvs index))]
      (if (nil? uv)
        (do (aset inputs 3 (aget inputs 0))
            (aset inputs 4 (aget inputs 1)))
        (do (checked uv :vec2 [:surface-uvs index])
            (aset inputs 3 (double (nth uv 0)))
            (aset inputs 4 (double (nth uv 1))))))))

(defn- execute! [instructions ^doubles registers]
  (doseq [instruction instructions]
    (.run ^Instruction instruction registers)))

(defn- fill-component!
  "Write one frame-constant register to a component at every head."
  [{:keys [components roots values]} component ^doubles registers ^long n]
  (let [^doubles target values, components (int components), component (int component)
        value (aget registers (int (nth roots component)))]
    (if (= components 1)
      (java.util.Arrays/fill target value)
      (dotimes [index n]
        (aset target (+ (* index components) component) value)))))

(defn- run-batch!
  "Evaluate a validated plan into freshly allocated fields."
  [batch env positions flat? surface-uvs n fields]
  (let [n (long n)
        uniforms (:uniforms batch)
        chart? (:surface-uv? batch)
        uv-flat? (instance? doubles-class surface-uvs)
        coordinates (if chart? 5 3)
        registers (double-array (:registers batch))
        spatial (filterv :spatial? fields)]
    (when (pos? n)
      (dotimes [slot (count uniforms)]
        (aset registers (+ slot coordinates) (double ((nth uniforms slot) env))))
      ;; Whole-output expressions that depend only on time/params are shared by
      ;; every head. Compute them once instead of re-reading the same inputs N times.
      (execute! (:constant-fields batch) registers)
      (doseq [field fields :when (not (:spatial? field))
              component (range (:components field))]
        (fill-component! field component registers n))
      (try (execute! (:hoisted batch) registers)
           (catch clojure.lang.ExceptionInfo error
             ;; Without hoisting this fault would surface at the first head,
             ;; after its coordinates load and after any earlier fault there.
             ;; Replay that head unhoisted so the same first fault is raised.
             (load-position! positions flat? 0 registers)
             (when chart? (load-uv! surface-uvs uv-flat? 0 registers))
             (execute! (:first-head batch) registers)
             (throw error)))
      (doseq [field spatial
              component (remove (set (:per-head field)) (range (:components field)))]
        (fill-component! field component registers n)))
    (let [^objects program (object-array (:per-head batch))
          steps (alength program)
          stores (vec (for [field spatial, component (:per-head field)] [field component]))
          ^objects targets (object-array (map #(:values (first %)) stores))
          ^ints sources (int-array (map (fn [[field component]] (nth (:roots field) component)) stores))
          ^ints strides (int-array (map #(:components (first %)) stores))
          ^ints offsets (int-array (map second stores))
          store-count (alength sources)]
      (dotimes [index n]
        (load-position! positions flat? index registers)
        (when chart? (load-uv! surface-uvs uv-flat? index registers))
        (dotimes [step steps]
          (.run ^Instruction (aget program step) registers))
        (dotimes [k store-count]
          (aset ^doubles (aget targets k) (+ (* index (aget strides k)) (aget offsets k))
                (aget registers (aget sources k))))))))

(defn evaluate-batch
  "Evaluate a compiled batch for ordered positions and return owned float64 fields.

  positions is either a vector of [x y z] vectors or a flat double-array of xyz
  triples. Optional surface-uvs supplies one [u v] or nil per position, or a flat
  double-array of pairs. A head without a chart uses its world x/y. env supplies
  shared explicit time and parameters. The result is
  {:count n :outputs {attribute {:type t :components k :values double-array}}}.
  Each output is interleaved by head within that field and has an independent
  lifetime. No input is mutated. At most four million output components are
  allocated per invocation. The caller performs fixture conversion/DMX packing."
  ([batch env positions] (evaluate-batch batch env positions nil))
  ([batch env positions surface-uvs]
  (when-not (and (map? batch) (= ::batch (:type batch)) (map? env))
    (invalid! [] "Expected a compiled batch plan and an explicit environment map"))
  (let [flat? (instance? doubles-class positions)
        count (cond flat? (do (when-not (zero? (mod (alength ^doubles positions) 3))
                               (invalid! [] "Flat batch positions must contain xyz triples"))
                             (quot (alength ^doubles positions) 3))
                    (vector? positions) (count positions)
                    :else (invalid! [] "Batch positions must be a vector of xyz vectors or a flat double-array"))
        components (reduce + (map :components (:outputs batch)))]
    (validate-surface-uv-count! surface-uvs count)
    (when (> (* (long count) components) 4000000)
      (invalid! [] "Batch exceeds four million output components"))
    (doseq [[key type] (:params batch)]
      (when-not (contains? (:params env) key) (invalid! [] "Missing expression parameter" {:key key}))
      (checked (get (:params env) key) type [:params key]))
    (doseq [clock (:clocks batch)] (checked (get env clock) :number [clock]))
    (let [fields (mapv (fn [output] (assoc output :values (double-array (* count (:components output))))) (:outputs batch))]
      (run-batch! batch env positions flat? surface-uvs count fields)
      {:count count
       :outputs (into {} (map (fn [field] [(:attribute field) (select-keys field [:type :components :values])]) fields))}))))

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
         :surface-uv (assoc inputs :surface-uv "v_uv")
         :position (assoc inputs :position "v_position")
         ::partial-max-blend (assoc inputs ::partial-max-blend true)
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

(defn- shader-helpers [used]
  (when (::partial-max-blend used)
    (apply str (for [type ["float" "vec2" "vec3" "vec4"]]
                 (str type " afterglow_max_blend(" type " prior, " type " incoming, float amount) {\n"
                      "  return prior + amount * (max(prior, incoming) - prior);\n}\n")))))

(defn emit-glsl
  "Generate a complete GLSL ES 3 fragment shader and binding metadata.
  CPU doubles are the reference. Inputs and valid operator domains must also
  be representable on a float32 GPU."
  ([expression] (emit-glsl expression :world))
  ([expression coordinates]
  (when-not (#{:world :surface-uv} coordinates) (invalid! [:coordinates] "Expected :world or :surface-uv"))
  (let [used (shader-inputs [expression])
        mapped? (contains? used :surface-uv)
        uv-only? (and (= coordinates :surface-uv) (not mapped?))
        input-declaration (if uv-only?
                            "in vec2 v_uv;\n#define v_position vec3(v_uv, 0.0)\n"
                            (str "in vec3 v_position;\n" (when mapped? "in vec2 v_uv;\n")))
        node (compile-node expression)
        uniforms (shader-uniforms [node])
        inputs (assoc (merge (dissoc used ::partial-max-blend) time-inputs)
                      :position (if uv-only? "v_uv" "v_position"))
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
                  "uniform float u_time_ms;\nuniform float u_elapsed_ms;\n" input-declaration
                  (uniform-declarations (dissoc inputs :position :surface-uv :elapsed-ms :time-ms) uniforms)
                  "out vec4 fragColor;\n" (shader-helpers used)
                  "void main() {\n  " (glsl-type result-type)
                  " value = " source-expression ";\n  fragColor = " result ";\n}\n")})))

(defn emit-glsl-batch
  "Compile named fixture expressions to a vertex shader for interleaved transform
  feedback. Offsets and stride count floats. Each point is one fixture, with its
  world position at location 0. When a material samples UVs, :surface-uv? true
  adds an independent vec2 at location 1. Its default uses world x/y for UV.
  Bind the returned varying names in output order
  before linking. Compare stride to the device's interleaved component limit."
  ([outputs] (emit-glsl-batch outputs {}))
  ([outputs {:keys [surface-uv?]}]
  (validate-outputs! outputs)
  (let [ordered (sort-by (comp str key) outputs)
        nodes (mapv (comp compile-node val) ordered)
        used (shader-inputs (map val ordered))
        mapped? (contains? used :surface-uv)
        chart? (and mapped? surface-uv?)
        inputs (cond-> (dissoc used ::partial-max-blend)
                 (and mapped? (not chart?)) (-> (dissoc :surface-uv) (assoc :position "v_position")))
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
                  (when mapped? (if chart? "layout(location = 1) in vec2 v_uv;\n" "#define v_uv v_position.xy\n"))
                  (uniform-declarations (dissoc inputs :position :surface-uv) uniforms)
                  (apply str declarations) (shader-helpers used) "void main() {\n" (apply str assignments)
                  "  gl_Position = vec4(0.0, 0.0, 0.0, 1.0);\n}\n")})))
