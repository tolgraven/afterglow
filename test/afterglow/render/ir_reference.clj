(ns afterglow.render.ir-reference
  "The tree-walking float64 batch evaluator of `afterglow.render.ir` as of
  Afterglow ef539be0, kept unchanged as a bit-identity oracle.

  `ir/compile-batch` now shares structurally equal subexpressions and
  evaluates frame-constant work once per call (tolgraven/tolglow#872). That
  must not change one bit of any output or the message, data or order of any
  fault. Tests compare both evaluators on the same plans and inputs. Do not
  optimise this namespace."
  (:require [afterglow.render.ir :as ir]))

(def ^:private invalid! @#'ir/invalid!)

(def ^:private finite? @#'ir/finite?)

(def ^:private checked @#'ir/checked)

(def ^:private width @#'ir/width)

(def ^:private collected @#'ir/collected)

(def ^:private compile-node @#'ir/compile-node)

(def ^:private analyze @#'ir/analyze)

(def ^:private validate-outputs! @#'ir/validate-outputs!)

(definterface ReferenceExpression
  (^double evalDouble [^doubles inputs]))

(defn- finite-result ^double [^double value path]
  (when-not (Double/isFinite value)
    (invalid! path "Expression produced a non-finite value"))
  value)

(defn- uniform-inputs [expression path]
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

(defn- arithmetic-component [op children]
  (let [^ReferenceExpression a (first children)
        ^ReferenceExpression b (get children 1)
        n (count children)]
    (if (= n 2)
      (case op
        :add (reify ReferenceExpression (evalDouble [_ in] (+ (.evalDouble a in) (.evalDouble b in))))
        :multiply (reify ReferenceExpression (evalDouble [_ in] (* (.evalDouble a in) (.evalDouble b in))))
        :min (reify ReferenceExpression (evalDouble [_ in] (min (.evalDouble a in) (.evalDouble b in))))
        :max (reify ReferenceExpression (evalDouble [_ in] (max (.evalDouble a in) (.evalDouble b in)))))
      (let [combine (case op
                      :add (fn ^double [^double x ^double y] (+ x y))
                      :multiply (fn ^double [^double x ^double y] (* x y))
                      :min (fn ^double [^double x ^double y] (min x y))
                      :max (fn ^double [^double x ^double y] (max x y)))]
        (reify ReferenceExpression
          (evalDouble [_ in]
            (loop [index 1, value (.evalDouble a in)]
              (if (= index n) value
                  (recur (inc index) (.invokePrim ^clojure.lang.IFn$DDD combine value
                                                  (.evalDouble ^ReferenceExpression (nth children index) in)))))))))))

(defn- scalar-component [expression component path slots]
  (let [op (:op expression)
        value-at (fn [value] (double (if (vector? value) (nth value component) value)))]
    (case op
      :const (let [value (value-at (:value expression))]
               (reify ReferenceExpression (evalDouble [_ _] value)))
      (:param :time :beat :bar :phrase)
      (let [slot (int (get slots [expression component]))]
        (reify ReferenceExpression (evalDouble [_ inputs] (aget inputs slot))))
      :surface-uv (let [slot (int ({:u 3 :v 4} (:axis expression)))]
                    (reify ReferenceExpression (evalDouble [_ inputs] (aget inputs slot))))
      :position (let [axis (int ({:x 0 :y 1 :z 2} (:axis expression)))]
                  (reify ReferenceExpression (evalDouble [_ inputs] (aget inputs axis))))
      (:vec2 :vec3 :vec4) (scalar-component (nth (:args expression) component) 0 (conj path :args component) slots)
      (let [children (mapv (fn [index child]
                             (scalar-component child (if (= :number (ir/expression-type child)) 0 component)
                                               (conj path :args index) slots))
                           (range) (:args expression))
            ^ReferenceExpression a (nth children 0)
            ^ReferenceExpression b (get children 1)
            ^ReferenceExpression c (get children 2)
            n (count children)
            operation
            (case op
              (:add :multiply :min :max) (arithmetic-component op children)
              :subtract (if (= n 1)
                          (reify ReferenceExpression (evalDouble [_ inputs] (- (.evalDouble a inputs))))
                          (reify ReferenceExpression (evalDouble [_ inputs] (- (.evalDouble a inputs) (.evalDouble b inputs)))))
              :divide (reify ReferenceExpression
                        (evalDouble [_ inputs]
                          (let [x (.evalDouble a inputs), y (.evalDouble b inputs)]
                            (when (zero? y) (invalid! path "Division by zero")) (/ x y))))
              :sin (reify ReferenceExpression (evalDouble [_ inputs] (Math/sin (.evalDouble a inputs))))
              :cos (reify ReferenceExpression (evalDouble [_ inputs] (Math/cos (.evalDouble a inputs))))
              :abs (reify ReferenceExpression (evalDouble [_ inputs] (Math/abs (.evalDouble a inputs))))
              :floor (reify ReferenceExpression (evalDouble [_ inputs] (Math/floor (.evalDouble a inputs))))
              :fract (reify ReferenceExpression (evalDouble [_ inputs] (let [x (.evalDouble a inputs)] (- x (Math/floor x)))))
              :exp (reify ReferenceExpression (evalDouble [_ inputs] (Math/exp (.evalDouble a inputs))))
              :sqrt (reify ReferenceExpression (evalDouble [_ inputs] (Math/sqrt (.evalDouble a inputs))))
              :pow (reify ReferenceExpression
                     (evalDouble [_ inputs]
                       (let [x (.evalDouble a inputs), y (.evalDouble b inputs)]
                         (when (or (neg? x) (and (zero? x) (not (pos? y))))
                           (invalid! path "Pow requires a nonnegative base and a positive exponent at zero"))
                         (Math/pow x y))))
              :clamp (reify ReferenceExpression
                       (evalDouble [_ inputs]
                         (let [x (.evalDouble a inputs), lo (.evalDouble b inputs), hi (.evalDouble c inputs)]
                           (when (> lo hi) (invalid! path "Clamp lower bound exceeds upper bound"))
                           (min hi (max lo x)))))
              :mix (reify ReferenceExpression
                     (evalDouble [_ inputs]
                       (let [x (.evalDouble a inputs), y (.evalDouble b inputs), amount (.evalDouble c inputs)]
                         (+ (* (- 1.0 amount) x) (* amount y)))))
              :afterglow.render.ir/partial-max-blend
              (reify ReferenceExpression
                (evalDouble [_ inputs]
                  (let [x (.evalDouble a inputs), highest (max x (.evalDouble b inputs)), amount (.evalDouble c inputs)]
                    (+ x (* amount (- highest x)))))))]
        (reify ReferenceExpression
          (evalDouble [_ inputs] (finite-result (.evalDouble ^ReferenceExpression operation inputs) path)))))))

(defn- compile-field [slots {:keys [expression components] :as field}]
  (let [spatial? (some #(#{:position :surface-uv} (:op %)) (tree-seq #(vector? (:args %)) :args expression))]
    (-> field
        (dissoc :node :expression)
        (assoc :spatial? (boolean spatial?)
               :scalars (mapv #(scalar-component expression % [] slots) (range components))))))

(defn compile-batch
  "The ef539be0 `ir/compile-batch`: one closure tree per output component."
  [outputs]
  (validate-outputs! outputs)
  (let [nodes (mapv (fn [[attribute expression]]
                      (let [node (compile-node expression)]
                        {:attribute attribute :type (:type node) :components (width (:type node))
                         :node node :expression expression}))
                    (sort-by (comp str key) outputs))
        uniforms (vec (into {} (mapcat #(uniform-inputs (:expression %) []) nodes)))
        chart? (boolean (some #(some #{[:surface-uv]} (ir/input-paths %)) (vals outputs)))
        slots (zipmap (map key uniforms) (iterate inc (if chart? 5 3)))]
    {:type ::batch :surface-uv? chart?
     :uniforms (mapv val uniforms)
     :params (collected (map :node nodes))
     :clocks (set (for [[_ expression] outputs
                        node (tree-seq #(and (map? %) (vector? (:args %))) :args expression)
                        :when (= :time (:op node))]
                    (if (= :absolute (:clock node :elapsed)) :time-ms :elapsed-ms)))
     :outputs (mapv #(compile-field slots %) nodes)}))

(def ^:private doubles-class (class (double-array 0)))

(defn- invalid-position! [index]
  (invalid! [:positions index] "Position must contain three finite coordinates"))

(defn- load-position! [positions flat? ^long index ^doubles xyz]
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

(defn evaluate-batch
  "The ef539be0 `ir/evaluate-batch` for a plan from this namespace's compile-batch."
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
     (ir/validate-surface-uv-count! surface-uvs count)
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
           chart? (:surface-uv? batch)
           uv-flat? (instance? doubles-class surface-uvs)
           coordinates (if chart? 5 3)
           inputs (double-array (+ coordinates (clojure.core/count uniforms)))]
       (when (pos? count)
         (dotimes [slot (clojure.core/count uniforms)]
           (aset inputs (+ slot coordinates) (double ((nth uniforms slot) env))))
         (doseq [{:keys [scalars components] :as field} (remove :spatial? fields)]
           (let [^doubles target (:values field), components (int components)]
             (dotimes [component components]
               (let [value (.evalDouble ^ReferenceExpression (nth scalars component) inputs)]
                 (if (= components 1)
                   (java.util.Arrays/fill target value)
                   (dotimes [index count]
                     (aset target (+ (* index components) component) value))))))))
       (dotimes [index count]
         (load-position! positions flat? index inputs)
         (when chart? (load-uv! surface-uvs uv-flat? index inputs))
         (dotimes [field-index spatial-count]
           (let [field (nth spatial-fields field-index), scalars (:scalars field)
                 components (int (:components field)), base (* index components), ^doubles target (:values field)]
             (dotimes [component components]
               (aset target (+ base component)
                     (.evalDouble ^ReferenceExpression (nth scalars component) inputs))))))
       {:count count
        :outputs (into {} (map (fn [field] [(:attribute field) (select-keys field [:type :components :values])]) fields))}))))
