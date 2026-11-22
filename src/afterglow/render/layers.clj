(ns afterglow.render.layers
  "Pure composition of native fixture fields. The frame renderer supplies validated
  assignment/batch rows and performs geometry and channel packing after composition."
  (:require [afterglow.runtime.faults :as faults]
            [thi.ng.color.core :as color]))

(defn- fail! [msg data] (throw (ex-info msg data)))
(defn- finite? [x] (and (number? x) (Double/isFinite (double x))))
(defn- unit? [x] (and (finite? x) (<= 0 x 1)))
(defn- xyz? [v] (and (vector? v) (= 3 (count v)) (every? finite? v)))
(defn- color? [x] (and (record? x) (satisfies? color/IRGBConvert x)))
(defn- rgb [x]
  (if (color? x)
    (let [c (color/as-rgba x)] [(:r c) (:g c) (:b c)])
    x))
(defn- typed [attribute value]
  (if (= attribute :color)
    (let [v (rgb value)]
      (when-not (and (xyz? v) (every? unit? v))
        (fail! "A light color requires three normalized components" {:attribute attribute :value v}))
      (if (color? value) value (color/rgba v)))
    value))

(def ^:private reads #{:previous :incoming :field})
(def ^:private operators #{:add :multiply :divide :rotate-y :rotate-hue})
(defn- validate-expr! [x depth]
  (cond
    (> depth 32) (fail! "Layer expression is too deeply nested" {})
    (or (finite? x) (xyz? x) (color? x)) nil
    (and (map? x) (reads (:op x)) (keyword? (:attribute x)))
    (when (contains? x :default) (validate-expr! (:default x) (inc depth)))
    (and (map? x) (operators (:op x)) (vector? (:args x)) (= 2 (count (:args x))))
    (doseq [child (:args x)] (validate-expr! child (inc depth)))
    :else (fail! "Invalid native layer expression" {:expression x})))

(defn validate-transforms!
  "Validate the portable slot transform program and return it for storage."
  [steps]
  (when-not (and (vector? steps) (<= (count steps) 128))
    (fail! "Expected up to 128 ordered layer transforms" {}))
  (doseq [{:keys [attribute value]} steps]
    (when-not (keyword? attribute) (fail! "Layer transform needs a field" {:attribute attribute}))
    (validate-expr! value 0))
  steps)

(defn- arithmetic [op a b]
  (let [f (case op :add + :multiply * :divide /)
        x (rgb a) y (rgb b)
        result (cond
                 (and (finite? x) (finite? y)) (f x y)
                 (and (xyz? x) (xyz? y)) (mapv f x y)
                 (and (xyz? x) (finite? y)) (mapv #(f % y) x)
                 (and (finite? x) (xyz? y)) (mapv #(f x %) y)
                 :else (fail! "Expected scalar, color or vector operands" {:op op}))]
    (if (or (color? a) (color? b)) (typed :color result) result)))

(defn- evaluate [expr env]
  (if (or (not (map? expr)) (color? expr))
    expr
    (let [{:keys [op attribute args]} expr]
      (if (reads op)
        (if-some [x (get-in env [op attribute])]
          x
          (if (contains? expr :default) (evaluate (:default expr) env)
              (fail! "Native layer field has no value for this target" {:op op :attribute attribute})))
        (let [[a b] (mapv #(evaluate % env) args)]
          (case op
            (:add :multiply :divide) (arithmetic op a b)
            :rotate-y (do (when-not (and (xyz? a) (finite? b)) (fail! "rotate-y needs a vector and radians" {}))
                          (let [[x y z] a c (Math/cos b) s (Math/sin b)]
                            [(+ (* x c) (* z s)) y (- (* z c) (* x s))]))
            :rotate-hue (do (when-not (finite? b) (fail! "rotate-hue needs a color and turns" {}))
                            (color/rotate-hue (typed :color a) (* 2.0 Math/PI b)))))))))

(defn- over [blend-value field before value blend opacity]
  (typed field (blend-value (rgb before) (rgb value) blend opacity)))

(defn- set-assignment [blend-value validate! fields {:keys [attribute value blend opacity] :as a}]
  (let [value (typed attribute value)
        opacity (get a :opacity 1)
        blend (get a :blend :replace)]
    (if (= :beat-ratio attribute)
      (when-not (and (finite? value) (unit? opacity) (#{:replace :max :add} blend))
        (fail! "Invalid beat-ratio contribution" {:assignment a}))
      (validate! (assoc a :value (rgb value))))
    (if (zero? opacity)
      fields
      (let [result (over blend-value attribute (get fields attribute) value blend opacity)]
        (if (= :beat-ratio attribute)
          (when-not (finite? result) (fail! "Beat-ratio arithmetic overflow" {:assignment a}))
          (validate! (assoc a :value (rgb result))))
        (assoc fields attribute result)))))

(defn- layer-spec! [{:keys [id member opacity member-opacity transforms]
                      :or {opacity 1 member-opacity 1 transforms []} :as spec}]
  (when-not (and (some? id) (nat-int? member) (unit? opacity) (unit? member-opacity)
                 (or (nil? (:targets spec)) (= :previous (:targets spec))))
    (fail! "Native layer needs an identity, a nonnegative member index and unit opacities" {:layer spec}))
  (validate-transforms! transforms)
  spec)

(defn- transform-fields [id prior incoming base transforms validate!]
  (reduce
   (fn [fields {:keys [attribute value]}]
     (let [v (typed attribute (evaluate value {:previous prior :incoming incoming :field fields}))]
       (if (= attribute :beat-ratio)
         (when-not (finite? v) (fail! "Expected a finite beat ratio" {:value v}))
         (validate! {:target-id id :attribute attribute :value (rgb v)}))
       (assoc fields attribute v)))
   base transforms))

(defn- apply-member [state blocks rows blend-value validate!]
  (let [{:keys [source native-layer]} (first blocks)
        {:keys [transforms member-opacity targets] :or {member-opacity 1}} native-layer]
    (try
      (when-not (every? #(= native-layer (:native-layer %)) blocks)
        (fail! "A layer member's contribution blocks must agree on its descriptor" {:layer native-layer}))
      (if (zero? member-opacity)
        state
        (let [inherited (when (= targets :previous) (zipmap (keys (:sources state)) (repeat [])))
              inputs (reduce (fn [acc block]
                               (reduce (fn [m a] (update m (:target-id a) (fnil conj []) a))
                                       acc (rows block nil)))
                             (or inherited {}) blocks)
              apply-row (partial set-assignment blend-value validate!)]
          (reduce-kv
           (fn [st id assignments]
             (let [prior (get-in st [:fields id] {})
                   incoming (reduce apply-row {} assignments)
                   base (reduce apply-row prior assignments)
                   post (transform-fields id prior incoming base transforms validate!)
                   written (into (set (keys incoming)) (map :attribute) transforms)]
               (reduce (fn [acc field]
                         (-> acc
                             (assoc-in [:fields id field]
                                       (over blend-value field (get prior field) (get post field) :replace member-opacity))
                             (assoc-in [:sources id field] source))) st written)))
           state inputs)))
      (catch Exception ex (throw (faults/attributed-error ex source))))))

(defn- group-blocks [backdrop members rows blend-value validate!]
  (let [ordered (sort-by #(get-in % [:native-layer :member]) members)
        opacity (get-in (first ordered) [:native-layer :opacity] 1)
        _ (doseq [block ordered]
            (when-not (= opacity (get-in block [:native-layer :opacity] 1))
              (throw (faults/attributed-error (ex-info "Layer opacity must agree across members" {})
                                               (:source block)))))
        members (partition-by (juxt #(get-in % [:native-layer :member]) :source) ordered)]
    (if (zero? opacity)
      []
      (let [{:keys [fields sources]}
            (reduce #(apply-member %1 %2 rows blend-value validate!) {:fields backdrop :sources {}} members)
            writes (for [[id attrs] (sort-by (comp pr-str key) sources)
                         [field source] (sort-by key attrs)
                         :when (not= :beat-ratio field)]
                     [source {:target-id id :attribute field :value (rgb (get-in fields [id field]))
                              :opacity opacity}])]
        (mapv (fn [run] {:kind :assignments :source (ffirst run) :assignments (mapv second run)})
              (partition-by first writes))))))

(defn- update-backdrop [fields block targets rows apply-row]
  (try
    (reduce (fn [m a] (update m (:target-id a) apply-row a)) fields (rows block targets))
    (catch Exception ex (throw (faults/attributed-error ex (:source block))))))

(defn compose
  "Compose tagged blocks at the last member's position in the ordinary priority
  stream. Only affected target rows are read into the native backdrop. Each
  target/field result retains the source of its final contributing member."
  [blocks rows blend-value validate!]
  (if-not (some :native-layer blocks)
    blocks
    (let [tagged (filterv :native-layer blocks)
          groups (group-by #(get-in % [:native-layer :id]) tagged)
          anchors (reduce-kv (fn [m i b]
                               (if-let [l (:native-layer b)]
                                 (do (try (layer-spec! l)
                                          (catch Exception ex (throw (faults/attributed-error ex (:source b)))))
                                     (assoc m (:id l) i)) m)) {} blocks)
          last-anchor (apply max (vals anchors))
          apply-row (partial set-assignment blend-value validate!)
          targets (into #{} (mapcat (fn [{:keys [kind assignments compiled]}]
                                      (if (= kind :batch) (:target-ids compiled) (map :target-id assignments)))) tagged)]
      (:out
       (reduce-kv
        (fn [{:keys [backdrop] :as state} i block]
          (let [layer (:native-layer block)
                entries (cond (nil? layer) [block]
                              (= i (get anchors (:id layer)))
                              (group-blocks backdrop (get groups (:id layer)) rows blend-value validate!)
                              :else [])]
            (cond-> (update state :out into entries)
              (< i last-anchor)
              (assoc :backdrop (reduce #(update-backdrop %1 %2 targets rows apply-row) backdrop entries)))))
        {:backdrop {} :out []} blocks)))))
