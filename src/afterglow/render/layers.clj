(ns afterglow.render.layers
  "Pure composition of native fixture fields. The frame renderer supplies validated
  assignment/batch rows and performs geometry and channel packing after composition."
  (:require [afterglow.runtime.faults :as faults]
            [afterglow.render.hdr :as hdr]
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
(defn- typed [high? attribute value]
  (if (= attribute :color)
    (let [v (rgb value)]
      (when-not (and (xyz? v) (if high? (not-any? neg? v) (every? unit? v)))
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

(defn- arithmetic [high? op a b]
  (let [f (case op :add + :multiply * :divide /)
        x (rgb a) y (rgb b)
        result (cond
                 (and (finite? x) (finite? y)) (f x y)
                 (and (xyz? x) (xyz? y)) (mapv f x y)
                 (and (xyz? x) (finite? y)) (mapv #(f % y) x)
                 (and (finite? x) (xyz? y)) (mapv #(f x %) y)
                 :else (fail! "Expected scalar, color or vector operands" {:op op}))]
    (if (or (color? a) (color? b)) (typed high? :color result) result)))

(defn- evaluate [high? expr env]
  (if (or (not (map? expr)) (color? expr))
    expr
    (let [{:keys [op attribute args]} expr]
      (if (reads op)
        (if-some [x (get-in env [op attribute])]
          x
          (if (contains? expr :default) (evaluate high? (:default expr) env)
              (fail! "Native layer field has no value for this target" {:op op :attribute attribute})))
        (let [[a b] (mapv #(evaluate high? % env) args)]
          (case op
            (:add :multiply :divide) (arithmetic high? op a b)
            :rotate-y (do (when-not (and (xyz? a) (finite? b)) (fail! "rotate-y needs a vector and radians" {}))
                          (let [[x y z] a c (Math/cos b) s (Math/sin b)]
                            [(+ (* x c) (* z s)) y (- (* z c) (* x s))]))
            :rotate-hue (do (when-not (finite? b) (fail! "rotate-hue needs a color and turns" {}))
                            (color/rotate-hue (typed high? :color a) (* 2.0 Math/PI b)))))))))

(defn- over [high? blend-value field before value blend opacity]
  (typed high? field (blend-value (rgb before) (rgb value) blend opacity)))

(defn- set-assignment [high? blend-value validate! fields {:keys [attribute value blend opacity] :as a}]
  (let [value (typed high? attribute value)
        opacity (get a :opacity 1)
        blend (get a :blend :replace)]
    (if (= :beat-ratio attribute)
      (when-not (and (finite? value) (unit? opacity) (#{:replace :max :add} blend))
        (fail! "Invalid beat-ratio contribution" {:assignment a}))
      (validate! (assoc a :value (rgb value))))
    (if (zero? opacity)
      fields
      (let [result (over high? blend-value attribute (get fields attribute) value blend opacity)]
        (if (= :beat-ratio attribute)
          (when-not (finite? result) (fail! "Beat-ratio arithmetic overflow" {:assignment a}))
          (validate! (assoc a :value (rgb result))))
        (assoc fields attribute result)))))

(defn- layer-spec! [{:keys [id member opacity member-opacity transforms]
                      :or {opacity 1 member-opacity 1 transforms []} :as spec}]
  (when-not (and (some? id) (nat-int? member) (unit? opacity) (unit? member-opacity)
                 (or (nil? (:targets spec)) (= :previous (:targets spec)))
                 (or (nil? (:target-ids spec)) (vector? (:target-ids spec))))
    (fail! "Native layer needs an identity, a nonnegative member index and unit opacities" {:layer spec}))
  (validate-transforms! transforms)
  spec)

(defn- transform-fields [high? id prior incoming base transforms validate!]
  (reduce
   (fn [fields {:keys [attribute value]}]
     (let [v (typed high? attribute (evaluate high? value {:previous prior :incoming incoming :field fields}))]
       (if (= attribute :beat-ratio)
         (when-not (finite? v) (fail! "Expected a finite beat ratio" {:value v}))
         (validate! {:target-id id :attribute attribute :value (rgb v)}))
       (assoc fields attribute v)))
   base transforms))

(defn- check-member! [blocks]
  (let [{:keys [source native-layer]} (first blocks)]
    (when-not (every? #(= native-layer (:native-layer %)) (next blocks))
      (throw (faults/attributed-error
              (ex-info "A layer member's contribution blocks must agree on its descriptor" {:layer native-layer})
              source)))))

(defn- apply-member [high? state blocks rows blend-value validate! allowed]
  (let [{:keys [source native-layer] :as first-block} (first blocks)
        {:keys [transforms member-opacity targets] :or {member-opacity 1}} native-layer]
    (try
      (check-member! blocks)
      (if (zero? member-opacity)
        state
        (let [inherited (when (= targets :previous)
                          (keys (if (:inherit-backdrop? native-layer) (:fields state) (:sources state))))
              target-ids (concat (:target-ids native-layer) inherited)
              initial (zipmap (if allowed (filter #(contains? allowed %) target-ids) target-ids)
                              (repeat []))
              inputs (reduce (fn [acc block]
                               (reduce (fn [m a] (update m (:target-id a) (fnil conj []) a))
                                       acc (rows block allowed)))
                             initial blocks)
              apply-row (partial set-assignment high? blend-value validate!)]
          (reduce-kv
           (fn [st id assignments]
             (let [prior (get-in st [:fields id] {})
                   incoming (reduce apply-row {} assignments)
                   base (reduce apply-row prior assignments)
                   post (transform-fields high? id prior incoming base transforms validate!)
                   written (into (set (keys incoming)) (map :attribute) transforms)
                   ;; A native transform can synthesize a value independent of
                   ;; its input. Apply member gain after the transform, once.
                   gain (::hdr/member-gain first-block)
                   post (if (and gain ((::hdr/gain-target? first-block) id))
                          (reduce (fn [m field]
                                    (if (and (hdr/light-attributes field)
                                             (or (= field :dimmer) (not (contains? written :dimmer))))
                                      (update m field #(arithmetic high? :multiply % gain)) m))
                                  post written)
                          post)]
               (reduce (fn [acc field]
                         (-> acc
                             (assoc-in [:fields id field]
                                       (over high? blend-value field (get prior field) (get post field) :replace member-opacity))
                             (assoc-in [:sources id field] source))) st written)))
           state inputs)))
      (catch Exception ex (throw (faults/attributed-error ex source))))))

(defn- ordered-members [blocks]
  (let [ordered (sort-by #(get-in % [:native-layer :member]) blocks)
        group (:native-layer (first ordered))
        opacity (:opacity group 1)]
    (doseq [block ordered]
      (when-not (and (= opacity (get-in block [:native-layer :opacity] 1))
                     (= (:target-weights group) (get-in block [:native-layer :target-weights])))
        (throw (faults/attributed-error (ex-info "Layer opacity and target weights must agree across members" {})
                                        (:source block)))))
    (partition-by (juxt #(get-in % [:native-layer :member]) :source) ordered)))

(defn- validate-weights! [weights source]
  (when (and (some? weights) (not (and (map? weights) (every? unit? (vals weights)))))
    (throw (faults/attributed-error (ex-info "Target weights must be a map of unit opacities" {}) source))))

(defn- group-blocks [high? backdrop blocks rows blend-value validate!]
  (let [members (ordered-members blocks)
        group (:native-layer (first blocks))
        opacity (:opacity group 1)
        weights (:target-weights group)
        allowed (when weights (into #{} (keep (fn [[id weight]] (when (pos? weight) id))) weights))]
    (if (or (zero? opacity) (and allowed (empty? allowed)))
      []
      (let [{:keys [fields sources]}
            (reduce #(apply-member high? %1 %2 rows blend-value validate! allowed) {:fields backdrop :sources {}} members)
            writes (for [[id attrs] (sort-by (comp pr-str key) sources)
                         [field source] (sort-by key attrs)
                         :when (not= :beat-ratio field)]
                     [source {:target-id id :attribute field :value (rgb (get-in fields [id field]))
                              :opacity (if weights (* opacity (weights id)) opacity)}])]
        (mapv (fn [run] {:kind :assignments :source (ffirst run) :assignments (mapv second run)})
              (partition-by first writes))))))

(defn- update-backdrop [fields block targets rows apply-row]
  (try
    (reduce (fn [m a] (update m (:target-id a) apply-row a)) fields (rows block targets))
    (catch Exception ex (throw (faults/attributed-error ex (:source block))))))

(defn- opaque? [x] (and (number? x) (== 1 x)))

(defn- physical-replacement? [{:keys [native-layer kind assignments compiled]}]
  (and (opaque? (:member-opacity native-layer 1))
       (empty? (:transforms native-layer))
       (case kind
         :batch (and (= :replace (:blend compiled))
                     (opaque? (:opacity compiled))
                     (not-any? #(= :beat-ratio (:attribute %)) (:columns compiled)))
         :assignments (every? (fn [{:keys [attribute value blend opacity]
                                   :or {blend :replace opacity 1}}]
                                (and (= :replace blend) (opaque? opacity)
                                     (not= :beat-ratio attribute)
                                     (or (not= :color attribute)
                                         (and (vector? value) (every? double? value)))))
                              assignments))))

(defn- unique-indices? [^ints indices]
  ;; A nil permutation is a unique prefix of patch order.
  (or (nil? indices)
      (let [seen (java.util.BitSet.)]
        (loop [row 0]
          (or (= row (alength indices))
              (let [idx (aget indices row)]
                (and (not (.get seen idx))
                     (do (.set seen idx) (recur (inc row))))))))))

(defn- masked-batch [block weights opacity]
  (let [{:keys [target-ids target-indices]} (:compiled block)]
    (when (unique-indices? target-indices)
      (let [opacities (double-array (count target-ids))
            opacity (double opacity)]
        (dotimes [row (alength opacities)]
          (aset opacities row (* opacity (double (get weights (nth target-ids row) 0)))))
        (assoc-in (dissoc block :native-layer) [:compiled ::opacities] opacities)))))

(defn- masked-assignments [block weights opacity]
  (loop [remaining (seq (:assignments block)), seen (transient #{}), output (transient [])]
    (if-let [{:keys [target-id attribute] :as row} (first remaining)]
      (let [weight (get weights target-id 0)]
        (if (zero? weight)
          (recur (next remaining) seen output)
          (let [k [target-id attribute]]
            (when-not (contains? seen k)
              (recur (next remaining) (conj! seen k)
                     (conj! output (assoc row :opacity (* opacity weight))))))))
      (assoc (dissoc block :native-layer) :assignments (persistent! output)))))

(defn- independent-columns? [blocks]
  ;; Intersecting writers must compose the entire scene before applying alpha.
  (loop [remaining (seq blocks), seen #{}]
    (if-let [{:keys [kind assignments compiled]} (first remaining)]
      (let [columns (into #{} (map :attribute) (if (= :batch kind) (:columns compiled) assignments))]
        (and (not-any? seen columns)
             (recur (next remaining) (into seen columns))))
      true)))

(defn- packed-factor? [x]
  (or (double? x) (float? x) (integer? x)))

(defn- direct-group [blocks]
  (let [members (ordered-members blocks)
        ordered (vec (mapcat (fn [member] (check-member! member) member) members))
        {:keys [target-weights opacity] :or {opacity 1}} (:native-layer (first ordered))]
    (when (every? physical-replacement? ordered)
      (cond
        (nil? target-weights)
        (when (opaque? opacity) (mapv #(dissoc % :native-layer) ordered))

        (or (zero? opacity) (empty? target-weights)) []

        (and (packed-factor? opacity) (every? packed-factor? (vals target-weights))
             (or (= 1 (count ordered)) (independent-columns? ordered)))
        (let [masked (mapv (fn [block]
                             ((if (= :batch (:kind block)) masked-batch masked-assignments)
                              block target-weights opacity))
                           ordered)]
          (when (every? some? masked) masked))))))

(defn- order-direct-blocks [blocks planned anchors]
  (reduce-kv
   (fn [result index {:keys [native-layer] :as block}]
     (cond
       (nil? native-layer) (conj result block)
       (= index (get anchors (:id native-layer))) (into result (planned (:id native-layer)))
       :else result))
   [] blocks))

(defn compose
  "Compose tagged blocks at the last member's position in the ordinary priority
  stream. Only affected target rows are read into the native backdrop. Each
  target/field result retains the source of its final contributing member.
  Optional :target-weights maps head IDs to [0,1]. Omitted heads receive no
  group output. Multiply the final group opacity by this weight once, after
  composing all native transforms and their inputs."
  ([blocks rows blend-value validate!] (compose blocks rows blend-value validate! false))
  ([blocks rows blend-value validate! high?]
  (if-not (some :native-layer blocks)
    blocks
    (let [tagged (filterv :native-layer blocks)
          groups (group-by #(get-in % [:native-layer :id]) tagged)
          anchors (reduce-kv (fn [m i b]
                               (if-let [l (:native-layer b)]
                                 (do (try (layer-spec! l)
                                          (catch Exception ex (throw (faults/attributed-error ex (:source b)))))
                                     (assoc m (:id l) i)) m)) {} blocks)]
      (doseq [[_ group] groups]
        (validate-weights! (get-in (first group) [:native-layer :target-weights]) (:source (first group))))
      (let [planned (update-vals groups direct-group)]
        (if (every? some? (vals planned))
        (order-direct-blocks blocks planned anchors)
        (let [last-anchor (apply max (vals anchors))
              apply-row (partial set-assignment high? blend-value validate!)
              targets (when-not (some #(get-in % [:native-layer :inherit-backdrop?]) tagged)
                        (into #{} (mapcat (fn [{:keys [kind assignments compiled native-layer]}]
                                            (concat (:target-ids native-layer)
                                                    (if (= kind :batch) (:target-ids compiled)
                                                        (map :target-id assignments))))) tagged))]
          (:out
           (reduce-kv
            (fn [{:keys [backdrop] :as state} i block]
              (let [layer (:native-layer block)
                    entries (cond (nil? layer) [block]
                                  (= i (get anchors (:id layer)))
                                  (group-blocks high? backdrop (get groups (:id layer)) rows blend-value validate!)
                                  :else [])]
                (cond-> (update state :out into entries)
                  (< i last-anchor)
                  (assoc :backdrop (reduce #(update-backdrop %1 %2 targets rows apply-row) backdrop entries)))))
            {:backdrop {} :out []} blocks)))))))))
