(ns afterglow.runtime.keyframes.values
  "Interpolate uncomposited effect outputs. Arrays are read-only endpoints.
  Each interpolated numeric column has its own storage."
  (:require [afterglow.render.photometry :as photometry]
            [afterglow.runtime :as runtime]
            [afterglow.time :as time]))

(def emitters (into #{:dimmer :color} (keys photometry/emitter-spectrum)))
(def geometry #{:aim :direction})
(def continuous (into (into emitters geometry) [:pan :tilt :zoom :focus :beat-ratio]))

(defn- invalid! [reason] (throw (ex-info reason {:type ::invalid-sampler})))

(defn blocks [context result]
  (when-not (and (= (:state context) (:state result)) (= [] (:intents result))
                 (false? (:done? result)) (vector? (:assignments result)))
    (invalid! "A predictive sampler must only produce continuous native outputs"))
  (let [blocks (:contributions (runtime/append-contributions result []))]
    (doseq [{:keys [kind assignments batch]} blocks]
      (case kind
        :assignments (when-not (every? (comp continuous :attribute) assignments)
                       (invalid! "Discrete effects must run on the live clock"))
        :batch (when-not (and (nil? (:field-request batch)) (seq (:outputs batch))
                              (every? continuous (keys (:outputs batch))))
                 (invalid! "Predictive batches need evaluated continuous fields"))))
    blocks))

(defn- bounds [attr hdr?]
  (cond
    (or (geometry attr) (= :beat-ratio attr)) [Double/NEGATIVE_INFINITY Double/POSITIVE_INFINITY]
    (and hdr? (emitters attr)) [0.0 Double/POSITIVE_INFINITY]
    :else [0.0 1.0]))

(defn- scalar [a b t lo hi]
  (let [v (+ (double a) (* (double t) (- (double b) (double a))))]
    (max lo (min hi v))))

(defn- assignment [t hdr? a b]
  (when-not (= (dissoc a :value) (dissoc b :value))
    (invalid! "Predictive assignment topology changed within a keyframe"))
  (let [[lo hi] (bounds (:attribute a) hdr?) a-value (:value a) b-value (:value b)
        sample #(scalar %1 %2 t lo hi)]
    (assoc a :value (if (and (vector? a-value) (vector? b-value) (= (count a-value) (count b-value)))
                      (mapv sample a-value b-value)
                      (sample a-value b-value)))))

(defn- column [attr t hdr? from to]
  (when-not (= (dissoc from :values) (dissoc to :values))
    (invalid! "Predictive column shape changed within a keyframe"))
  (let [^doubles a (:values from) ^doubles b (:values to) n (alength a)
        t (double t) [lo hi] (bounds attr hdr?) lo (double lo) hi (double hi)
        out (double-array n)]
    (when-not (= n (alength b)) (invalid! "Predictive field size changed"))
    (dotimes [i n]
      (let [x (aget a i)]
        (aset-double out i (max lo (min hi (+ x (* t (- (aget b i) x))))))))
    (assoc from :values out)))

(defn- blend-block [t hdr? a b]
  (when-not (= (:kind a) (:kind b))
    (invalid! "Predictive output representation changed within a keyframe"))
  (case (:kind a)
    :assignments
    (let [as (:assignments a) bs (:assignments b)]
      (when-not (= (count as) (count bs)) (invalid! "Predictive assignment count changed"))
      (assoc a :assignments (mapv (partial assignment t hdr?) as bs)))
    :batch
    (let [left (:batch a) right (:batch b)
          as (:outputs left) bs (:outputs right)]
      (when-not (and (= (dissoc left :outputs) (dissoc right :outputs)) (= (set (keys as)) (set (keys bs))))
        (invalid! "Predictive batch topology changed within a keyframe"))
      (assoc-in a [:batch :outputs] (reduce-kv (fn [m attr field] (assoc m attr (column attr t hdr? field (bs attr)))) {} as)))))

(defn blend [origin target t hdr?]
  (cond
    (zero? t) origin
    (== 1.0 t) target
    :else (do (when-not (= (count origin) (count target)) (invalid! "Predictive block count changed"))
              (mapv (partial blend-block t hdr?) origin target))))

(defn map-columns [f blocks]
  (mapv (fn [block]
          (if (= :batch (:kind block))
            (update-in block [:batch :outputs] update-vals #(update % :values f))
            block)) blocks))

(defn- batch-rows [{:keys [target-ids blend outputs opacity]}]
  (for [[i id] (map-indexed vector target-ids)
        [attr {:keys [components values]}] outputs]
    (let [^doubles xs values start (* i components)]
      (cond-> {:target-id id :attribute attr :blend (or blend :replace)
               :value (if (= 1 components) (aget xs start)
                         (mapv #(aget xs (+ start %)) (range components)))}
        (some? opacity) (assoc :opacity opacity)))))

(defn- rows [blocks]
  (into [] (mapcat (fn [block] (if (= :batch (:kind block))
                                 (batch-rows (:batch block)) (:assignments block)))) blocks))

(defn- align [order other]
  ;; Different IR paths can group the same assignments differently. Preserve
  ;; the origin's order and the order of successive writes to one attribute.
  (let [key-of (juxt :target-id :attribute)
        index (group-by key-of other)]
    (loop [remaining order index index result (transient [])]
      (if-let [row (first remaining)]
        (let [k (key-of row) available (get index k)]
          (when-not (seq available) (invalid! "Predictive effect changed its targets"))
          (recur (next remaining) (assoc index k (next available)) (conj! result (first available))))
        (do (when (some seq (vals index)) (invalid! "Predictive effect added targets"))
            (persistent! result))))))

(defn endpoints [origin target]
  (if (= (mapv :kind origin) (mapv :kind target)) [origin target]
    (let [start (rows origin)
          end (align start (rows target))]
      [[{:kind :assignments :assignments start}] [{:kind :assignments :assignments end}]])))

(defn read-values [blocks target attribute]
  (let [relevant? (fn [row] (and (= target (:target-id row)) (= attribute (:attribute row))))
        values-of (fn [{:keys [kind batch assignments]}]
                    (if (= :assignments kind)
                      (into [] (comp (filter relevant?) (map :value)) assignments)
                      (let [{:keys [target-ids outputs]} batch
                            {:keys [components values]} (get outputs attribute)
                            i (if values (.indexOf ^java.util.List target-ids target) -1)]
                        (when-not (neg? i)
                          (let [^doubles xs values start (* i components)]
                            [(if (= components 1) (aget xs start)
                               (mapv #(aget xs (+ start %)) (range components)))])))))]
    (into [] (mapcat values-of) blocks)))
