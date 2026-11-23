(ns afterglow.control.resolution
  "Infer physical channel precision from an immutable fixture patch and authored
  output expressions. A binding with no physical destination stays continuous."
  (:require [afterglow.render.photometry :as photometry]
            [clojure.set :as set]))

(defn- id-key [x] (if (string? x) (keyword x) x))
(defn- field [m k] (get m k (get m (name k))))

(defn- width [spec]
  (cond
    (and (integer? spec) (pos? spec)) 8
    (and (vector? spec) (= 2 (count spec)) (every? #(and (integer? %) (pos? %)) spec)) 16
    (map? spec) (cond (or (field spec :fine-offset) (field spec :fine)) 16
                      (or (field spec :offset) (field spec :coarse)) 8)))

(defn- largest [bits] (when (seq bits) (reduce max bits)))

(defn- fixture-widths [fixture]
  (let [channels (or (field fixture :channels) (field fixture :compiled-channels))
        direct (into {} (keep (fn [[attr spec]] (when-let [n (width spec)] [(id-key attr) n]))) channels)
        rgb? (every? direct [:red :green :blue])
        color-channels (cond-> [:red :green :blue] (= :extract-min (id-key (field fixture :rgbw-policy))) (conj :white))
        movement (when (every? direct [:pan :tilt]) (max (:pan direct) (:tilt direct)))
        intensity (or (:dimmer direct) (largest (keep direct (keys photometry/emitter-spectrum))))]
    (cond-> direct
      intensity (assoc :dimmer intensity)
      rgb? (assoc :color (largest (keep direct color-channels)))
      movement (assoc :aim movement :direction movement))))

(defrecord PatchWidths [all by-id])

(defn patch-widths
  "Build once per rig revision. Passing the result to parameter-bits avoids
  revisiting every LED head for each encoder or Studio widget."
  [fixtures]
  (let [by-id (into {} (map (fn [fixture] [(id-key (field fixture :id)) (fixture-widths fixture)])) fixtures)]
    (->PatchWidths (reduce (partial merge-with max) {} (vals by-id)) by-id)))

(defn- output-entries [definition]
  (let [outputs (field definition :outputs)]
    (concat (if (map? outputs) (map (fn [[attr expr]] {:attribute attr :value expr}) outputs) outputs)
            (field (field definition :layer) :transforms))))

(defn- references? [bindings param expression visited]
  (boolean
   (some (fn [node]
           (when (map? node)
             (let [op (id-key (field node :op)) k (id-key (field node :key))
                   ref (case op :param [:params k] :varying [:varyings k]
                             :variable (into [:variables] (map id-key) (or (field node :path) [k])) nil)]
               (or (and (= :param op) (= param k))
                   (when (and ref (not (contains? visited ref)))
                     (when-let [binding (get bindings ref)]
                       (references? bindings param binding (conj visited ref))))))))
         (tree-seq coll? seq expression))))

(defn- targets [x] (when (coll? x) (into #{} (map id-key) x)))
(defn- intersection [a b] (cond (nil? a) b (nil? b) a :else (set/intersection a b)))

(defn parameter-bits
  "Return the finest patched channel width reached by this parameter, or nil.
  Output, definition and optional instance target IDs intersect. Accepts a
  fixture collection or patch-widths result, and string or keyword wire IDs."
  ([fixtures definition parameter] (parameter-bits fixtures definition parameter nil))
  ([fixtures definition parameter instance-targets]
   (let [patch (if (instance? PatchWidths fixtures) fixtures (patch-widths fixtures))
         param (id-key parameter)
         bindings (field definition :blocks)
         selected (intersection (targets (field definition :targets)) (targets instance-targets))]
     (largest
      (keep (fn [output]
              (let [attr (id-key (field output :attribute)) ref [:outputs attr]]
                (when (or (references? bindings param (field output :value) #{})
                          (when-let [binding (get bindings ref)] (references? bindings param binding #{ref})))
                  (if-some [ids (intersection selected (targets (field output :targets)))]
                    (largest (keep #(get-in (:by-id patch) [% attr]) ids))
                    (get (:all patch) attr)))))
            (output-entries definition))))))

(defn fine-step
  "Relative increment for a physical continuous control. Bounds within [0,1]
  constrain a normalized output without stretching its encoded channel span.
  Other control units use their declared range, e.g. cycles or degrees."
  [bits [low high]]
  (when (and (#{8 16} bits) (number? low) (number? high) (< low high))
    (/ (if (<= 0 low high 1) 1.0 (double (- high low))) (if (= bits 16) 65535.0 255.0))))
