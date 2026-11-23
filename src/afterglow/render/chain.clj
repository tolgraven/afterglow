(ns afterglow.render.chain
  "Lower adjacent pure field requests onto one native-space IR batch. The ordinary
  attribution and validation path remains available for every rejected chain."
  (:require [afterglow.render.ir :as ir])
  (:import [java.util Arrays]))

(defn create-cache
  "Bounded, per-show cache of compiled chain shapes. Values and clocks are frame-local."
  [] (atom {}))

(def ^:private max-members 8)
(def ^:private eligible-attributes #{:color :dimmer :focus :zoom :pan :tilt :aim :direction :red :green :blue :white})
(def ^:private spatial-ops #{:position :surface-uv})
(def ^:private capture-ops #{:param :time :beat :bar :phrase})

(defn- unit? [n] (and (number? n) (<= 0 n 1)))
(defn- only? [allowed item] (every? allowed (keys item)))
(defn- request [block] (get-in block [:batch :field-request]))
(defn- group [block] (:group (request block)))
(defn- expressions [group] (or (:expressions group) (get-in group [:shader :outputs])))

(defn- candidate? [{:keys [kind batch] :as block}]
  (let [{:keys [group env scales]} (:field-request batch)
        outputs (expressions group)]
    (and (= :batch kind) (only? #{:kind :batch :source} block)
         (only? #{:target-ids :blend :opacity :field-request} batch)
         (only? #{:group :env :scales :hdr?} (:field-request batch))
         (vector? (:target-ids batch)) (seq (:target-ids batch))
         (map? env) (map? outputs) (seq outputs) (every? eligible-attributes (keys outputs))
         (or (nil? scales) (and (map? scales) (every? outputs (keys scales)) (every? unit? (vals scales))))
         (#{:replace :max :add} (:blend batch :replace))
         (unit? (:opacity batch 1)) (pos? (:opacity batch 1)))))

(defn- same-coordinates? [a b]
  (or (identical? a b)
      (if (and (instance? double/1 a) (instance? double/1 b))
        (Arrays/equals ^doubles a ^doubles b)
        (= a b))))

(defn- same-layout? [a b]
  (and (same-coordinates? (:positions a) (:positions b))
       (same-coordinates? (:surface-uvs a) (:surface-uvs b))))

(defn- shape [block]
  (let [{:keys [batch]} block]
    [(group block) (:blend batch :replace) (== 1 (:opacity batch 1))
     (set (keys (:scales (request block))))]))

(defn- param [key] {:op :param :key key})
(defn- op [operation & args] {:op operation :args (vec args)})

(defn- lower-field
  "Use a separate namespace for each effect's captured clocks and parameters."
  [node index captures]
  (cond
    (capture-ops (:op node))
    (let [slot (or (get-in @captures [node :key]) (keyword (str "chain_" index) (str "u" (count @captures))))]
      (vswap! captures #(if (contains? % node) % (assoc % node {:key slot :read (ir/compile-expression node)})))
      (assoc (param slot) :type (ir/expression-type node)))

    (:args node) (update node :args #(mapv (fn [arg] (lower-field arg index captures)) %))
    :else node))

(defn- stage [index [group blend full? scales]]
  (let [captures (volatile! {})
        outputs (into {} (map (fn [[attribute expression]] [attribute (lower-field expression index captures)]))
                      (sort-by (comp str key) (expressions group)))
        scale-keys (into {} (map-indexed (fn [i attr] [attr (keyword (str "chain_" index) (str "s" i))])
                                          (sort-by str scales)))
        fields (reduce-kv (fn [result attr key] (update result attr #(op :multiply % (param key)))) outputs scale-keys)]
    {:fields fields :captures (vec (vals @captures)) :scales scale-keys :blend blend
     :alpha (when-not full? (keyword (str "chain_" index) "alpha"))}))

(defn- fold-field [previous incoming blend alpha]
  (if (and (= blend :replace) (nil? alpha))
    incoming
    (when previous
      (let [value (case blend :replace incoming :add (op :add previous incoming) :max (op :max previous incoming))]
        (if alpha (op :add previous (op :multiply (param alpha) (op :subtract value previous))) value)))))

(defn- fold-stage [previous {:keys [fields blend alpha]}]
  (reduce-kv (fn [acc attr field]
               (if-let [value (fold-field (get acc attr) field blend alpha)]
                 (assoc acc attr value) (reduced nil)))
             previous fields))

(defn- range-of [value]
  (let [xs (if (vector? value) value [value])]
    (when (and (seq xs) (every? #(and (number? %) (Double/isFinite (double %)) (<= (abs (double %)) Float/MAX_VALUE)) xs))
      [(double (reduce min xs)) (double (reduce max xs))])))

(defn- endpoints [f [al ah] [bl bh]]
  (range-of [(f al bl) (f ah bl) (f al bh) (f ah bh)]))

(defn- hull [ranges] [(reduce min (map first ranges)) (reduce max (map second ranges))])

(defn- operation-range [operation ranges]
  (let [[[al ah] [bl bh] [cl ch]] ranges]
    (case operation
      (:vec2 :vec3 :vec4) (hull ranges)
      (:sin :cos) [-1.0 1.0]
      :fract [0.0 1.0]
      :floor [(Math/floor al) (Math/floor ah)]
      :abs [(if (<= al 0 ah) 0.0 (min (abs al) (abs ah))) (max (abs al) (abs ah))]
      :sqrt (when (>= al 0) [(Math/sqrt al) (Math/sqrt ah)])
      :exp (range-of [(Math/exp al) (Math/exp ah)])
      :min [(reduce min (map first ranges)) (reduce min (map second ranges))]
      :max [(reduce max (map first ranges)) (reduce max (map second ranges))]
      :clamp (when (<= bh cl) [(min cl (max bl al)) (min ch (max bh ah))])
      :mix (when (<= 0 cl ch 1) (hull (take 2 ranges)))
      :subtract (if bl (endpoints - (first ranges) (second ranges)) [(- ah) (- al)])
      :divide (when-not (<= bl 0 bh) (endpoints / (first ranges) (second ranges)))
      (:add :multiply) (reduce (fn [a b] (or (endpoints (if (= operation :add) + *) a b) (reduced nil))) ranges)
      nil)))

(defn- coordinate [values width row axis]
  (if (instance? double/1 values) (aget ^doubles values (+ (* width row) axis))
    (get-in values [row axis])))

(defn- coordinate-ranges [{:keys [positions surface-uvs]} fields]
  (let [axes (into #{} (comp (mapcat #(tree-seq :args :args %))
                             (filter #(spatial-ops (:op %))) (map #(select-keys % [:op :axis]))) fields)
        n (if (instance? double/1 positions) (quot (alength ^doubles positions) 3) (count positions))]
    (into {}
          (for [{:keys [op axis] :as node} axes
                :let [column ({:x 0 :y 1 :z 2 :u 0 :v 1} axis)
                      uv? (= op :surface-uv)
                      at (fn [row] (or (when uv? (coordinate surface-uvs 2 row column))
                                       (coordinate positions 3 row column)))
                      extremes (reduce (fn [[lo hi] row]
                                         (let [v (at row)] [(min lo v) (max hi v)]))
                                       [Double/POSITIVE_INFINITY Double/NEGATIVE_INFINITY] (range n))]]
            [node (range-of extremes)]))))

(defn- interval [{:keys [op key value args axis]} env]
  (cond
    (= op :param) (range-of (get env key))
    (= op :const) (range-of value)
    (spatial-ops op) (get-in env [::positions {:op op :axis axis}])
    :else (let [children (mapv #(interval % env) args)]
            (when (every? some? children) (operation-range op children)))))

(defn- valid-output? [attribute interval]
  (and interval (or (#{:aim :direction} attribute) (<= 0 (first interval) (second interval) 1))))

(defn- safe-stage
  "Retain the intermediate validation that frame/resolve-contributions applies
  before the next blend. Unknown or possibly invalid bounds stay on its original path."
  [previous {:keys [fields blend alpha]} env]
  (reduce-kv
   (fn [ranges attr field]
     (let [incoming (interval field env)
           prior (get ranges attr)]
       (if-not (valid-output? attr incoming) (reduced nil)
         (let [blended (case blend
                         :replace incoming
                         :add (when prior (endpoints + prior incoming))
                         :max (when prior (operation-range :max [prior incoming])))
               amount (if alpha (get env alpha) 1)
               final (cond (nil? blended) nil
                           (== 1 amount) blended
                           prior (range-of [(+ (* (- 1.0 amount) (first prior)) (* amount (first blended)))
                                            (+ (* (- 1.0 amount) (second prior)) (* amount (second blended)))]))]
           (if (valid-output? attr final) (assoc ranges attr final) (reduced nil))))))
   previous fields))

(defn- captured [stages blocks]
  (reduce (fn [params [stage block]]
            (let [{:keys [env scales]} (request block)
                  values (reduce (fn [m {:keys [key read]}] (assoc m key (read env))) params (:captures stage))
                  values (reduce-kv (fn [m attr key] (assoc m key (get scales attr))) values (:scales stage))]
              (cond-> values (:alpha stage) (assoc (:alpha stage) (get-in block [:batch :opacity] 1)))))
          {} (map vector stages blocks)))

(defn- prepare [prepare-group shapes]
  (let [groups (mapv first shapes) first-group (first groups)]
    (when (every? #(same-layout? first-group %) (rest groups))
      (let [stages (mapv stage (range) shapes)
            outputs (reduce (fn [acc stage] (or (fold-stage acc stage) (reduced nil))) {} stages)]
        (when outputs
          {:stages stages
           :coordinate-ranges (coordinate-ranges first-group (mapcat (comp vals :fields) stages))
           :prepared (prepare-group outputs (:positions first-group) (ir/compile-batch outputs) (:surface-uvs first-group))})))))

(defn- cached-plan [cache prepare-group shapes]
  (let [entries @cache]
    (if (contains? entries shapes) (get entries shapes)
      (let [plan (prepare prepare-group shapes)]
        (swap! cache #(assoc (if (< (count %) 32) % {}) shapes plan))
        plan))))

(defn- fuse-run [cache prepare-group blocks]
  (when (< 1 (count blocks))
    (try
      (when-let [{:keys [stages prepared coordinate-ranges]} (cached-plan cache prepare-group (mapv shape blocks))]
        (let [params (captured stages blocks)
              bounds-env (assoc params ::positions coordinate-ranges)
              safe? (reduce #(or (safe-stage %1 %2 bounds-env) (reduced nil)) {} stages)]
          (when safe?
            {:kind :batch :source (:source (peek blocks))
             :batch {:target-ids (get-in (first blocks) [:batch :target-ids]) :blend :replace
                     :field-request {:group prepared :env {:params params}}}})))
      ;; Missing parameters, unsupported ranges and compiler limits use the original
      ;; requests so the show can attribute any failure to the right running effect.
      (catch RuntimeException _ nil))))

(defn fuse
  "Replace adjacent compatible requests over identical ordered target IDs with
  one prepared field request. Native layers, annotation-bearing blocks and
  selections that differ are barriers. Each field starts with an opaque replace.
  The caller can retry its original blocks to attribute downstream frame errors."
  [cache prepare-group blocks]
  (let [ordered (if (vector? blocks) blocks (vec blocks))]
    (loop [start 0 consumed 0 result nil]
      (if (= start (count ordered))
        (if result (into result (subvec ordered consumed)) ordered)
        (let [block (nth ordered start)]
          (if-not (candidate? block)
            (recur (inc start) consumed result)
            (let [ids (get-in block [:batch :target-ids])
                  end (loop [i (inc start)]
                        (if (and (< i (count ordered)) (< (- i start) max-members)
                                 (candidate? (nth ordered i)) (= ids (get-in ordered [i :batch :target-ids])))
                          (recur (inc i)) i))
                  run (subvec ordered start end)]
              (if-let [fused (fuse-run cache prepare-group run)]
                (recur end end (conj (into (or result []) (subvec ordered consumed start)) fused))
                (recur (inc start) consumed result)))))))))
