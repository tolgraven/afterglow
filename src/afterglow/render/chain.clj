(ns afterglow.render.chain
  "Lower pure field requests onto native-space IR batches. Keep original requests
  available for validation and attribution when a plan cannot prove coverage."
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.ir :as ir])
  (:import [java.util Arrays]))

(defn create-cache
  "Bounded, per-show cache of compiled chain shapes. Values and clocks are frame-local."
  [] (atom {}))

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
         (or (= :replace (:blend batch :replace))
             (not-any? #{:aim :direction} (keys outputs)))
         (unit? (:opacity batch 1)) (pos? (:opacity batch 1)))))

(defn- same-coordinates? [a b]
  (or (identical? a b)
      (if (and (instance? double/1 a) (instance? double/1 b))
        (Arrays/equals ^doubles a ^doubles b)
        (= a b))))

(defn- shape [block]
  (let [{:keys [batch]} block]
    [(group block) (:blend batch :replace) (== 1 (:opacity batch 1))
     (set (keys (:scales (request block)))) (:target-ids batch)]))

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
      (case blend
        :replace (op :mix previous incoming (param alpha))
        :add (op :add previous (if alpha (op :multiply incoming (param alpha)) incoming))
        :max (if alpha
               (ir/partial-max-blend previous incoming (param alpha))
               (op :max previous incoming))))))

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

(defn- weighted-mix-range [prior incoming [lo hi]]
  (when (<= 0 lo hi 1)
    (let [dry (endpoints * prior [(- 1.0 hi) (- 1.0 lo)])
          wet (endpoints * incoming [lo hi])]
      (when (and dry wet) (endpoints + dry wet)))))

(defn- partial-mixed-range [blend [lo hi :as prior] [incoming-lo :as incoming]
                            [blended-lo blended-hi] amount]
  (let [frame-lo (+ lo (* amount (- blended-lo hi)))
        frame-hi (+ hi (* amount (- blended-hi lo)))
        ;; A nonnegative add cannot lower the prior, and a replacement
        ;; between nonnegative inputs cannot produce a negative result.
        frame-lo (case blend
                   :add (max lo frame-lo)
                   :replace (if (and (<= 0 lo) (<= 0 incoming-lo)) (max 0.0 frame-lo) frame-lo))
        amounts [amount amount]
        lowered (case blend
                  :replace (weighted-mix-range prior incoming amounts)
                  :add (when-let [wet (endpoints * incoming amounts)] (endpoints + prior wet)))]
    ;; The frame computes prior + alpha * (blended - prior). GLSL mix
    ;; and the simplified add round differently. Both must stay valid.
    (when lowered (range-of [(min frame-lo (first lowered)) (max frame-hi (second lowered))]))))

(defn- partial-max-range [[lo hi :as prior] [incoming-lo incoming-hi] [alpha-lo alpha-hi]]
  (when (<= 0 alpha-lo alpha-hi 1)
    (if (<= incoming-hi lo)
      prior
      ;; Rounded subtraction breaks monotonicity in the prior when it appears
      ;; in both the sum and the difference. Bound those operations separately.
      (let [delta-lo (max 0.0 (- incoming-lo hi))
            delta-hi (max 0.0 (- incoming-hi lo))
            upper (+ hi (* alpha-hi delta-hi))
            ;; With nonnegative inputs, subtraction can round up by at most
            ;; one ULP at the input ceiling. Scaling cannot increase the delta.
            upper (if (and (<= 0 lo) (<= 0 incoming-lo))
                    (min upper (Math/nextUp (double (max hi incoming-hi))))
                    upper)]
        (range-of [(+ lo (* alpha-lo delta-lo)) upper])))))

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
      :mix (apply weighted-mix-range ranges)
      ::ir/partial-max-blend (apply partial-max-range ranges)
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
                           (= :max blend) (partial-max-range prior incoming [amount amount])
                           prior (partial-mixed-range blend prior incoming blended amount))]
           (if (valid-output? attr final) (assoc ranges attr final) (reduced nil))))))
   previous fields))

(defn- captured [stages blocks]
  (reduce (fn [params [stage block]]
            (let [{:keys [env scales]} (request block)
                  values (reduce (fn [m {:keys [key read]}] (assoc m key (read env))) params (:captures stage))
                  values (reduce-kv (fn [m attr key] (assoc m key (get scales attr))) values (:scales stage))]
              (cond-> values (:alpha stage) (assoc (:alpha stage) (get-in block [:batch :opacity] 1)))))
          {} (map vector stages blocks)))

(defn- typed-fields? [group]
  (let [fields (get-in group [:cpu-plan :outputs])]
    (and (seq fields)
         (= (set (map :attribute fields)) (set (keys (expressions group))))
         (every? (fn [{:keys [attribute type]}] (= type (frame/batch-field-type attribute))) fields))))

(defn- valid-chart? [uvs n]
  (let [finite? #(and (number? %) (<= (abs (double %)) Float/MAX_VALUE))]
    (cond
      (nil? uvs) true
      (instance? double/1 uvs) (and (= (* 2 n) (alength ^doubles uvs)) (every? finite? uvs))
      (vector? uvs) (and (= n (count uvs))
                         (every? #(or (nil? %) (and (vector? %) (= 2 (count %)) (every? finite? %))) uvs))
      :else false)))

(defn- compatible-layout? [base group masked?]
  (and (same-coordinates? (:positions base) (:positions group))
       (or (same-coordinates? (:surface-uvs base) (:surface-uvs group))
           ;; The surviving request keeps its own program. A captured chart on
           ;; the covered material is immaterial to a follower that never reads UV.
           (and masked? (:surface-uvs base) (nil? (:surface-uvs group))
                (false? (get-in group [:cpu-plan :surface-uv?]))
                (not-any? #(some #{[:surface-uv]} (ir/input-paths %)) (vals (expressions group)))))))

(defn- prepare [prepare-group shapes masked?]
  (let [groups (mapv first shapes) first-group (first groups)
        targets (peek (first shapes))]
    ;; A repeated row has already seen writes from other rows of its effect.
    ;; Check once on plan creation, before compiling a row-independent shader.
    (when (and (every? typed-fields? groups)
               (or (not masked?) (and (every? #(= targets (peek %)) (rest shapes))
                                      (not-any? :preparation-error groups)
                                      (valid-chart? (:surface-uvs first-group) (count targets))))
               (= (count targets) (count (set targets)))
               (every? #(compatible-layout? first-group % masked?) (rest groups)))
      (let [stages (mapv stage (range) shapes)
            outputs (reduce (fn [acc stage] (or (fold-stage acc stage) (reduced nil))) {} stages)]
        (when outputs
          (cond-> {:stages stages
                   :coordinate-ranges (coordinate-ranges first-group (mapcat (comp vals :fields) stages))}
            (not masked?) (assoc :prepared (prepare-group outputs (:positions first-group)
                                                         (ir/compile-batch outputs) (:surface-uvs first-group)))))))))

(defn- cached-plan [cache prepare-group shapes masked?]
  (let [entries @cache
        k (if masked? [::across-masks shapes] shapes)]
    (if (contains? entries k) (get entries k)
      (let [plan (prepare prepare-group shapes masked?)]
        (swap! cache #(assoc (if (< (count %) 32) % {}) k plan))
        plan))))

(defn- fuse-run [cache prepare-group blocks masked?]
  (try
    (when-let [{:keys [stages prepared coordinate-ranges]}
               (cached-plan cache prepare-group (mapv shape blocks) masked?)]
      (let [params (captured stages blocks)
            env (assoc params ::positions coordinate-ranges)]
        (when (reduce #(or (safe-stage %1 %2 env) (reduced nil)) {} stages)
          (if masked? (peek blocks)
            {:kind :batch :source (:source (peek blocks))
             :batch {:target-ids (get-in (first blocks) [:batch :target-ids]) :blend :replace
                     :field-request {:group prepared :env {:params params}}}}))))
    ;; Missing parameters, unsupported ranges and compiler limits use the original
    ;; requests so the show can attribute any failure to the right running effect.
    (catch RuntimeException _ nil)))

(defn- partial-blend [{:keys [batch]}]
  (when-not (== 1 (:opacity batch 1))
    (:blend batch :replace)))

(defn- partial-maximum? [block]
  (= :max (partial-blend block)))

(defn- disjoint-write? [targets {:keys [kind batch assignments native-layer]}]
  (and (nil? native-layer)
       (case kind
         :batch (let [ids (:target-ids batch)]
                  (and (vector? ids) (not-any? #(contains? targets %) ids)))
         :assignments (and (vector? assignments)
                           (every? #(and (map? %) (contains? % :target-id)
                                         (not (contains? targets (:target-id %))))
                                   assignments))
         false)))

(defn- safe-maximum-run? [ids run following]
  ;; A partial add or replacement can already change the rounded result on
  ;; the CPU. A later write can also observe a backdrop rounded by the GPU.
  (or (not-any? partial-maximum? run)
      (and (not-any? #{:add :replace} (map partial-blend run))
           (or (empty? following)
               (let [targets (set ids)]
                 (every? #(disjoint-write? targets %) following))))))

(defn- append-runs
  "Try the entire aligned interval first. Split only at semantic, range or IR
  complexity limits. A failed trial never generates an exponential-size shader:
  compile-batch caps each output at 4,096 nodes and 64 nested operations."
  [cache prepare-group out blocks]
  (if (= 1 (count blocks)) (conj! out (first blocks))
    (if-let [fused (fuse-run cache prepare-group blocks false)]
      (conj! out fused)
      (if (and (some partial-maximum? blocks)
               (some #(= :add (get-in % [:batch :blend])) blocks))
        ;; A fused prefix could round its backdrop differently and hide
        ;; an invalid stage when the remaining requests run on the frame.
        (reduce conj! out blocks)
        (let [i (quot (count blocks) 2)
              left (append-runs cache prepare-group out (subvec blocks 0 i))]
          (append-runs cache prepare-group left (subvec blocks i)))))))

(defn- fuse-adjacent
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
                        (if (and (< i (count ordered)) (candidate? (nth ordered i))
                                 (= ids (get-in ordered [i :batch :target-ids])))
                          (recur (inc i)) i))]
              (if (= (inc start) end)
                (recur end consumed result)
                (let [run (subvec ordered start end)
                      lowered (when (safe-maximum-run? ids run (subvec ordered end))
                                (persistent! (append-runs cache prepare-group (transient []) run)))]
                  (if (or (nil? lowered) (= (count run) (count lowered)))
                    (recur end consumed result)
                    (recur end end (into (into (or result []) (subvec ordered consumed start)) lowered))))))))))))

(def ^:private separate-scalars #{:white :dimmer :focus :zoom})

(defn- opaque-request? [{:keys [batch] :as block}]
  (and (candidate? block) (= :replace (:blend batch :replace)) (== 1 (:opacity batch 1))))

(defn- independent-color-mask? [member-count block]
  (let [{:keys [id targets transforms inherit-backdrop? target-weights]} (:native-layer block)]
    (and (= 1 (get member-count id)) (nil? targets) (not inherit-backdrop?)
         (empty? transforms) (map? target-weights)
         (candidate? (dissoc block :native-layer)) (typed-fields? (group block))
         (= #{:color} (set (keys (expressions (group block))))))))

(defn- join-across-masks [cache prepare-group member-count lower masks upper]
  (when (and (opaque-request? lower) (opaque-request? upper))
    (let [attributes (keys (expressions (group lower)))
          final (expressions (group upper))]
      (when (and (every? separate-scalars attributes) (every? final attributes)
                 (every? #(independent-color-mask? member-count %) masks))
        ;; All earlier fields are physically overwritten. The existing reducer
        ;; proves their captured values and blended ranges before removing them.
        (fuse-run cache prepare-group [lower upper] true)))))

(defn- masked-runs [blocks]
  (let [masked? #(:native-layer (nth blocks %))]
    (filter #(masked? (first %)) (partition-by (comp boolean masked?) (range (count blocks))))))

(defn fuse
  "Lower compatible field requests while preserving ordered mask writes. A
  single-member color mask can separate a fully overwritten scalar material
  from its replacement. Unknown fields, transforms, partial opacity and
  previous-target dependencies retain their original order and validation."
  [cache prepare-group blocks]
  (let [ordered (fuse-adjacent cache prepare-group blocks)]
    (if-not (and (< 2 (count ordered)) (some :native-layer ordered)) ordered
      (let [counts (frequencies (keep #(get-in % [:native-layer :id]) ordered))]
        (loop [runs (seq (masked-runs ordered)) consumed 0 out nil]
          (if-let [run (first runs)]
            (let [start (first run) lower (dec start) upper (inc (last run))
                  masks (subvec ordered start upper)
                  fused (when (and (<= consumed lower) (< upper (count ordered)))
                          (join-across-masks cache prepare-group counts (nth ordered lower) masks (nth ordered upper)))]
              (if fused
                (let [prefix (into (or out []) (subvec ordered consumed lower))]
                  (recur (next runs) (inc upper) (conj (into prefix masks) fused)))
                (recur (next runs) consumed out)))
            (if out (into out (subvec ordered consumed)) ordered)))))))
