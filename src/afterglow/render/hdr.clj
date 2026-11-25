(ns afterglow.render.hdr
  "Linear light overdrive and single-bounce spatial highlights before DMX packing."
  (:require [afterglow.render.photometry :as photometry]
            [afterglow.render.hdr.packed :as packed]
            [afterglow.render.shutter :as shutter]
            [thi.ng.color.core :as color]))

(def emitters (set (keys photometry/emitter-spectrum)))

(def light-attributes (conj emitters :color :dimmer))

(defn- nonnegative? [n] (and (number? n) (Double/isFinite (double n)) (not (neg? n))))

(defn validate!
  "Validate resolved, portable frame controls. Distances are metres."
  [settings]
  (let [{:keys [gain source-gains cue-gains instance-gains fixture-ids max-excess
                white-mix spill spill-white-mix radius falloff]
         :or {gain 1 max-excess 1 white-mix 1 spill 0 spill-white-mix 1 radius 1 falloff :linear}} settings]
    (when-not (and (map? settings)
                   (every? #{:gain :source-gains :cue-gains :instance-gains :fixture-ids
                             :max-excess :white-mix :spill :spill-white-mix :radius :falloff} (keys settings))
                   (every? nonnegative? [gain max-excess radius])
                   (every? #(and (nonnegative? %) (<= % 1)) [white-mix spill spill-white-mix])
                   (#{:linear :quadratic :smoothstep} falloff)
                   (or (nil? fixture-ids) (vector? fixture-ids) (set? fixture-ids))
                   (every? #(or (nil? %) (and (map? %) (every? nonnegative? (vals %))))
                           [source-gains cue-gains instance-gains]))
      (throw (ex-info "Invalid HDR gain, scope, spill or highlight settings" {:settings settings}))))
  settings)

(defn- rgb-attrs? [channels] (every? channels [:red :green :blue]))

;; A lane has both a storage offset and a visible RGB basis. Only the selected
;; native primary/white lanes receive spill. Invisible UV never radiates a halo.
(defrecord Lane [attribute slot tint receive])

(defrecord Head [id index position rgb? extract? lamp? physical virtual shutters])

(defn- lanes [attrs slots rgb?]
  (mapv (fn [attribute]
          (let [rgb (second (photometry/emitter-spectrum attribute))
                receive (cond
                          rgb? (case attribute :red 0 :green 1 :blue 2 nil)
                          (= attribute :uv) nil
                          :else :tint)]
            (->Lane attribute (slots attribute) rgb receive))) attrs))

(defn- head [i {:keys [id channels position rgbw-policy emission-color compiled-channels]} slots]
  (let [attrs (sort (filter emitters (keys channels)))
        rgb? (rgb-attrs? channels)
        physical (lanes attrs slots rgb?)
        virtual (when rgb? (into [(->Lane :r 0 [1 0 0] 0) (->Lane :g 1 [0 1 0] 1) (->Lane :b 2 [0 0 1] 2)]
                                 (remove #(#{:red :green :blue :white} (:attribute %))) physical))
        lamp? (and (empty? attrs) (:dimmer channels) (not-any? channels [:fog :haze :fan :relay :pump]))
        shutters (shutter/profile compiled-channels)]
    (when (or lamp? (seq attrs))
      (assoc (->Head id i position rgb? (= rgbw-policy :extract-min) (boolean lamp?)
                     (if lamp? [(->Lane :dimmer 3 (or emission-color [1 1 1]) :tint)] physical) virtual shutters)
             :white? (contains? channels :white)
             :simple-rgb? (and rgb? (every? #{:red :green :blue :white} attrs))
             :scan-slots (int-array (into [0 1 2 3] (map :slot) physical))))))

(defn- spatial-index [heads]
  (let [axis (if (seq heads)
               (apply max-key (fn [axis]
                                (let [xs (map #(nth (:position %) axis) heads)]
                                  (- (reduce max xs) (reduce min xs)))) [0 1 2]) 0)
        ordered (vec (sort-by #(nth (:position %) axis) heads))]
    {:spatial ordered :axis axis :coords (double-array (map #(nth (:position %) axis) ordered))}))

(defn layout
  "Build the ordered photometric lane and spatial index for a patch once."
  [fixtures slots]
  (let [heads (into [] (keep-indexed #(head %1 %2 slots)) fixtures)]
    (assoc (spatial-index heads) :heads heads
           ;; A moving mirror or other utility can receive a field event even
           ;; without emitting any light. Build its index only on observation.
           :listeners (delay (spatial-index (map-indexed (fn [i fixture]
                                                           (assoc (select-keys fixture [:id :position]) :index i))
                                                         fixtures))))))

(defn- lower-bound [^doubles coords x]
  (loop [lo 0 hi (alength coords)]
    (if (= lo hi) lo
      (let [mid (unsigned-bit-shift-right (+ lo hi) 1)]
        (if (< (aget coords mid) (double x)) (recur (inc mid) hi) (recur lo mid))))))

(defn- scatter! [{:keys [spatial axis coords]} head allowed ^doubles incident ^doubles excess settings contacts]
  (let [[x y z :as pos] (:position head)
        radius (double (:radius settings 1))
        center (double (nth pos axis))
        ^doubles coords coords
        spill (double (:spill settings 0))
        falloff (:falloff settings :linear)]
    (when (pos? radius)
      (loop [k (long (lower-bound coords (- center radius)))]
        (when (and (< k (alength coords)) (< (aget coords k) (+ center radius)))
          (let [other (nth spatial k)]
            (when (and (not= (:index other) (:index head)) (or (nil? allowed) (contains? allowed (:id other))))
              (let [[a b c] (:position other)
                    dx (- (double a) (double x)) dy (- (double b) (double y)) dz (- (double c) (double z))
                    t (- 1.0 (/ (Math/sqrt (+ (* dx dx) (* dy dy) (* dz dz))) radius))]
                (when (pos? t)
                  (let [weight (case falloff :linear t :quadratic (* t t) :smoothstep (* t t (- 3.0 (* 2.0 t))))
                        f (* spill weight)
                        at (* 3 (long (:index other)))]
                    (when contacts
                      (vswap! contacts assoc! (:id other)
                              (* weight (max (aget excess 0) (aget excess 1) (aget excess 2)))))
                    (when (pos? f)
                      (dotimes [c 3]
                        (aset incident (+ at c) (min Double/MAX_VALUE (+ (aget incident (+ at c)) (* f (aget excess c))))))))))))
          (recur (inc k)))))))

(defn- receiver-level ^double [receive tint ^doubles incident at]
  (cond
    (int? receive) (aget incident (+ (int at) (int receive)))
    (= :tint receive) (let [[r g b] tint]
                        (/ (+ (* (double r) (aget incident (int at)))
                              (* (double g) (aget incident (inc (int at))))
                              (* (double b) (aget incident (+ (int at) 2))))
                           (max 1.0e-12 (+ (double r) (double g) (double b)))))
    :else 0.0))

(defn- read-row
  "Decode native emitter precedence before applying gain. Leave the :color lane
  intact when no explicit RGBW overrides require physical emitter mixing."
  [head read-value]
  (let [color (read-value :color [0.0 0.0 0.0])
        [r g b] color
        virtual? (and (:rgb? head) (not-any? #(some? (read-value % nil)) [:red :green :blue :white]))
        lanes (if virtual? (:virtual head) (:physical head))
        x (if (:extract? head) (double (min r g b)) 0.0)
        dimmer (double (read-value :dimmer (if (:lamp? head) 0.0 1.0)))
        levels (double-array (count lanes))]
    (dotimes [j (count lanes)]
      (let [a (:attribute (nth lanes j))]
        (aset levels j (double (case a
                                 :r r :g g :b b
                                 :red (read-value a (- (double r) x)) :green (read-value a (- (double g) x))
                                 :blue (read-value a (- (double b) x)) :white (read-value a x)
                                 :dimmer 1.0 (read-value a 0.0))))))
    {:lanes lanes :levels levels :dimmer dimmer :virtual? virtual? :color color}))

(defn- source-excess [row gain limit]
  (let [{:keys [lanes levels dimmer]} row
        ^doubles levels levels
        scale (min Double/MAX_VALUE (* (double gain) (double dimmer)))
        out (double-array 3)]
    (dotimes [j (alength levels)]
      (let [raw (min Double/MAX_VALUE (* scale (aget levels j)))]
        (when (> raw 1.0)
          (let [tint (:tint (nth lanes j)) extra (- raw 1.0)]
            (dotimes [c 3] (aset out c (+ (aget out c) (* extra (double (nth tint c))))))))))
    (dotimes [c 3] (aset out c (min (double limit) (aget out c))))
    out))

(defn- write-row [row head gain source-white ^doubles incident at spill-white]
  (let [{:keys [lanes levels dimmer virtual?]} row
        ^doubles levels levels
        scale (min Double/MAX_VALUE (* (double dimmer) (double gain)))
        changed (double-array (alength levels))
        peak (loop [j 0 peak 0.0]
               (if (= j (alength levels)) peak
                 (let [{:keys [receive tint]} (nth lanes j)
                       base (min 1.0 (* scale (aget levels j)))
                       source (if receive (+ base (* (double source-white) (- 1.0 base))) base)
                       lit (min 1.0 (+ source (receiver-level receive tint incident at)))
                       final (if receive (+ lit (* (double spill-white) (- 1.0 lit))) lit)]
                   (aset changed j final)
                   (recur (inc j) (max peak final)))))
        ;; Preserve physical dimmer use at its original ratio when possible.
        ;; Lift the dimmer only enough to represent a brighter or incident lane.
        d (if (:lamp? head) peak (max peak (min 1.0 scale)))]
    (if (:lamp? head) {:dimmer d}
      (let [normalized (fn [i] (if (pos? d) (/ (aget changed (int i)) d) 0.0))
            start (cond-> {:dimmer d}
                    virtual? (assoc :color (mapv normalized (range 3)))
                    (and (not virtual?) (some #(> (double %) 1.0) (:color row)))
                    (assoc :color (mapv #(min 1.0 (double %)) (:color row))))]
        (reduce (fn [m j] (assoc m (:attribute (nth lanes j)) (normalized j)))
                start (range (if virtual? 3 0) (count lanes)))))))

(defn process!
  "Read the composed native field of each emitter and write only normalized
  changes to the private frame scratch. Incoming spill is accumulated from the
  untouched first pass. No fixture can feed received energy back into the pass."
  [layout settings read-at! write-at! high-at? fixture-count packed observe?]
  (let [allowed (some-> (:fixture-ids settings) set)
        scoped? #(or (nil? allowed) (contains? allowed (:id %)))
        default-white (if (seq settings) 1.0 0.0)
        source-white-mix (double (:white-mix settings default-white))
        spill-white-mix (double (:spill-white-mix settings default-white))
        gain (:gain settings 1.0)
        gains (:source-gains settings)
        limit (:max-excess settings 1.0)
        spill? (and (pos? (:spill settings 0)) (pos? (:radius settings 1)))
        contacts (when observe? (volatile! (transient {})))
        incident (double-array (* 3 fixture-count))
        sources (object-array fixture-count)
        gain-frame (double-array fixture-count 1.0)
        whites (double-array fixture-count)
        changed (boolean-array fixture-count)
        tmp (double-array 3)]
    (doseq [head (:heads layout)]
      (let [i (int (:index head))
            g (min Double/MAX_VALUE (* (double (if (scoped? head) gain 1.0)) (double (get gains (:id head) 1.0))))]
        (when (or (not (== g 1.0)) (high-at? head))
          (let [read-value #(read-at! i %1 %2)
                ^doubles excess (if (packed/eligible? packed head)
                                  (do (packed/excess! packed head [g limit] tmp) tmp)
                                  (let [row (read-row head read-value)]
                                    (aset sources i row)
                                    (source-excess row g limit)))
                peak (max (aget excess 0) (aget excess 1) (aget excess 2))]
            (aset changed i true)
            (aset gain-frame i g)
            (when (and (pos? peak) (scoped? head))
              (aset whites i (min 1.0 (* source-white-mix peak)))
              (when (and (or spill? observe?) (shutter/open? (:shutters head) read-value))
                (let [received (when observe? (volatile! (transient {})))]
                  (scatter! (if observe? @(:listeners layout) layout) head allowed incident excess settings received)
                  (when received
                    (let [found (persistent! @received)]
                      (when (seq found) (vswap! contacts assoc! (:id head) found)))))))))))
    (doseq [head (:heads layout)]
      (let [i (int (:index head)) at (* i 3)
            halo (max (aget incident at) (aget incident (inc at)) (aget incident (+ at 2)))]
        (when (or (aget changed i) (pos? halo))
          (let [gain (aget gain-frame i) white (aget whites i)
                spill-white (min 1.0 (* spill-white-mix halo))]
            (if (packed/eligible? packed head)
              (packed/write! packed head incident [gain white spill-white])
              (let [row (or (aget sources i) (read-row head #(read-at! i %1 %2)))]
                (write-at! i (write-row row head gain white incident at spill-white))))))))
    (when contacts (persistent! @contacts))))

(defn- contribution-gain [{:keys [source emission-gain]} {:keys [cue-gains instance-gains]}]
  (let [g (* (double (or emission-gain 1)) (double (get cue-gains (:cue-id source) 1))
             (double (get instance-gains (:instance-id source) 1)))]
    (when-not (nonnegative? g) (throw (ex-info "Invalid cue emission gain" {:effect-source source})))
    g))

(defn- gain-owner [block]
  (or (get-in block [:source :instance-id]) (get-in block [:source :cue-id]) (:source block)))

(defn- dimmer-targets [blocks]
  (reduce (fn [by-owner {:keys [kind compiled assignments] :as block}]
            (let [ids (case kind
                        :assignments (keep #(when (and (= :dimmer (:attribute %)) (pos? (:opacity % 1)))
                                              (:target-id %)) assignments)
                        :batch (when (and (pos? (:opacity compiled)) (some #(= :dimmer (:attribute %)) (:columns compiled)))
                                 (:target-ids compiled)))]
              (if (seq ids) (update by-owner (gain-owner block) (fnil into #{}) ids) by-owner)))
          {} blocks))

(defn- scale-column [targets scale? scale {:keys [attribute components values source-stride] :as column}]
  (if-not (light-attributes attribute)
    column
    (let [width (long components) stride (long (or source-stride width)) ^doubles source values
          eligible? #(scale? attribute %)]
      (if (and (zero? stride) (seq targets) (every? eligible? targets))
        (assoc column :values (double-array (map scale source)))
        (let [result (double-array (* (count targets) width))]
          (dotimes [row (count targets)]
            (let [gain? (eligible? (nth targets row))]
              (dotimes [component width]
                (let [value (aget source (+ (* row stride) component))]
                  (aset result (+ (* row width) component) (if gain? (double (scale value)) value))))))
          (assoc column :values result :source-stride width))))))

(defn- scale-block [{:keys [kind compiled assignments source] :as block} dimmers selected emitting? g]
  (let [scale? (fn [attr id] (and (light-attributes attr) (emitting? id) (or (nil? selected) (contains? selected id))
                                  (or (= :dimmer attr) (not (contains? dimmers id)))))
        scale (fn [v]
                (when-not (nonnegative? v)
                  (throw (ex-info "Invalid light input before cue gain" {:value v :effect-source source})))
                (let [v (* (double v) (double g))]
                  (when-not (nonnegative? v) (throw (ex-info "Cue emission gain overflow" {:effect-source source}))) v))]
    (case kind
      :assignments (assoc block :assignments
                          (mapv (fn [{:keys [attribute target-id value] :as a}]
                                  (if (scale? attribute target-id)
                                    (assoc a :value (if (= :color attribute)
                                                      (if (vector? value) (mapv scale value)
                                                        (let [c (color/as-rgba value)]
                                                          (mapv scale [(:r c) (:g c) (:b c)])))
                                                      (scale value))) a)) assignments))
      :batch (update-in block [:compiled :columns]
                        #(mapv (partial scale-column (:target-ids compiled) scale? scale) %)))))

(defn contribution-gains?
  "Whether HDR may scale ordered contributions before blending, including
  intrinsic emission gain tags that enable HDR without explicit settings."
  [blocks {:keys [cue-gains instance-gains]}]
  (or (not (contains? #{nil {}} cue-gains))
      (not (contains? #{nil {}} instance-gains))
      (boolean (some :emission-gain blocks))))

(defn apply-contribution-gains
  "Scale an owner's dimmer or its emitters exactly once, ahead of composition.
  Fresh typed buffers keep retries and captures independent."
  [blocks settings emitting?]
  (if-not (and settings (contribution-gains? blocks settings))
    blocks
    (let [dimmers (dimmer-targets blocks) selected (some-> (:fixture-ids settings) set)
          applies? #(and (emitting? %) (or (nil? selected) (contains? selected %)))]
      (mapv (fn [block]
              (let [g (contribution-gain block settings)]
                (cond
                  (== 1.0 g) block
                  (seq (get-in block [:native-layer :transforms]))
                  (assoc block ::member-gain g ::gain-target? applies?)
                  :else (scale-block block (dimmers (gain-owner block)) selected emitting? g)))) blocks))))
