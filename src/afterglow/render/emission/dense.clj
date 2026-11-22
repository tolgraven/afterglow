(ns afterglow.render.emission.dense
  "Compiled output addresses for applying frame-wide emission policies. Each
  processor returns privately owned buffers and reuses immutable patch layout."
  (:require [afterglow.render.photometry :as photometry]))

(deftype Lane [^long u ^long i ^long fu ^long fi ^double pivot spec ^double red ^double green ^double blue])
(deftype Head [id ^long index ^long start dimmer ^objects emitters ^double red ^double green ^double blue])

(defn- lane [indices spec tint]
  (let [[u i] (:coarse spec) [fu fi] (:fine spec) [r g b] tint]
    (Lane. (long (indices u)) (long i) (if fu (long (indices fu)) -1) (long (or fi -1)) (double (:inverted-from spec -1)) spec
           (double r) (double g) (double b))))

(defn compile-layout [fixtures universes light-key]
  (let [indices (zipmap universes (range))
        heads (object-array (count fixtures))]
    (loop [i 0 offset 0]
      (if (= i (count fixtures)) {:heads heads :size offset :universes universes}
        (let [fixture (nth fixtures i) channels (light-key fixture)]
          (if-not channels (recur (inc i) offset)
            (let [[r g b] (:emission-color fixture [1.0 1.0 1.0])
                  emitters (object-array (for [[attr spec] (dissoc channels :dimmer)]
                                          (lane indices spec (second (photometry/emitter-spectrum attr)))))
                  dimmer (when-let [spec (:dimmer channels)] (lane indices spec [r g b]))]
              (aset heads i (Head. (:id fixture) i offset dimmer emitters r g b))
              (recur (inc i) (+ offset (max 1 (alength emitters)))))))))))

(defn- decode ^double [raw pivot]
  (/ (if (and pivot (>= raw pivot)) (+ pivot (- 255.0 raw)) raw) 255.0))

(defn packed-word
  "Nearest physical word, or greatest deliverable logical level <= target.
  A fractional inversion pivot splits the two monotone runs at its first
  representable DMX step. Quantizing across that boundary can turn a tiny
  correction into full output, so consider the runs separately."
  [channel x down?]
  (let [scale (if (:fine channel) 255 1)
        pivot (:inverted-from channel)
        maximum (* 255 scale)
        split (if pivot (long (Math/ceil (* scale (double pivot)))) (inc maximum))
        raw (* x 255.0)
        choose (fn [desired lo hi descending?]
                 (when (<= lo hi)
                   (let [word (long (if down?
                                      (if descending? (Math/ceil desired) (Math/floor desired))
                                      (Math/round (double desired))))
                         word (max lo (min hi word))
                         value (decode (/ word (double scale)) pivot)]
                     (if (or (not down?) (<= value x)) [word value]
                       ;; Floating-point conversion at an exact step can
                       ;; exceed x by one ulp. Try its lower-drive neighbor.
                       (let [adjacent ((if descending? inc dec) word)]
                         (when (<= lo adjacent hi)
                           [adjacent (decode (/ adjacent (double scale)) pivot)]))))))
        left (choose (* scale raw) 0 (dec split) false)
        right (when pivot (choose (* scale (+ pivot (- 255.0 raw))) split maximum true))]
    (cond (nil? left) (first right)
          (nil? right) (first left)
          (<= (abs (- x (second left))) (abs (- x (second right)))) (first left)
          :else (first right))))

(defn- level ^double [^objects buffers ^Lane lane]
  (let [raw (bit-and 255 (aget ^bytes (aget buffers (.-u lane)) (.-i lane)))
        x (if (neg? (.-fu lane)) (double raw)
            (+ raw (/ (bit-and 255 (aget ^bytes (aget buffers (.-fu lane)) (.-fi lane))) 255.0)))]
    (let [pivot (.-pivot lane)] (/ (if (and (>= pivot 0.0) (>= x pivot)) (+ pivot (- 255.0 x)) x) 255.0))))

(defn- write! [^objects buffers ^Lane lane ^double x down?]
  (let [fine? (not (neg? (.-fu lane)))
        spec (.-spec lane)
        word (long (if (or fine? (>= (.-pivot lane) 0.0))
                     (packed-word spec x down?)
                     (let [v (* 255.0 x)]
                       (if down? (let [i (long (Math/floor v))]
                                   (if (> (/ i 255.0) x) (dec i) i))
                         (Math/round v)))))]
    (aset-byte ^bytes (aget buffers (.-u lane)) (.-i lane) (unchecked-byte (if fine? (quot word 255) word)))
    (when fine? (aset-byte ^bytes (aget buffers (.-fu lane)) (.-fi lane) (unchecked-byte (rem word 255))))))

(defn- packed [frame layout]
  (object-array (map (:universes frame) (:universes layout))))

(defn- output [frame layout copy]
  (let [out (copy frame)]
    {:frame out :buffers (packed out layout)
     :changed (when (:values frame) (boolean-array (count (:target-order frame))))
     :rgb (get-in out [:compact :fields :emitted-color :values])
     :intensity (get-in out [:compact :fields :intensity :values])}))

(defn- project! [{:keys [^objects buffers ^booleans changed ^doubles rgb ^doubles intensity]} ^Head head]
  (let [i (.-index head)]
    (when changed (aset-boolean changed i true))
    (when rgb
      (let [base (* 3 i)
            ^objects es (.-emitters head)
            d (if-let [d (.-dimmer head)] (level buffers d) 1.0)]
        (if (zero? (alength es))
          (do (aset-double intensity i d)
              (aset-double rgb base (* d (.-red head)))
              (aset-double rgb (inc base) (* d (.-green head)))
              (aset-double rgb (+ base 2) (* d (.-blue head))))
          (loop [j 0 peak 0.0 r 0.0 g 0.0 b 0.0]
            (if (= j (alength es))
              (do (aset-double intensity i (if (.-dimmer head) d peak))
                  (aset-double rgb base (* d (min 1.0 r)))
                  (aset-double rgb (inc base) (* d (min 1.0 g)))
                  (aset-double rgb (+ base 2) (* d (min 1.0 b))))
              (let [^Lane e (aget es j)
                    x (level buffers e)]
                (recur (inc j) (max peak x) (+ r (* x (.-red e))) (+ g (* x (.-green e))) (+ b (* x (.-blue e))))))))))))

(defn- unit! ^double [x]
  (when-not (and (number? x) (<= 0 x 1)) (throw (ex-info "Expected normalized fixture gain" {:gain x})))
  (double x))

(def ^:private doubles-class (class (double-array 0)))
(defn- column [values n]
  (when (instance? doubles-class values)
    (when-not (= n (alength ^doubles values))
      (throw (ex-info "A control column must match the compiled fixture order" {})))
    values))

(defn scale [layout frame gains copy]
  (let [^objects heads (:heads layout)
        ^doubles gain-array (column gains (alength heads))
        owned (delay (output frame layout copy))]
    (dotimes [i (alength heads)]
      (when-let [^Head h (aget heads i)]
        (let [gain (unit! (if gain-array (aget gain-array i) (get gains (.-id h) 1.0)))]
          (when (< gain 1.0)
            (let [{:keys [^objects buffers] :as out} @owned
                  ^objects es (.-emitters h)]
              (if-let [d (.-dimmer h)]
                (write! buffers d (* gain (level buffers d)) true)
                (dotimes [j (alength es)]
                  (let [lane (aget es j)] (write! buffers lane (* gain (level buffers lane)) true))))
              (project! out h))))))
    (if (realized? owned) @owned {:frame frame})))

(defn- filter-level ^double [^double previous ^double goal ^double coefficient ^double ceiling]
  (let [x (+ previous (* coefficient (- goal previous)))]
    (min ceiling (if (< (abs (- x goal)) 1.0e-9) goal x))))

(defn follow
  "Track physical emitter products in a private, patch-ordered precision buffer.
  Changed DMX bytes and projection values use separate output-owned buffers."
  [layout frame previous prior-frame attack release ceiling copy]
  (let [^objects heads (:heads layout)
        size (long (:size layout)) n (alength heads)
        ^doubles prior (column previous size)
        ^doubles next-levels (double-array size)
        ^doubles aa (column attack n) ^doubles rr (column release n)
        global-a (if aa 0.0 (double attack)) global-r (if rr 0.0 (double release))
        cap (unit! ceiling)
        source (packed frame layout)
        seed (when prior-frame (packed prior-frame layout))
        owned (delay (output frame layout copy))]
    (dotimes [i n]
      (when-let [^Head head (aget heads i)]
        (let [^objects es (.-emitters head) offset (.-start head) lamp? (zero? (alength es))
              dimmer (.-dimmer head)
              d (if dimmer (level source dimmer) 1.0)
              d0 (if (and seed dimmer) (level seed dimmer) 1.0)
              a (if aa (aget aa i) global-a) r (if rr (aget rr i) global-r)
              active? (and (>= a 0) (>= r 0)) width (max 1 (alength es))
              known? (and prior (not (Double/isNaN (aget prior offset))))]
          (when (or (not (Double/isFinite a)) (not (Double/isFinite r)) (> a 1.0) (> r 1.0))
            (throw (ex-info "Response coefficients are bounded by one; negative means bypass" {:attack a :release r})))
          (if-not active?
            (java.util.Arrays/fill next-levels (int offset) (int (+ offset width)) Double/NaN)
            (loop [j 0 peak 0.0 changed? false]
            (if (= j width)
              (when changed?
                (let [{:keys [^objects buffers] :as out} @owned]
                  (if lamp?
                    (write! buffers dimmer (aget next-levels offset) false)
                    (let [next-d (if dimmer (max d peak) 1.0)]
                      (when dimmer (write! buffers dimmer next-d false))
                      (when (pos? next-d)
                        (dotimes [k width]
                          (write! buffers (aget es k) (/ (aget next-levels (+ offset k)) next-d) false)))))
                  (project! out head)))
              (let [idx (+ offset j) lane (when-not lamp? (aget es j))
                    goal (if lamp? d (* d (level source lane)))
                    old (cond known? (aget prior idx)
                              seed (if lamp? d0 (* d0 (level seed lane)))
                              :else 0.0)
                    x (filter-level old goal (if (> goal old) a r) cap)]
                (aset-double next-levels idx x)
                (recur (inc j) (max peak x) (or changed? (not (== x goal)))))))))))
    (assoc (if (realized? owned) @owned {:frame frame}) :levels next-levels)))
