(ns afterglow.bench-movement-reference
  "Independent matrix/calibration and physical DMX oracle for developer benchmarks.
  Deliberately does not call production render functions. The benchmark contract
  uses RGBW heads, explicit degree-interval calibration and integer/pair channels;
  it is not another production fixture interpreter.")

(defn- dot [a b] (reduce + (map * a b)))
(defn- transpose [matrix] (apply mapv vector matrix))
(defn- matrix-product [a b] (mapv (fn [row] (mapv #(dot row %) (transpose b))) a))
(defn- local-vector [rotation world]
  (let [[x y z] (map #(Math/toRadians (double %)) rotation)
        cx (Math/cos x) sx (Math/sin x) cy (Math/cos y) sy (Math/sin y) cz (Math/cos z) sz (Math/sin z)
        rx [[1.0 0.0 0.0] [0.0 cx (- sx)] [0.0 sx cx]]
        ry [[cy 0.0 sy] [0.0 1.0 0.0] [(- sy) 0.0 cy]]
        rz [[cz (- sz) 0.0] [sz cz 0.0] [0.0 0.0 1.0]]
        world-basis (matrix-product rz (matrix-product ry rx))]
    ;; Forward placement matrix is inverted by transposition for rigid rotation.
    (mapv #(dot % world) (transpose world-basis))))

(defn- normalized [fixture axis angle previous]
  (let [{lo :min-deg hi :max-deg} (get-in fixture [:calibration axis])
        convert #(/ (- % lo) (- hi lo))
        candidates (mapv convert (if (= :pan axis) [angle (- angle 360.0) (+ angle 360.0)] [angle]))
        legal (filterv #(<= 0.0 % 1.0) candidates)
        chosen (first (sort-by #(Math/abs (- (double %) (double (or previous (convert 0.0)))))
                              (if (seq legal) legal candidates)))]
    (max 0.0 (min 1.0 chosen))))

(defn reference-geometry [fixture aim previous]
  (let [world (mapv - aim (:position fixture))
        [x y z] (local-vector (:rotation-deg fixture) world)
        size (Math/sqrt (dot world world))]
    {:pan (normalized fixture :pan (Math/toDegrees (Math/atan2 x z)) (:pan previous))
     :tilt (normalized fixture :tilt (Math/toDegrees (Math/atan2 y (Math/hypot x z))) (:tilt previous))
     :direction (mapv #(/ % size) world)}))

(defn- check! [expected actual details]
  (when-not (if (number? expected)
              (and (number? actual) (<= (Math/abs (- (double expected) (double actual))) 1e-9))
              (= expected actual))
    (throw (ex-info "Moving-head reference mismatch" (assoc details :expected expected :actual actual)))))

(defn- expected-bytes [level fine?]
  (if fine?
    (let [code (Math/round (* 65535.0 (double level)))]
      [(quot code 256) (rem code 256)])
    [(Math/round (* 255.0 (double level)))]))

(defn- slot-byte [universes fixture offset]
  (let [slot (+ (dec (:address fixture)) (dec offset))
        universe (+ (:universe fixture) (quot slot 512))]
    (bit-and 255 (aget ^bytes (get universes universe) (mod slot 512)))))

(defn check-frame!
  "Check every normalized axis and physical channel against explicit expected assignments.
  Inputs use the public fixture contract; no engine, compiler or IO is involved."
  [fixtures assignments previous-preview preview universes]
  (check! (count fixtures) (count assignments) {:field :all-head-assignments})
  (check! (count fixtures) (count preview) {:field :all-head-preview})
  (doseq [[index fixture] (map-indexed vector fixtures)]
    (let [actual (nth preview index) assigned (nth assignments index)
          geometry (when (:aim assigned) (reference-geometry fixture (:aim assigned) (get previous-preview index)))
          color (:color assigned [0.0 0.0 0.0]) white (:white assigned 0.0) dimmer (:dimmer assigned 1.0)
          values (merge {:pan 0.0 :tilt 0.0 :focus 0.0 :zoom 0.0 :white white :dimmer dimmer}
                        (zipmap [:red :green :blue] color) assigned geometry)]
      (check! (:id fixture) (:id actual) {:fixture index :field :id})
      (doseq [field [:pan :tilt :focus :zoom]]
        (check! (get values field) (get actual field) {:fixture index :field field}))
      (doseq [field [:aim :direction]]
        (if-let [expected (get values field)]
          (doseq [component (range 3)]
            (check! (nth expected component) (get-in actual [field component]) {:fixture index :field field :component component}))
          (check! nil (get actual field) {:fixture index :field field})))
      (doseq [[field offsets] (:channels fixture)
              :let [offsets (if (vector? offsets) offsets [offsets])
                    bytes (expected-bytes (get values field) (= 2 (count offsets)))]
              [offset expected] (map vector offsets bytes)]
        (check! expected (slot-byte universes fixture offset) {:fixture index :field field :channel-offset offset}))))
  {:checked-heads (count fixtures) :checked-heads-after-16 (max 0 (- (count fixtures) 16))
   :universe-checksum (reduce (fn [checksum [_ bytes]]
                               (unchecked-add-int (unchecked-multiply-int 31 checksum) (java.util.Arrays/hashCode ^bytes bytes)))
                             1 (sort-by key universes))})

(defn self-check! []
  (let [fixture {:position [0.0 0.0 0.0] :rotation-deg [0.0 0.0 0.0]
                 :calibration {:pan {:min-deg -270.0 :max-deg 270.0}
                               :tilt {:min-deg -135.0 :max-deg 135.0}}}
        forward (reference-geometry fixture [0.0 0.0 1.0] nil)
        rotated (reference-geometry (assoc fixture :rotation-deg [0.0 90.0 0.0]) [1.0 0.0 0.0] nil)
        pitched (reference-geometry (assoc fixture :rotation-deg [90.0 0.0 0.0]) [0.0 -1.0 0.0] nil)
        rolled (reference-geometry (assoc fixture :rotation-deg [0.0 0.0 90.0]) [0.0 1.0 0.0] nil)]
    (check! 0.5 (:pan forward) {:case :forward})
    (check! 0.5 (:tilt forward) {:case :forward})
    (check! 0.5 (:pan rotated) {:case :rotated-forward})
    (check! 0.5 (:tilt pitched) {:case :pitched-forward})
    (check! (/ 2.0 3.0) (:pan rolled) {:case :rolled-right})
    (check! [0 255] (expected-bytes (/ 255.0 65535.0) true) {:case :before-carry})
    (check! [1 0] (expected-bytes (/ 256.0 65535.0) true) {:case :after-carry})
    (check! [128 0] (expected-bytes 0.5 true) {:case :midpoint})
    (check! [255 255] (expected-bytes 1.0 true) {:case :full-scale})
    true))
