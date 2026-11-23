(ns afterglow.render.verified
  "Independently reproduce every field in an audience participant's slice.
  The physical output uses the local float64 reference, even for a successful check."
  (:require [afterglow.render.ir :as ir])
  (:import [java.nio ByteBuffer ByteOrder FloatBuffer]
           [java.security SecureRandom]
           [java.util Arrays]))

(defn- slice [points width start n]
  (cond (nil? points) nil
        (instance? double/1 points)
        (Arrays/copyOfRange ^doubles points (int (* width start)) (int (* width (+ start n))))
        :else (subvec (vec points) start (+ start n))))

(defn- close? [^double expected ^double actual]
  (and (Double/isFinite expected) (Double/isFinite actual)
       (<= (abs (- expected actual)) (* 1.0e-5 (max 1.0 (abs expected))))))

(defn readback
  "Return the independent CPU fields only when all returned float32 values match.
  Jobs carry a fixture-row offset and count into the captured immutable program."
  [{:keys [cpu-plan positions surface-uvs packet]} env {:keys [start count]} ^bytes bytes]
  (let [plan (:plan packet)
        cpu (ir/evaluate-batch cpu-plan env (slice positions 3 start count) (slice surface-uvs 2 start count))
        floats (.asFloatBuffer (.order (ByteBuffer/wrap bytes) ByteOrder/LITTLE_ENDIAN))]
    (when (and (= (.remaining floats) (* count (:stride plan)))
               (every?
                (fn [{:keys [attribute components offset]}]
                  (let [^doubles result (get-in cpu [:outputs attribute :values])]
                    (loop [i 0]
                      (or (= i (alength result))
                          (and (close? (aget result i)
                                       (.get floats (int (+ (* (quot i components) (:stride plan)) offset (rem i components)))))
                               (recur (inc i)))))))
                (:outputs plan)))
      cpu)))

(def ^:private random-source (delay (SecureRandom.)))

(defn- indices [n]
  (if (<= n 4)
    (range n)
    (let [^SecureRandom rng @random-source]
      (loop [rows #{}]
        (if (= 4 (count rows))
          rows
          (recur (conj rows (.nextInt rng n))))))))

(defn agree?
  "Compare all corresponding float32 values. Then independently verify up to
  four unpredictable rows selected after receipt. Colluding participants can
  still agree on an incorrect unsampled value: full verification is stronger."
  [group env job ^bytes a ^bytes b]
  (let [^FloatBuffer la (.asFloatBuffer (.order (ByteBuffer/wrap a) ByteOrder/LITTLE_ENDIAN))
        ^FloatBuffer rb (.asFloatBuffer (.order (ByteBuffer/wrap b) ByteOrder/LITTLE_ENDIAN)) width (* Float/BYTES (get-in group [:packet :plan :stride]))
        sample (fn [i]
                 (let [row (Arrays/copyOfRange a (int (* width i)) (int (* width (inc i))))]
                   (readback group env {:start (+ (:start job) i) :count 1} row)))]
    (and (= (alength a) (alength b) (* width (:count job)))
         (loop [i 0]
           (or (= i (.limit la))
               (and (close? (.get la (int i)) (.get rb (int i))) (recur (inc i)))))
         (every? sample (indices (:count job))))))
