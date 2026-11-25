(require '[afterglow.runtime.keyframes.values :as values])
(import '[com.sun.management ThreadMXBean]
        '[java.lang.management ManagementFactory]
        '[java.util Random])
(set! *warn-on-reflection* true)

(defn batch [ids fields]
  [{:kind :batch :batch {:target-ids ids :count (count ids) :outputs fields}}])

(defn field [components samples]
  {:type (if (= components 3) :vec3 :number) :components components :values (double-array samples)})

(defn validate [blocks hdr?]
  (when-not (identical? blocks (values/validate-blocks! blocks hdr?))
    (throw (ex-info "Validation changed the blocks" {}))))

(defn accept? [attr components xs hdr?]
  (let [blocks (batch [:fixture] {attr (field components xs)})
        ^doubles column (get-in blocks [0 :batch :outputs attr :values])
        before (mapv #(Double/doubleToRawLongBits %) xs)]
    (try
      (validate blocks hdr?)
      (assert (= before (mapv #(Double/doubleToRawLongBits %) column)))
      true
      (catch clojure.lang.ExceptionInfo e
        (assert (= {:type ::values/invalid-sampler} (ex-data e)))
        (assert (= "Invalid predictive endpoint" (ex-message e)))
        false))))

(defn check-boundaries! []
  (let [rng (Random. 387111)
        adjacent [(Math/nextDown 0.0) -0.0 0.0 (Math/nextUp 0.0)
                  (Math/nextDown 1.0) 1.0 (Math/nextUp 1.0)
                  (- Double/MAX_VALUE) Double/MAX_VALUE Double/NaN
                  (Double/longBitsToDouble 9221120237041090561)
                  Double/NEGATIVE_INFINITY Double/POSITIVE_INFINITY]
        inputs (into adjacent (repeatedly 1024 #(Double/longBitsToDouble (.nextLong rng))))
        fields [[:dimmer 1 false false 0.0 1.0] [:dimmer 1 true false 0.0 Double/POSITIVE_INFINITY]
                [:color 3 false false 0.0 1.0] [:color 3 true false 0.0 Double/POSITIVE_INFINITY]
                [:focus 1 false false 0.0 1.0] [:focus 1 true false 0.0 1.0]
                [:aim 3 false true Double/NEGATIVE_INFINITY Double/POSITIVE_INFINITY]
                [:direction 3 true true Double/NEGATIVE_INFINITY Double/POSITIVE_INFINITY]
                [:beat-ratio 1 true true Double/NEGATIVE_INFINITY Double/POSITIVE_INFINITY]]]
    (reduce +
            (for [[attr components hdr? unbounded? lo hi] fields
                  slot (range components)
                  x inputs]
              (let [x (double x)
                    expected (and (Double/isFinite x) (or unbounded? (<= lo x hi)))
                    xs (assoc (vec (repeat components 0.0)) slot x)]
                (assert (= expected (accept? attr components xs hdr?))
                        (pr-str [attr hdr? slot x expected]))
                1)))))

(defn measure [blocks hdr? warmup calls]
  (let [^ThreadMXBean bean (ManagementFactory/getPlatformMXBean ThreadMXBean)]
    (assert (.isThreadAllocatedMemoryEnabled bean))
    (assert (.isCurrentThreadCpuTimeSupported bean))
    (dotimes [_ warmup] (validate blocks hdr?))
    (mapv (fn [_]
            (let [alloc-before (.getCurrentThreadAllocatedBytes bean)
                  cpu-before (.getCurrentThreadCpuTime bean)
                  start (System/nanoTime)]
              (dotimes [_ calls] (validate blocks hdr?))
              (let [elapsed (- (System/nanoTime) start)
                    cpu (- (.getCurrentThreadCpuTime bean) cpu-before)
                    allocated (- (.getCurrentThreadAllocatedBytes bean) alloc-before)]
                {:calls calls :allocated-bytes allocated :cpu-ns cpu :elapsed-ns elapsed})))
          (range 7))))

(defn fixture-ids [n] (mapv #(str "owned-fixture-" %) (range n)))

(let [ids (fixture-ids 20064)
      movers (subvec ids 20000)
      dimmer (batch ids (array-map :dimmer (field 1 (repeat 20064 0.375))))
      rgbw (batch ids (array-map :color (field 3 (repeat (* 3 20064) 0.375))
                                 :white (field 1 (repeat 20064 1.5))
                                 :dimmer (field 1 (repeat 20064 -0.0))))
      mover (batch movers (array-map :aim (field 3 (take (* 3 64) (cycle [-2.0 4.0 1.5])))
                                     :focus (field 1 (repeat 64 0.25))
                                     :beat-ratio (field 1 (repeat 64 (/ 7.0 3.0)))))
      cases (array-map :dimmer [dimmer false 20064 200 40]
                       :hdr-rgbw [rgbw true 100320 200 40]
                       :mover [mover false 320 3000 4000])]
  (prn {:java (System/getProperty "java.runtime.version")
        :clojure (clojure-version)
        :boundary-checks (check-boundaries!)
        :cases (into {} (for [[id [blocks hdr? components warmup calls]] cases]
                          [id {:rows (count (get-in blocks [0 :batch :target-ids])) :components components
                               :hdr? hdr? :warmup warmup :samples (measure blocks hdr? warmup calls)}]))}))
