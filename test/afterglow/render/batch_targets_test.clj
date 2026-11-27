(ns afterglow.render.batch-targets-test
  "Typed batch target validation and target indices on a mixed rig.

  Batch bytes are checked against the scalar assignment path, which never
  reads batch target plans. Errors are checked by message and ex-data. Each
  case also runs warm (one compiled patch reused across frames) and cold (a
  freshly compiled patch per call)."
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.render.frame :as frame])
  (:import [java.util.concurrent Executors TimeUnit Callable]))

(defn- place [fixtures]
  ;; Pack fixtures from address 497 so the rig crosses a universe boundary.
  (loop [offset 496 [fixture & more] fixtures out []]
    (if-not fixture out
      (let [footprint (reduce max (flatten (vals (:channels fixture))))]
        (recur (+ offset footprint) more
               (conj out (assoc fixture :universe (inc (quot offset 512)) :address (inc (mod offset 512)))))))))

(defn- mixed-rig []
  (place (vec (concat
               (for [i (range 12)] {:id (keyword (str "p" i)) :position [(double i) 0.0 0.0]
                                    :channels {:red 1 :green 2 :blue 3 :white 4}})
               (for [i (range 4)] {:id (keyword (str "d" i)) :position [0.0 1.0 (double i)] :channels {:dimmer 1}})
               (for [i (range 4)] {:id (keyword (str "r" i)) :position [1.0 1.0 (double i)]
                                   :channels {:red 1 :green 2 :blue 3 :dimmer 4}})
               (for [i (range 2)] {:id (keyword (str "m" i)) :position [2.0 4.0 (double i)]
                                   :channels {:red 1 :green 2 :blue 3 :white 4 :dimmer 5 :pan [6 7] :tilt 8}})))))

(defn- ids [prefix n] (mapv #(keyword (str prefix %)) (range n)))

;; One vector instance per batch, as a compiled effect holds it across frames.
(def ^:private targets
  {:all-pixels (ids "p" 12)
   :every-other-pixel (vec (take-nth 2 (ids "p" 12)))
   :reversed-pixels (vec (rseq (ids "p" 12)))
   :repeated [:p1 :p1 :p2 :p0]
   :whole-rig (vec (concat (ids "p" 12) (ids "d" 4) (ids "r" 4) (ids "m" 2)))
   :pars-and-movers (vec (concat (ids "r" 4) (ids "m" 2)))
   :white-heads [:m1 :p3 :m0 :p7]
   :movers (ids "m" 2)
   :empty []})

(def ^:private plan
  [[:all-pixels :color :replace]
   [:every-other-pixel :white :replace]
   [:reversed-pixels :color :max]
   [:repeated :red :replace]
   [:whole-rig :dimmer :replace]
   [:pars-and-movers :color :max]
   [:white-heads :white :max]
   [:movers :pan :replace]
   [:empty :dimmer :replace]])

(defn- frame-batches [frame]
  (let [rng (java.util.Random. (long frame))]
    (mapv (fn [[target attribute blend]]
            (let [ids (get targets target)
                  width (if (= :color attribute) 3 1)
                  values (double-array (* width (count ids)))]
              (dotimes [i (alength values)] (aset values i (.nextDouble rng)))
              {:target-ids ids :blend blend
               :outputs {attribute {:type (if (= 3 width) :vec3 :number) :components width :values values}}}))
          plan)))

(defn- assignments [batches]
  (vec (for [{:keys [target-ids outputs blend] :or {blend :replace}} batches
             [attribute {:keys [components values]}] outputs
             [row id] (map-indexed vector target-ids)]
         {:target-id id :attribute attribute :blend blend
          :value (if (= 3 components)
                   (mapv #(aget ^doubles values (+ (* 3 row) %)) (range 3))
                   (aget ^doubles values row))})))

(defn- bytes-of [result] (into (sorted-map) (update-vals (:universes result) vec)))

(defn- outcome [f]
  (try {:bytes (bytes-of (f))}
       (catch clojure.lang.ExceptionInfo error
         {:message (.getMessage error) :data (ex-data error)})))

(def ^:private option-sets [{} {:include-values? false} {:include-values? false :compact-values? true}])

(deftest mixed-rig-batches-pack-like-scalar-assignments-warm-and-cold
  (let [rig (mixed-rig)
        patch (frame/compile-patch rig)]
    (doseq [frame (range 6) options option-sets]
      (let [batches (frame-batches frame)
            expected (bytes-of (frame/resolve-frame (frame/compile-patch rig) (assignments batches) options))]
        (testing (str "frame " frame " " options)
          (is (= expected (bytes-of (frame/resolve-batches patch batches options))) "warm patch")
          (is (= expected (bytes-of (frame/resolve-batches (frame/compile-patch rig) batches options))) "cold patch")
          (is (= expected (bytes-of (frame/resolve-batches patch batches (assoc options :hdr {:white-mix 1.0}))))
              "a per-frame HDR patch keeps the target plans"))))))

(defn- one [target attribute & [n]]
  (let [ids (if (keyword? target) (get targets target) target)
        width (if (= :color attribute) 3 1)]
    {:target-ids ids
     :outputs {attribute {:type (if (= 3 width) :vec3 :number) :components width
                          :values (double-array (* width (or n (count ids))) 0.5)}}}))

(def ^:private failures
  ;; [description batch expected-message expected-data]
  [["colour reaches a dimmer-only fixture"
    (one [:p0 :p1 :d1 :d2] :color) "Fixture does not implement batch attribute" {:target-id :d1 :attribute :color}]
   ["white reaches a par without white"
    (one [:m0 :r1 :p2] :white) "Fixture does not implement batch attribute" {:target-id :r1 :attribute :white}]
   ["an attribute no fixture has fails on the first row"
    (one :all-pixels :focus) "Fixture does not implement batch attribute" {:target-id :p0 :attribute :focus}]
   ["pan on a subset that includes pixels"
    (one :whole-rig :pan) "Fixture does not implement batch attribute" {:target-id :p0 :attribute :pan}]
   ["an unknown target after an ordered prefix"
    (one [:p0 :p1 :zz :p3] :red) "Unknown batch target" {:target-id :zz}]
   ["an unknown target in a reordered subset"
    (one [:m1 :nope] :dimmer) "Unknown batch target" {:target-id :nope}]
   ["shape errors are reported before support errors"
    (assoc (one [:d0] :color) :count 2) "Invalid batch shape, count or blend" {}]
   ["a support error in an earlier sorted column precedes a later field error"
    (assoc-in (one [:p0 :d0] :color) [:outputs :red] {:type :number :components 1 :values (double-array 1)})
    "Fixture does not implement batch attribute" {:target-id :d0 :attribute :color}]
   ["a field error in an earlier sorted column precedes a later support error"
    (assoc-in (one [:p0 :d0] :white) [:outputs :red] {:type :number :components 1 :values (double-array 1)})
    "Invalid typed batch output field" {:attribute :red}]])

(deftest invalid-batches-fail-with-the-same-message-and-data-warm-and-cold
  (let [rig (mixed-rig)
        patch (frame/compile-patch rig)]
    (doseq [[description batch message data] failures]
      (testing description
        (let [expected {:message message :data (assoc data :type ::frame/invalid-frame)}]
          (dotimes [_ 3]
            (is (= expected (outcome #(frame/resolve-batches patch [batch] {:include-values? false}))))
            (is (= expected (outcome #(frame/resolve-batches patch [batch])))))
          (is (= expected (outcome #(frame/resolve-batches (frame/compile-patch rig) [batch] {:include-values? false})))))))))

(deftest a-target-vector-accepted-for-one-attribute-still-rejects-another
  (let [patch (frame/compile-patch (mixed-rig))
        ids (get targets :pars-and-movers)]
    (is (contains? (outcome #(frame/resolve-batches patch [(one ids :color)])) :bytes))
    (is (= {:message "Fixture does not implement batch attribute"
            :data {:target-id :r0 :attribute :white :type ::frame/invalid-frame}}
           (outcome #(frame/resolve-batches patch [(one ids :white)]))))
    (is (contains? (outcome #(frame/resolve-batches patch [(one ids :dimmer)])) :bytes))))

(deftest a-rig-change-rechecks-the-same-target-vector
  (let [rig (mixed-rig)
        ids (get targets :white-heads)
        batch (one ids :white)
        before (frame/compile-patch rig)
        ;; The same IDs, but :m0 lost its white emitter and the rig is reordered.
        changed (place (vec (reverse (mapv #(if (= :m0 (:id %)) (update % :channels dissoc :white) %) rig))))
        after (frame/compile-patch changed)
        reordered (frame/compile-patch (place (vec (reverse rig))))]
    (is (contains? (outcome #(frame/resolve-batches before [batch] {:include-values? false})) :bytes))
    (is (= {:message "Fixture does not implement batch attribute"
            :data {:target-id :m0 :attribute :white :type ::frame/invalid-frame}}
           (outcome #(frame/resolve-batches after [batch] {:include-values? false}))))
    (testing "a reordered rig maps the same target vector to its new rows"
      (doseq [frame (range 3) options option-sets]
        (let [batches (frame-batches frame)]
          (is (= (bytes-of (frame/resolve-frame reordered (assignments batches) options))
                 (bytes-of (frame/resolve-batches reordered batches options))))
          (is (= (bytes-of (frame/resolve-frame before (assignments batches) options))
                 (bytes-of (frame/resolve-batches before batches options)))))))
    (testing "a patch whose fixtures were replaced by assoc does not reuse stale plans"
      (let [stale (assoc before :by-id (:by-id after))]
        (is (= {:message "Fixture does not implement batch attribute"
                :data {:target-id :m0 :attribute :white :type ::frame/invalid-frame}}
               (outcome #(frame/resolve-batches stale [batch] {:include-values? false}))))))))

(deftest many-distinct-target-vectors-stay-correct
  (let [rig (mixed-rig)
        patch (frame/compile-patch rig)
        pixels (ids "p" 12)
        ;; Far more fresh vectors than any bounded memo holds, each used twice.
        subsets (vec (for [i (range 2000)] (vec (take (inc (mod i 12)) (drop (mod i 5) (cycle pixels))))))]
    (doseq [round (range 2) [i ids] (map-indexed vector subsets)]
      (let [batch (one ids :color)
            expected (bytes-of (frame/resolve-frame patch (assignments [batch]) {:include-values? false}))]
        (when-not (= expected (bytes-of (frame/resolve-batches patch [batch] {:include-values? false})))
          (is false (str "round " round " subset " i)))))
    (is (= {:message "Fixture does not implement batch attribute"
            :data {:target-id :d0 :attribute :color :type ::frame/invalid-frame}}
           (outcome #(frame/resolve-batches patch [(one (conj (nth subsets 7) :d0) :color)]))))))

(deftest concurrent-workers-share-one-patch-without-changing-results
  (let [rig (mixed-rig)
        patch (frame/compile-patch rig)
        work (vec (for [frame (range 24)]
                    (let [batches (frame-batches frame)
                          bad (nth failures (mod frame (count failures)))]
                      {:batches batches
                       :expected (bytes-of (frame/resolve-frame patch (assignments batches) {:include-values? false}))
                       :bad (second bad)
                       :bad-expected {:message (nth bad 2) :data (assoc (nth bad 3) :type ::frame/invalid-frame)}})))
        pool (Executors/newFixedThreadPool 4)]
    (try
      (let [tasks (for [round (range 8) {:keys [batches expected bad bad-expected]} work]
                    (reify Callable
                      (call [_]
                        [(= expected (bytes-of (frame/resolve-batches patch batches {:include-values? false})))
                         (= bad-expected (outcome #(frame/resolve-batches patch [bad] {:include-values? false})))])))
            results (mapv #(.get ^java.util.concurrent.Future %) (.invokeAll pool (vec tasks)))]
        (is (= (count results) (* 8 (count work))))
        (is (every? #(= [true true] %) results)))
      (finally (.shutdownNow pool) (.awaitTermination pool 5 TimeUnit/SECONDS)))))

(defn- memo-entries [patch] (#'frame/memoized-target-plans patch))

(deftest a-compiled-patch-reuses-one-plan-per-target-vector
  (let [patch (frame/compile-patch (mixed-rig))]
    (dotimes [frame 5]
      (frame/resolve-batches patch (frame-batches frame) {:include-values? false}))
    (is (= (count targets) (memo-entries patch)) "one entry per target vector, not per frame")
    (is (zero? (memo-entries (frame/compile-patch (mixed-rig)))) "a recompiled patch starts empty")))

(deftest a-vector-aliasing-a-mutated-array-is-rechecked
  ;; clojure.core/vec adopts an Object[] of 32 or fewer elements, so the same
  ;; vector instance can change contents when the array is written.
  (let [patch (frame/compile-patch (mixed-rig))
        cold #(outcome (fn [] (frame/resolve-batches (frame/compile-patch (mixed-rig)) [%] {:include-values? false})))
        warm #(outcome (fn [] (frame/resolve-batches patch [%] {:include-values? false})))]
    (testing "a row now naming a fixture without the attribute"
      (let [array (object-array [:p1 :p0])
            ids (vec array)
            batch (one ids :red)]
        (is (contains? (warm batch) :bytes))
        (aset array 1 :d0)
        (is (= [:p1 :d0] ids) "the vector aliases the array")
        (is (= {:message "Fixture does not implement batch attribute"
                :data {:target-id :d0 :attribute :red :type ::frame/invalid-frame}}
               (cold batch) (warm batch)))))
    (testing "rows that now map to other fixtures"
      (let [array (object-array [:p2 :p3 :m0])
            ids (vec array)
            batch (one ids :white)
            bytes #(bytes-of (frame/resolve-frame patch (assignments [batch]) {:include-values? false}))]
        (is (= (bytes) (:bytes (warm batch))))
        (aset array 0 :m1) (aset array 2 :p5)
        (is (= (bytes) (:bytes (warm batch)) (:bytes (cold batch))))))
    (testing "an unknown ID written into a cached prefix vector"
      (let [array (object-array [:p0 :p1 :p2])
            ids (vec array)
            batch (one ids :red)]
        (is (contains? (warm batch) :bytes))
        (aset array 1 :gone)
        (is (= {:message "Unknown batch target" :data {:target-id :gone :type ::frame/invalid-frame}}
               (cold batch) (warm batch)))))))

(deftest only-persistent-vectors-are-memoized-and-the-memo-stays-bounded
  (let [patch (frame/compile-patch (mixed-rig))
        pixels (ids "p" 12)]
    (frame/resolve-batches patch [(one (subvec pixels 2 7) :red)] {:include-values? false})
    (frame/resolve-batches patch [(one (into (vector-of :long) []) :red 0)] {:include-values? false})
    (is (zero? (memo-entries patch)) "subvectors and primitive vectors bypass the memo")
    (let [held (vec (for [i (range 1000)] (vec (take (inc (mod i 12)) (drop (mod i 5) (cycle pixels))))))]
      (doseq [ids held] (frame/resolve-batches patch [(one ids :red)] {:include-values? false}))
      (is (<= (memo-entries patch) 128))
      (is (pos? (memo-entries patch))))
    (testing "the patch prints its memo as one short token"
      (is (re-find #"TargetPlans\[128 slots\]" (pr-str patch)))
      (is (not (re-find #"null, null" (pr-str patch)))))))
