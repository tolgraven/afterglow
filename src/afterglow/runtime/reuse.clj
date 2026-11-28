(ns afterglow.runtime.reuse
  "Show-owned reuse of calculations with explicitly injected data inputs."
  (:require [afterglow.runtime :as runtime])
  (:import [java.lang.reflect Array]
           [java.util.concurrent.atomic AtomicReference]))

(def ^:private missing (Object.))

(def ^:private uncacheable (ex-info "Value cannot be retained in an effect cache" {}))

(def ^:private scalar-classes
  #{Boolean Character Byte Short Integer Long Float Double java.math.BigInteger
    java.math.BigDecimal clojure.lang.BigInt clojure.lang.Ratio})

(def default-max-shared-bytes
  "Bytes of read-only primitive arrays one :shared-outputs? binding may retain:
  8 MiB, or 1,048,576 float64 elements. A group of 40,000 RGBW pixels returns
  160,000 (1.28 MB); the bound admits about 262,000 such pixels per group."
  (* 8 1024 1024))

(defn- charge!
  "Charge n nodes or copied elements (budget 0) or n bytes of arrays admitted
  by reference (budget 1)."
  ([^longs remaining n] (charge! remaining 0 n))
  ([^longs remaining budget n]
   (let [budget (int budget)]
     (when (neg? (aset-long remaining budget (- (aget remaining budget) (long n))))
       (throw uncacheable)))))

(defn- element-bytes ^long [^Class component]
  (condp identical? component
    Double/TYPE 8 Long/TYPE 8 Integer/TYPE 4 Float/TYPE 4
    Short/TYPE 2 Character/TYPE 2 Byte/TYPE 1 Boolean/TYPE 1))

(defn- snapshot
  "Admit plain persistent data. Detach private primitive arrays in outputs
  (arrays? true), or admit them by reference when the caller has declared them
  read-only (arrays? :shared). Return original persistent subtrees when every
  member is immutable or shared."
  [x ^longs remaining arrays? depth]
  (charge! remaining 1)
  (when (or (> depth 64) (meta x)) (throw uncacheable))
  (cond
    (and (float? x) (Double/isNaN (double x))) (throw uncacheable)
    (or (nil? x) (keyword? x) (symbol? x) (contains? scalar-classes (class x))) x
    (string? x) (do (charge! remaining (count x)) x)
    (or (vector? x) (and (map? x) (not (record? x))))
    (reduce-kv (fn [result k value]
                 (when (map? x)
                   (cond (string? k) (charge! remaining (count k))
                         (not (keyword? k)) (throw uncacheable)))
                 (let [v (snapshot value remaining arrays? (inc depth))]
                   (if (identical? value v) result (assoc result k v))))
               x x)
    (and arrays? (.isArray ^Class (class x))
         (.isPrimitive ^Class (.getComponentType ^Class (class x))))
    (let [n (Array/getLength x)
          component (.getComponentType ^Class (class x))]
      (if (= :shared arrays?)
        ;; Nothing is copied, so the array's bytes count against their own
        ;; bound rather than the node and copied-element budget.
        (do (charge! remaining 1 (* n (element-bytes component))) x)
        (let [copy (Array/newInstance component n)]
          (charge! remaining n)
          (System/arraycopy x 0 copy 0 n)
          copy)))
    :else (throw uncacheable)))

(defn- capture [value limit shared-bytes arrays?]
  (try (snapshot value (long-array [(long limit) (long shared-bytes)]) arrays? 0)
       (catch clojure.lang.ExceptionInfo error
         (if (identical? error uncacheable) missing (throw error)))))

(defn immutable-inputs?
  "Whether a value fits the bounded immutable input contract used by reuse."
  [value]
  (not (identical? missing (capture value 65536 0 false))))

(defn retained-output
  "Admit bounded effect output data and detach its primitive arrays."
  [value]
  (let [saved (capture value 65536 0 true)]
    (when-not (identical? missing saved) saved)))

(defn- inputs-for [paths context]
  (reduce (fn [inputs path]
            (let [v (get-in context path missing)]
              (if (identical? missing v) inputs (assoc-in inputs path v))))
          {} paths))

(defn evaluator
  "Bind a calculation to declared keyword paths. The function receives only a
  nested map of those inputs, with absent leaves omitted. :pure? true attests
  that inputs and immutable values captured at bind time fully determine it.
  Other functions run every time. Bind once per compiled plan and show.

  Each binding holds at most one successful value. :max-values bounds the
  input key and the output (default 65536 each), counting every node and
  every element of a copied primitive array. Uncacheable values still
  evaluate. By default primitive output buffers are private to the caller on
  every invocation: a miss retains a copy and a hit returns a new copy.
  :shared-outputs? true attests that the calculation returns fresh arrays and
  that the caller and every later reader treat them as read-only. The binding
  then retains the returned value itself and returns that same value on a
  hit, possibly to several workers at once; nothing is copied. A caller that
  must change a value writes a new array it owns. Arrays admitted this way
  count one node each against :max-values, and their elements count against
  :max-shared-bytes instead (default 8 MiB, 1,048,576 float64 elements, for
  pixel groups of 40,000 and more), so their length alone does not stop
  retention.

  Memory one binding can retain: its input key (at most :max-values nodes and
  copied elements) and one output. A private-copy output holds at most
  :max-values nodes and elements, 512 KiB of float64 at the default. A shared
  output holds at most :max-values nodes plus :max-shared-bytes of arrays.
  The binding keeps that value for as long as the binding itself is reachable,
  whether or not anything still calls it: a host that caches compiled programs
  retains one output per cached binding, not per running instance. Call
  `clear!` when a binding stops being used, for example when the last
  instance running its program releases. Inputs use Java value equality so signed zero and numeric representation
  remain observable. Concurrent misses may evaluate independently; no
  callback runs inside a lock or CAS retry."
  [{:keys [pure? inputs max-values shared-outputs? max-shared-bytes]
    :or {pure? false max-values 65536 shared-outputs? false
         max-shared-bytes default-max-shared-bytes} :as declaration} calculate]
  (when-not (and (fn? calculate) (boolean? pure?) (boolean? shared-outputs?)
                 (vector? inputs) (every? #(and (vector? %) (seq %) (every? keyword? %)) inputs)
                 (pos-int? max-values) (pos-int? max-shared-bytes))
    (throw (ex-info "Expected a calculation, boolean purity and a vector of keyword paths" {})))
  (let [entry (AtomicReference.)
        arrays (if shared-outputs? :shared true)
        shared-bytes (if shared-outputs? max-shared-bytes 0)]
    (with-meta
      (fn [context]
        (let [inputs (inputs-for inputs context)
              key (when pure? (capture inputs max-values 0 false))]
          (if (or (not pure?) (identical? key missing))
            (calculate inputs)
            (let [prior (.get entry)]
              (if (and prior (.equals ^Object key (:key prior)))
                (if (:copy? prior) (capture (:value prior) max-values shared-bytes arrays) (:value prior))
                (let [result (calculate inputs)
                      value (capture result max-values shared-bytes arrays)]
                  (when-not (identical? value missing)
                    (.compareAndSet entry prior
                                    {:key key :value value :copy? (not (identical? result value))}))
                  result))))))
      {::declaration declaration ::entry entry})))

(defn clear!
  "Drop the value a binding or `step` retains, so its arrays can be collected.
  The binding stays usable: its next call evaluates and may retain again. An
  evaluation already running when this is called stores its result only if
  nothing was retained when it started. Returns nil; other functions are
  ignored. Call it outside any CAS retry, at the owner that retires the
  binding's program."
  [binding]
  (when-let [^AtomicReference entry (::entry (meta binding))]
    (.set entry nil))
  nil)

(defn retains?
  "Whether a binding or `step` currently retains a value."
  [binding]
  (boolean (some-> ^AtomicReference (::entry (meta binding)) .get)))

(defn step
  "Build effect middleware from a declared-input calculation. It returns a map
  with optional :state, ordered :assignments, :contributions, :intents or
  :done?. Each invocation applies these to the current context. Returned
  intents retain normal per-frame delivery semantics on a cache hit."
  [declaration calculate]
  (let [run (evaluator declaration
                       (fn [inputs]
                         (let [out (calculate inputs)]
                           (when-not (and (map? out)
                                          (every? #{:state :assignments :contributions :intents :done?} (keys out))
                                          (every? #(vector? (get out % [])) [:assignments :contributions :intents])
                                          (boolean? (:done? out false)))
                             (throw (ex-info "Invalid effect result" {})))
                           (when (seq (:contributions out))
                             (runtime/append-contributions {:assignments []} (:contributions out)))
                           out)))]
    (with-meta
      (fn [context]
        (let [out (run context)]
          (cond-> context
            (seq (:contributions out)) (runtime/append-contributions (:contributions out))
            (seq (:assignments out)) (update :assignments into (:assignments out))
            (seq (:intents out)) (update :intents into (:intents out))
            (contains? out :state) (assoc :state (:state out))
            (:done? out) (assoc :done? true))))
      (meta run))))
