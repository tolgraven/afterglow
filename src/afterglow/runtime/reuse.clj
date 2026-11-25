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

(defn- charge! [^longs remaining n]
  (when (neg? (aset-long remaining 0 (- (aget remaining 0) (long n))))
    (throw uncacheable)))

(defn- snapshot
  "Admit plain persistent data. Detach private primitive arrays in outputs.
  Return original persistent subtrees when every member is immutable."
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
    (let [n (Array/getLength x)]
      (charge! remaining n)
      (let [copy (Array/newInstance (.getComponentType ^Class (class x)) n)]
        (System/arraycopy x 0 copy 0 n)
        copy))
    :else (throw uncacheable)))

(defn- capture [value limit arrays?]
  (try (snapshot value (long-array [(long limit)]) arrays? 0)
       (catch clojure.lang.ExceptionInfo error
         (if (identical? error uncacheable) missing (throw error)))))

(defn immutable-inputs?
  "Whether a value fits the bounded immutable input contract used by reuse."
  [value]
  (not (identical? missing (capture value 65536 false))))

(defn retained-output
  "Admit bounded effect output data and detach its primitive arrays."
  [value]
  (let [saved (capture value 65536 true)]
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

  Each binding holds at most one successful value. :max-values bounds both
  input and output capture (default 65536 nodes and primitive elements).
  Uncacheable values still evaluate. Primitive output buffers are private to
  the caller on every invocation. Inputs use Java value equality so signed
  zero and numeric representation remain observable. Concurrent misses may
  evaluate independently; no callback runs inside a lock or CAS retry."
  [{:keys [pure? inputs max-values] :or {pure? false max-values 65536} :as declaration} calculate]
  (when-not (and (fn? calculate) (boolean? pure?)
                 (vector? inputs) (every? #(and (vector? %) (seq %) (every? keyword? %)) inputs)
                 (pos-int? max-values))
    (throw (ex-info "Expected a calculation, boolean purity and a vector of keyword paths" {})))
  (let [entry (AtomicReference.)]
    (with-meta
      (fn [context]
        (let [inputs (inputs-for inputs context)
              key (when pure? (capture inputs max-values false))]
          (if (or (not pure?) (identical? key missing))
            (calculate inputs)
            (let [prior (.get entry)]
              (if (and prior (.equals ^Object key (:key prior)))
                (if (:copy? prior) (capture (:value prior) max-values true) (:value prior))
                (let [result (calculate inputs)
                      value (capture result max-values true)]
                  (when-not (identical? value missing)
                    (.compareAndSet entry prior
                                    {:key key :value value :copy? (not (identical? result value))}))
                  result))))))
      {::declaration declaration})))

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
