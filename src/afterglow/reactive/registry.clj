(ns afterglow.reactive.registry
  "Portable definitions for the explicitly owned JVM reactive boundary.
  Validation never evaluates code. Source restoration requires an explicit
  trust decision and is separate from loading fixture/show data."
  (:require [clojure.string :as str])
  (:import [java.io PushbackReader StringReader]))

(defn portable?
  "Values which round-trip as ordinary EDN without tagged readers or objects."
  [value]
  (cond
    (or (nil? value) (boolean? value) (string? value) (keyword? value) (char? value)) true
    (number? value) (if (or (float? value) (double? value)) (Double/isFinite (double value)) true)
    (and (map? value) (not (record? value))) (every? (fn [[k v]] (and (portable? k) (portable? v))) value)
    (or (vector? value) (list? value) (set? value)) (every? portable? value)
    :else false))

(defn- invalid! [message data] (throw (ex-info message (assoc data :type ::invalid-registry))))

(defn semantic-action? [action]
  (and (map? action) (or (keyword? (:op action)) (string? (:op action))) (portable? action)
       (not-any? #(contains? action %) [:epoch :command-id :source :time-ms])))

(defn read-function
  "Read exactly one literal function form, with reader evaluation disabled."
  [source]
  (when-not (and (string? source) (not (str/blank? source)))
    (invalid! "Reactive source must be a nonempty function string" {}))
  (try
    (with-open [reader (PushbackReader. (StringReader. source))]
      (binding [*read-eval* false *data-readers* {} *default-data-reader-fn* nil]
        (let [form (read {:eof ::eof} reader)]
          (when-not (and (seq? form) (#{'fn 'fn* 'clojure.core/fn} (first form))
                         (= ::eof (read {:eof ::eof} reader)))
            (invalid! "Reactive source must contain exactly one literal fn form" {}))
          form)))
    (catch clojure.lang.ExceptionInfo e (throw e))
    (catch Exception e (throw (ex-info "Cannot read reactive function source" {:type ::invalid-registry} e)))))

(defn validate-definition [definition]
  (when-not (and (map? definition) (keyword? (:id definition))
                 (#{:sub :fx} (:kind definition)))
    (invalid! "Reactive registrations need a keyword ID and :sub or :fx kind" {:definition definition}))
  (let [{:keys [type symbol namespace form bindings] :as implementation} (:implementation definition)]
    (when-not (map? implementation) (invalid! "Missing reactive implementation" {:id (:id definition)}))
    (case type
      :var (when-not (and (string? symbol) (re-matches #"[^\s/]+/[^\s/]+" symbol))
             (invalid! "A reactive var reference must be namespace/name" {:id (:id definition)}))
      :source (do
                (when-not (and (string? namespace) (re-matches #"[^\s/]+" namespace)
                               (map? bindings)
                               (every? (fn [[k v]] (and (string? k) (re-matches #"[A-Za-z_!?*+<>=$%-][A-Za-z0-9_!?*+<>=$%.\-]*" k)
                                                        (portable? v))) bindings))
                  (invalid! "Reactive source needs its namespace and explicit portable bindings" {:id (:id definition)}))
                (read-function form))
      (invalid! "Unknown reactive implementation type" {:id (:id definition) :implementation-type type})))
  (when-not (portable? definition) (invalid! "Reactive definition contains nonportable values" {:id (:id definition)}))
  definition)

(defn validate-registry [registry]
  (when-not (and (map? registry) (vector? (:registrations registry)))
    (invalid! "Reactive registry requires a registrations vector" {}))
  (doseq [definition (:registrations registry)] (validate-definition definition))
  (let [ids (map (juxt :kind :id) (:registrations registry))]
    (when-not (= (count ids) (count (distinct ids))) (invalid! "Duplicate reactive registration" {})))
  (when-let [state (:state registry)]
    (when-not (and (map? state) (map? (:cells state)) (not (contains? (:cells state) :db))
                   (every? keyword? (keys (:cells state))) (portable? (:cells state))
                   (vector? (:pending-actions state)) (every? semantic-action? (:pending-actions state))
                   (vector? (:watchers state)))
      (invalid! "Malformed reactive state" {}))
    (doseq [{:keys [id query effect-id initialized? value]} (:watchers state)]
      (when-not (and (keyword? id) (vector? query) (keyword? (first query)) (portable? query)
                     (keyword? effect-id) (boolean? initialized?) (portable? value))
        (invalid! "Malformed reactive watcher" {:id id}))
      (let [registrations (set (map (juxt :kind :id) (:registrations registry)))]
        (when-not (and (contains? registrations [:sub (first query)])
                       (contains? registrations [:fx effect-id]))
          (invalid! "Reactive watcher references a missing subscription or effect handler" {:id id}))))
    (let [ids (map :id (:watchers state))]
      (when-not (= (count ids) (count (distinct ids))) (invalid! "Duplicate reactive watcher" {}))))
  (when-not (portable? registry) (invalid! "Reactive registry contains nonportable values" {}))
  registry)

(defn resolve-handler
  "Resolve a var or compile trusted REPL source. Never call implicitly on an
  arbitrary imported document. The function body is not run during compilation."
  [definition {:keys [trusted-source?]}]
  (validate-definition definition)
  (let [{:keys [type symbol namespace form bindings]} (:implementation definition)
        handler (case type
                  :var (let [v (requiring-resolve (clojure.core/symbol symbol))]
                         (when-not (var? v) (invalid! "Reactive var could not be resolved" {:symbol symbol}))
                         @v)
                  :source
                  (do
                    (when-not trusted-source?
                      (throw (ex-info "Restoring reactive source requires explicit trust" {:type ::untrusted-source :id (:id definition)})))
                    (let [namespace-symbol (clojure.core/symbol namespace)
                          target (or (find-ns namespace-symbol)
                                     (do (require namespace-symbol) (find-ns namespace-symbol)))
                          locals (mapcat (fn [[k v]] [(clojure.core/symbol k) (list 'quote v)]) (sort-by key bindings))]
                      (binding [*ns* target]
                        (eval (list 'let (vec locals) (read-function form)))))))]
    (when-not (fn? handler) (invalid! "Reactive implementation did not resolve to a function" {:id (:id definition)}))
    handler))
