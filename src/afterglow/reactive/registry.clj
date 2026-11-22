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

(defn source-description
  "Capture names needed to compile a literal function after its REPL session
  closes. Namespace aliases, refers and imported classes are names only. Local
  def values must be supplied through the registration's explicit bindings."
  [host form]
  (cond-> {:type :source :namespace (str (ns-name host)) :form (pr-str form)}
    (::temporary (meta host))
    (assoc :environment
           (let [symbols (filter symbol? (tree-seq coll? seq form))
                 names (into #{} (mapcat (fn [s] [(str s) (namespace s) (str/replace (name s) #"\.$" "")])) symbols)
                 used (fn [table describe]
                        (into {} (keep (fn [[k v]] (when (names (str k)) [(str k) (describe v)]))) table))]
             {:requires (->> symbols (keep namespace) distinct sort
                             (filterv #(and (not= % (str (ns-name host))) (find-ns (symbol %)))))
              :aliases (used (ns-aliases host) #(str (ns-name %)))
              :refers (used (remove (fn [[_ v]] (= 'clojure.core (ns-name (:ns (meta v))))) (ns-refers host))
                            #(str (symbol %)))
              :imports (used (ns-imports host) #(.getName ^Class %))}))))

(defn- valid-environment? [environment]
  (and (map? environment)
       (every? #{:aliases :refers :imports :requires} (keys environment))
       (or (nil? (:requires environment))
           (and (vector? (:requires environment)) (every? string? (:requires environment))))
       (every? (fn [table] (and (map? table) (every? string? (keys table)) (every? string? (vals table))))
               (vals (dissoc environment :requires)))))

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
                               (or (not (contains? implementation :environment)) (valid-environment? (:environment implementation)))
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

(defn- compile-temporary [environment compile!]
  ;; Reconstitute only compiler names. Each handler gets a fresh namespace,
  ;; including during parallel restores. It never owns session vars or jobs.
  (let [name (gensym "afterglow.reactive.restored__")
        target (create-ns name)]
    (try
      (binding [*ns* target]
        (refer 'clojure.core)
        (doseq [library (:requires environment)] (require (symbol library)))
        (doseq [[local library] (:aliases environment)]
          (require (symbol library)) (alias (symbol local) (symbol library)))
        (doseq [[local qualified] (:refers environment)]
          (let [v (requiring-resolve (symbol qualified))]
            (.refer target (symbol local) v)))
        (doseq [[_ class-name] (:imports environment)]
          (.importClass target (Class/forName class-name false (clojure.lang.RT/baseLoader))))
        (compile!))
      (finally (remove-ns name)))))

(defn- compile-source [{:keys [namespace form bindings environment]}]
  (let [library (symbol namespace)
        local-bindings (mapcat (fn [[k v]] [(symbol k) (list 'quote v)]) (sort-by key bindings))
        compile! #(eval (list 'let (vec local-bindings) (read-function form)))]
    (cond
      environment (compile-temporary environment compile!)
      (find-ns library) (binding [*ns* (find-ns library)] (compile!))
      ;; Older files record a generated session UUID without a namespace
      ;; environment. Literal functions using core and captured values still load.
      (re-find #"(?:_|-)[0-9a-f]{8}(?:[_-][0-9a-f]{4}){3}[_-][0-9a-f]{12}$" namespace)
      (compile-temporary {} compile!)
      :else (do (require library) (binding [*ns* (the-ns library)] (compile!))))))

(defn resolve-handler
  "Resolve a var or compile trusted REPL source. Never call implicitly on an
  arbitrary imported document. The function body is not run during compilation."
  [definition {:keys [trusted-source? allowed-vars]}]
  (validate-definition definition)
  (let [{:keys [type symbol namespace form bindings]} (:implementation definition)
        handler (case type
                  :var (let [name (clojure.core/symbol symbol)
                             _ (when-not (or (true? trusted-source?) (contains? allowed-vars name))
                                 (throw (ex-info "Restoring an unregistered reactive var requires explicit trust"
                                                 {:type ::untrusted-var :id (:id definition) :symbol symbol})))
                             v (requiring-resolve name)]
                         (when-not (var? v) (invalid! "Reactive var could not be resolved" {:symbol symbol}))
                         @v)
                  :source
                  (do
                    (when-not (true? trusted-source?)
                      (throw (ex-info "Restoring reactive source requires explicit trust" {:type ::untrusted-source :id (:id definition)})))
                    (compile-source (:implementation definition))))]
    (when-not (fn? handler) (invalid! "Reactive implementation did not resolve to a function" {:id (:id definition)}))
    handler))
