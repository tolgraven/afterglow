(ns afterglow.runtime
  "Pure effect evaluation kernel for the new control model and show engine.

  Effects return ordered ordinary or typed contributions. The engine coordinates
  their lifecycle and the render backend resolves fixture output. Old show/effect
  protocols are not executed here.

  Effects are pure functions of a supplied frame snapshot and their own state.
  They describe assignments and external work as data; the owner of the show
  performs that work only after accepting a complete frame. Callers supply time,
  randomness and any parallel executor explicitly.")

(defn- invalid!
  [message data]
  (throw (ex-info message data)))

(defn- finite-number?
  [value]
  (and (number? value) (Double/isFinite (double value))))

(defn- result-shape?
  [result]
  (and (map? result) (contains? result :state)
       (vector? (:assignments result))
       (or (not (contains? result :contributions)) (vector? (:contributions result)))
       (vector? (:intents result))
       (instance? Boolean (:done? result))))

(defn- validate-contributions! [blocks]
  (when-not (and (vector? blocks)
                 (every? (fn [block]
                           (and (map? block)
                                (case (:kind block)
                                  :assignments (vector? (:assignments block))
                                  :batch (map? (:batch block))
                                  false))) blocks))
    (invalid! "Contributions must be ordered assignment or typed batch blocks"
              {:type ::invalid-contributions})))

(defn append-contributions
  "Append ordered contribution blocks to an effect context, flushing assignments.

  Blocks are {:kind :assignments :assignments [...]} or {:kind :batch :batch ...}.
  Ordinary middleware may continue appending to :assignments; those values form
  the tail after the blocks. Call this helper whenever adding blocks so earlier
  ordinary contributions keep their exact order. Typed arrays must be privately
  owned until returned and read-only thereafter. This helper performs no IO."
  [context blocks]
  (when-not (vector? (:assignments context))
    (invalid! "Effect context requires vector assignments" {:type ::invalid-result}))
  (validate-contributions! blocks)
  (let [existing (:contributions context [])]
    (validate-contributions! existing)
    (assoc context :assignments []
           :contributions (into (cond-> existing
                                  (seq (:assignments context))
                                  (conj {:kind :assignments :assignments (:assignments context)})) blocks))))

(defn- validate-context
  [context]
  (when-not (and (map? context) (map? (:frame context))
                 (vector? (:effects context)))
    (invalid! "Expected a context with a :frame map and an :effects vector"
              {:type ::invalid-context}))
  (doseq [instance (:effects context)]
    (when-not (and (map? instance)
                   (some? (:id instance))
                   (finite-number? (:priority instance))
                   (integer? (:order instance))
                   (not (neg? (:order instance)))
                   (contains? instance :state)
                   (ifn? (:step instance)))
      (invalid! "Expected an effect instance with :id, finite :priority, nonnegative integer :order, :state and callable :step"
                {:type ::invalid-instance :effect-id (:id instance)})))
  (let [ids (mapv :id (:effects context))]
    (when-not (= (count ids) (count (set ids)))
      (invalid! "Effect instance ids must be unique"
                {:type ::duplicate-effect-id})))
  context)

(defn evaluate-instance
  "Evaluate one descriptor with strict result validation. The show coordinator
  owns per-instance failure policy; executor and model failures remain distinct."
  [frame instance]
  (let [id (:id instance)
        input {:frame frame :effect-id id
               :instance (or (:instance instance) (dissoc instance :step))
               :state (:state instance)
               :assignments [] :contributions [] :intents [] :done? false}
        result (try
                 ((:step instance) input)
                 (catch Exception cause
                   (throw (ex-info "Effect step failed"
                                   {:type ::step-failed :effect-id id} cause))))]
    (when-not (result-shape? result)
      (invalid! "Effect step must return :state, vector :assignments, vector :intents and boolean :done?"
                {:type ::invalid-result :effect-id id}))
    ;; Identity comes from the instance, never from the effect's return value.
    (cond-> {:id id :state (:state result) :assignments (:assignments result)
             :contributions (:contributions (append-contributions result []))
             :intents (:intents result) :done? (:done? result)}
      (::observe (meta result)) (vary-meta assoc ::observe (::observe (meta result))))))

(defn observable-instance
  "Keep a completed step's optional, pure query function outside portable show data."
  [{:keys [instance state] :as evaluation}]
  (let [next (assoc instance :state state)]
    (cond (::observe (meta evaluation)) (vary-meta next assoc ::observe (::observe (meta evaluation)))
          (::observe (meta next)) (vary-meta next dissoc ::observe)
          :else next)))

(defn observe
  "Inspect a committed step on demand. Absent and faulted instances have no observation."
  [instance query]
  (when-let [read-query (::observe (meta instance))]
    (read-query query)))

(defn- index-results
  [instances results]
  (let [expected (set (map :id instances))
        indexed (reduce
                 (fn [acc result]
                   (let [id (:id result)]
                     (when-not (and (result-shape? result) (contains? expected id)
                                    (not (contains? acc id)))
                       (invalid! "Executor must return each evaluation exactly once"
                                 {:type ::invalid-executor-result :effect-id id}))
                     (assoc acc id result)))
                 {} results)]
    (when-not (= expected (set (keys indexed)))
      (invalid! "Executor omitted effect evaluations"
                {:type ::missing-executor-results
                 :missing-ids (vec (remove #(contains? indexed %) (map :id instances)))}))
    indexed))

(defn merge-results
  "Validate and deterministically merge already evaluated results. Used by the
  show coordinator to isolate effect faults without evaluating healthy work twice."
  [context evaluated]
  (validate-context context)
  (let [instances (:effects context)
        results (index-results instances evaluated)
        ordered (sort-by (fn [[position instance]]
                           [(:priority instance) (:order instance) position])
                         (map-indexed vector instances))
        contributions (map (fn [[_ instance]] (get results (:id instance))) ordered)
        blocks (into [] (mapcat :contributions) contributions)
        structured? (some #(or (:native-layer %) (= :batch (:kind %))) blocks)]
    (assoc context
           :effects (into [] (keep (fn [instance]
                                    (let [result (get results (:id instance))]
                                      (when-not (:done? result) (assoc instance :state (:state result)))))) instances)
           :contributions blocks
           :assignments (when-not structured? (into [] (mapcat :assignments) blocks))
           :intents (into [] (mapcat :intents) contributions))))

(defn render-frame
  "Evaluate independent effects and return the next immutable context.

  Context contains a :frame map (the immutable show/time/input snapshot) and an
  :effects vector. Each instance requires :id, numeric finite :priority,
  nonnegative integer :order (launch order), :state, and a pure :step function.

  A step takes a map with :frame, :effect-id, :instance, :state, :assignments [], :intents []
  and :done? false. It returns that map with updated :state, assignment/intent
  vectors, and a boolean :done?. Compose steps with ordinary functions such as
  comp or ->. Only :state, :assignments, :contributions, :intents and :done? are
  consumed; the frame and identity remain owned by the caller. :instance is the descriptor's explicit :instance
  data when present, otherwise the descriptor without its step function.
  Optional :contributions stores ordered assignment/batch blocks; use
  append-contributions to preserve order when composing with ordinary steps.
  All inputs/state/output data must be immutable or exclusively owned until
  return and read-only thereafter (typed numeric result buffers).
  The kernel validates shape, but cannot prove that arbitrary user functions
  are pure or that data contains no mutable Java objects.

  Optional map-work is a blocking mapping function of [f instances]. It must
  invoke f once per instance and return the unmodified results, in any order.
  Use it to inject a bounded executor; its lifecycle and cancellation belong to
  the caller. No global pool, atom, clock, randomness, IO or output publication
  is used here. The default mapv evaluates serially.

  Assignment and intent vectors are concatenated by ascending priority, then
  launch order, then original vector position. Per-effect vector order is kept.
  The returned :contributions stream preserves mixed block ordering. Aggregate
  :assignments remains a vector for ordinary-only results and is nil when typed
  batches are present, preventing accidental partial rendering by old consumers.
  Target blending/DMX packing is a later stage.
  A completed effect's final contributions are included, then it is removed.
  Remaining instances keep their original vector order with updated state.

  A failed step or incomplete/duplicate executor result throws before a new
  context is returned. The caller must commit/publicize only a successful return.
  This does not roll back side effects in a step that violates the pure contract."
  ([context]
   (render-frame context mapv))
  ([context map-work]
   (validate-context context)
   (when-not (ifn? map-work)
     (invalid! "Expected a callable map-work" {:type ::invalid-executor}))
   (merge-results context (map-work (partial evaluate-instance (:frame context)) (:effects context)))))
