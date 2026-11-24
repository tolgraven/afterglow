(ns afterglow.render.compute
  "Frame-owned expression evaluation followed by calibrated fixture rendering.
  Native stages are independent opt-ins. The reference path is float64 on CPU."
  (:require [afterglow.render.fields :as fields]
            [afterglow.render.distributed :as distributed]
            [afterglow.render.chain :as chain]
            [afterglow.render.frame :as frame]
            [afterglow.render.gpu.movement :as movement]
            [afterglow.render.hdr :as hdr]
            [afterglow.render.ir :as ir]
            [afterglow.runtime.faults :as faults])
  (:import [java.util.concurrent CancellationException ExecutionException Future TimeUnit TimeoutException]))

;; Loading the CPU renderer must work with only its normal dependencies.
(def ^:private native
  (delay {:open! (requiring-resolve 'afterglow.render.gpu.session/open!)
          :submit! (requiring-resolve 'afterglow.render.gpu.session/submit!)
          :status (requiring-resolve 'afterglow.render.gpu.session/status)
          :close! (requiring-resolve 'afterglow.render.gpu.session/close!)
          :group (requiring-resolve 'afterglow.render.gpu.session/group)}))

(defn- failure [^Throwable error]
  (when-not (faults/recoverable? error) (throw error))
  {:type (or (:type (ex-data error)) (.getSimpleName (class error)))
   :message (.getMessage error)})

(defn- open-expressions! [options budget]
  (let [state (atom {:requested :native-gpu :active :cpu :gpu-budget-ms budget
                     :native-dispatches 0 :cpu-fallbacks 0 :deadline-fallbacks 0})]
    (try (let [session ((:open! @native) options)]
           (swap! state assoc :active :native-gpu)
           {:session session :state state})
         (catch Throwable error
           (swap! state assoc :last-fallback (assoc (failure error) :stage :open))
           {:state state}))))

(defn open!
  "Own the resources for one renderer. :compute-backend selects expression
  evaluation and :movement-backend selects calibrated movement. Each defaults
  to :cpu and accepts :native-gpu. :budget-ms (default 25) bounds combined GPU
  time per frame. :gpu-options controls :timeout-ms, :max-programs and
  :queue-capacity. CPU-only operation acquires no worker or graphics context."
  ([] (open! {}))
  ([{:keys [compute-backend movement-backend budget-ms gpu-options]
     :or {compute-backend :cpu movement-backend :cpu budget-ms 25 gpu-options {}}}]
   (doseq [[key backend allowed] [[:compute-backend compute-backend #{:cpu :native-gpu :distributed}]
                                  [:movement-backend movement-backend #{:cpu :native-gpu}]]]
     (when-not (allowed backend)
       (throw (ex-info "Unknown render backend" {key backend}))))
   (when (or (not= :cpu compute-backend) (= :native-gpu movement-backend))
     (when-not (and (integer? budget-ms)
                    (<= 1 budget-ms (if (= :native-gpu movement-backend) 10000 Integer/MAX_VALUE)))
       (throw (ex-info "Invalid GPU time budget for the selected backend" {:budget-ms budget-ms})))
     (when-not (and (map? gpu-options)
                    (every? #{:max-programs :queue-capacity :timeout-ms} (keys gpu-options))
                    (every? pos-int? (vals gpu-options))
                    (<= (:queue-capacity gpu-options 4) Integer/MAX_VALUE)
                    (<= (:timeout-ms gpu-options 1000) 10000))
       (throw (ex-info "Invalid native queue, program capacity or fence timeout" {:gpu-options gpu-options})))
     (let [mover (when (= :native-gpu movement-backend)
                   (movement/open! {:budget-ms budget-ms :timeout-ms (:timeout-ms gpu-options 1000)}))]
       (try
         (merge {:budget-ns (* 1000000 budget-ms) :movement mover :chains (chain/create-cache)}
                (when (= :distributed compute-backend)
                  {:pool (distributed/create)
                   :state (atom {:requested :distributed :active :distributed :gpu-budget-ms budget-ms
                                 :native-dispatches 0 :cpu-fallbacks 0 :deadline-fallbacks 0})})
                (when (= :native-gpu compute-backend) (open-expressions! gpu-options budget-ms)))
         (catch Throwable error
           (when mover
             (try (movement/close! mover) (catch Throwable cleanup (.addSuppressed error cleanup))))
           (throw error)))))))

(defn expressions-enabled?
  "Whether a compiler can select native expression groups for this owner."
  [owner]
  (contains? #{:native-gpu :distributed} (:active (some-> owner :state deref))))

(defn status
  "Current expression backend, native session metrics and fallback counters."
  [owner]
  (if-let [state (:state owner)]
    (cond-> @state (:pool owner) (assoc :pool (distributed/status (:pool owner)))
            (:session owner) (assoc :session ((:status @native) (:session owner))))
    {:requested :cpu :active :cpu}))

(defn movement-status
  "Movement backend for a completed render output, or :idle before the first frame."
  [owner output]
  (if (:movement owner)
    (merge {:requested :native-gpu :backend :idle} (:movement output))
    {:requested :cpu :backend :cpu}))

(defn close!
  "Release the owned workers and graphics contexts after active draws finish."
  [owner]
  (try (when-let [pool (:pool owner)] (distributed/close! pool))
       (when-let [session (:session owner)] ((:close! @native) session))
       (finally
         (when-let [state (:state owner)] (swap! state assoc :active :stopped))
         (when-let [mover (:movement owner)] (movement/close! mover)))))

(defn prepare-group
  "Prepare named expression definitions and a matching ir/compile-batch plan.
  Capture ordered xyz positions and optional surface UVs at their original
  precision for CPU fallback."
  ([expressions positions cpu-plan] (prepare-group expressions positions cpu-plan nil))
  ([expressions positions cpu-plan surface-uvs]
   (let [positions (if (instance? double/1 positions) (aclone ^doubles positions) positions)
         uvs (when (:surface-uv? cpu-plan)
               (if (instance? double/1 surface-uvs) (aclone ^doubles surface-uvs) surface-uvs))]
     (merge {:expressions expressions :cpu-plan cpu-plan :positions positions :surface-uvs uvs}
            (try {:shader ((:group @native) expressions positions uvs)}
                 (catch Throwable error {:preparation-error (failure error)}))))))

(defn group-preparer [owner]
  (if (:pool owner) distributed/prepare-group prepare-group))

(defn- cpu-result! [owner {:keys [cpu-plan positions surface-uvs]} env detail]
  (when-let [state (:state owner)]
    (swap! state (fn [s] (cond-> (update s :cpu-fallbacks inc)
                           detail (assoc :last-fallback detail)
                           (= :deadline (:stage detail)) (update :deadline-fallbacks inc)))))
  (ir/evaluate-batch cpu-plan env positions surface-uvs))

(def ^:private late {:stage :deadline :type :budget-exhausted :message "GPU result exceeded this frame's deadline"})

(defn- draw! [session shader env deadline]
  (let [^Future job ((:submit! @native) session shader env :fixture-frame)]
    (try
      (let [batch (.get job (max 0 (- deadline (System/nanoTime))) TimeUnit/NANOSECONDS)]
        (if (< (System/nanoTime) deadline) {:batch batch} {:error late}))
      (catch TimeoutException _ (.cancel job false) {:error late})
      (catch CancellationException _ {:error {:stage :evaluate :type :cancelled :message "GPU job was cancelled"}})
      (catch ExecutionException error (throw (.getCause error)))
      (catch InterruptedException error
        (.cancel job false)
        (.interrupt (Thread/currentThread))
        (throw error)))))

(defn- evaluate! [owner deadline {:keys [shader preparation-error] :as group} env]
  (cond
    (not (expressions-enabled? owner)) (cpu-result! owner group env nil)
    preparation-error (cpu-result! owner group env (assoc preparation-error :stage :prepare))
    (>= (System/nanoTime) deadline) (cpu-result! owner group env late)
    (:pool owner)
    (let [attempt (try {:batch (distributed/evaluate! (:pool owner) group env deadline)}
                       (catch Exception error {:error (failure error)}))]
      (or (:batch attempt) (cpu-result! owner group env (:error attempt))))
    :else
    (let [session (:session owner)
          result (try (draw! session shader env deadline)
                      (catch Throwable error {:error (assoc (failure error) :stage :evaluate)}))]
      (if-let [batch (:batch result)]
        (do (swap! (:state owner) update :native-dispatches inc) batch)
        (do (when (:closed? ((:status @native) session))
              (swap! (:state owner) update :active #(if (= :native-gpu %) :cpu %)))
            (cpu-result! owner group env (:error result)))))))

(defn frame-renderer
  "Create a single frame's function [compiled-patch ordered-blocks render-options].
  Supply frame-start-ns from System/nanoTime. Healthy deferred fields can reuse
  their detached arrays across fault-isolation retries of this frame. All draws
  and retries share its absolute budget. Render options include the last
  accepted rich/compact movement history. No device output is published here."
  [owner frame-start-ns]
  (let [deadline (when owner (+ frame-start-ns (:budget-ns owner)))
        evaluate-fields (fields/frame-evaluator (partial evaluate! owner deadline))
        mover (:movement owner)]
    (fn render [patch blocks options]
      (let [resolve! (fn [blocks]
                       (let [contributions (evaluate-fields blocks)]
                         (if mover
                           (movement/resolve-contributions! mover patch contributions (assoc options :deadline-nanos deadline))
                           (frame/resolve-contributions patch contributions options))))
            ;; Contribution gains use each original source and that owner's dimmers.
            fused (if (and (expressions-enabled? owner)
                           (not (hdr/contribution-gains? blocks (:hdr options))))
                    (chain/fuse (:chains owner) (group-preparer owner) blocks)
                    blocks)]
        (if (identical? fused blocks) (resolve! blocks)
          (try (resolve! fused)
               ;; Original requests attribute faults to individual running cues.
               (catch Exception _ (resolve! blocks))))))))
