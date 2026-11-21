(ns afterglow.runtime.replay
  "Portable deterministic recordings of the new command/engine/render pipeline.

  No clock, RNG, pool, compiler cache, file or device is owned here. The caller
  supplies a pure compiler and optionally a worker mapper/renderer. Recordings
  capture already evaluated observations without evaluating effects a second
  time. Full typed output is projected only at this diagnostic boundary."
  (:require [afterglow.control.model :as control]
            [afterglow.runtime.engine :as engine]
            [afterglow.render.frame :as render])
  (:import [java.nio.charset StandardCharsets]
           [java.security MessageDigest]))

(defn- fail! [type message data]
  (throw (ex-info message (assoc data :type type))))

(defn- finite? [value]
  (and (number? value) (Double/isFinite (double value))))

(defn- portable
  "Copy plain EDN, dropping metadata and normalizing Float to readable Double."
  ([value] (portable value []))
  ([value path]
   (cond
     (or (nil? value) (boolean? value) (string? value) (char? value)
         (keyword? value) (symbol? value)) value
     (or (integer? value) (ratio? value) (decimal? value)) value
     (or (instance? Double value) (instance? Float value))
     (if (finite? value) (double value)
         (fail! ::nonportable "Recording numbers must be finite" {:path path}))
     (record? value) (fail! ::nonportable "Recording data cannot contain records" {:path path})
     (map? value) (into {} (map (fn [[k v]] [(portable k (conj path :key))
                                           (portable v (conj path k))])) value)
     (vector? value) (mapv #(portable %1 (conj path %2)) value (range))
     (set? value) (into #{} (map #(portable % (conj path :member))) value)
     (list? value) (apply list (map-indexed #(portable %2 (conj path %1)) value))
     :else (fail! ::nonportable "Recording needs plain EDN; mutable objects and functions are not portable"
                  {:path path :class (.getName (class value))}))))

(defn- printed [value]
  (binding [*print-length* nil *print-level* nil *print-meta* false
            *print-readably* true *print-dup* false *print-namespace-maps* false]
    (pr-str value)))

(defn- canonical [value]
  ;; Tag containers so a user vector cannot collide with a canonical map/set.
  (cond
    (map? value) [:map (->> value (map (fn [[k v]] [(canonical k) (canonical v)]))
                           (sort-by (comp printed first)) vec)]
    (set? value) [:set (->> value (map canonical) (sort-by printed) vec)]
    (vector? value) [:vector (mapv canonical value)]
    (list? value) [:list (mapv canonical value)]
    :else [:scalar value]))

(defn digest
  "SHA-256 of canonical plain EDN, independent of map/set insertion order and
  printer bindings. Not an authenticity signature or a cross-version promise."
  [value]
  (let [source (.getBytes ^String (printed (canonical (portable value))) StandardCharsets/UTF_8)
        bytes (.digest (MessageDigest/getInstance "SHA-256") source)]
    (apply str (map #(format "%02x" (bit-and 255 %)) bytes))))

(defn- portable-output [output]
  (when (some? output) (portable (render/portable-frame output))))

(defn new-recording
  "Start with the entire immutable model, including registry versions, active
  instance state, command receipts and seed data. Optional :output preserves
  prior aim history; :metadata should identify compiler/source revisions.

  Result is plain EDN. Float values normalize to Double and metadata is dropped;
  atoms, arrays in model/state, functions, records and nonfinite floats fail."
  ([model] (new-recording model {}))
  ([model {:keys [output metadata] :or {metadata {}}}]
   (when-not (map? model) (fail! ::invalid-input "Initial model must be a map" {}))
   (let [initial {:model (portable model) :output (portable-output output)}]
     {:schema-version 1 :metadata (portable metadata) :initial initial
      :initial-digest (digest initial) :steps []})))

(defn- validate-recording! [recording]
  (when-not (and (map? recording) (= 1 (:schema-version recording))
                 (map? (:initial recording)) (map? (get-in recording [:initial :model]))
                 (vector? (:steps recording))
                 (= (:initial-digest recording) (digest (:initial recording))))
    (fail! ::invalid-recording "Invalid schema or changed initial replay snapshot" {})))

(defn- input-step [step]
  (let [kind (:kind step)
        field (case kind :command :command :frame :frame nil)]
    (when-not (and (map? step) field (map? (get step field))
                   (every? #{:kind :command :frame :clock} (keys step))
                   (not (contains? step (if (= field :command) :frame :command))))
      (fail! ::invalid-step "Input needs :kind :command/:frame and the matching payload" {}))
    (portable step)))

(defn- observation [kind result portable-frame]
  (when-not (and (map? result) (map? (:model result))
                 (case kind
                   :command (and (map? (:ack result)) (vector? (:events result)))
                   :frame (vector? (:intents result))
                   false))
    (fail! ::invalid-observation "Expected a completed control or engine result" {:kind kind}))
  (let [model (portable (:model result))
        instances (into {} (map (fn [[id instance]]
                                  [id (select-keys instance
                                                   [:id :cue-id :effect-id :effect-version :state :params
                                                    :priority :order :phase :started-at-ms :started-at-beat
                                                    :release-at-ms :release-at-beat :duration-timer :release-timer])]))
                        (:instances model))]
    (merge {:model-digest (digest model) :output-digest (digest portable-frame)
            :instances instances}
           (portable (select-keys result (case kind :command [:ack :events] :frame [:intents]))))))

(defn- append-portable [recording step result output]
  (update recording :steps conj (assoc step :expected (observation (:kind step) result output))))

(defn append-observation
  "Append one already completed command/frame and its last completed output.
  step is {:kind :command :command envelope} or {:kind :frame :frame snapshot},
  optionally :clock {:time-ms ... :beat ...} captured before that operation.
  result is the actual apply-command/advance return. Pass output nil until the
  first render, and the unchanged last output for command observations.

  This function never executes a command, effect or renderer. The owner calls it
  once after a successful commit, in commit order. It trusts that association;
  replay verifies it later. Full output projection and hashing are intentionally
  diagnostic work, not a zero-cost 40 Hz logging promise."
  [recording step result output]
  (validate-recording! recording)
  (append-portable recording (input-step step) result (portable-output output)))

(defn- capture-clock [model step]
  (if (contains? step :clock)
    (let [clock (:clock step)
          time-ms (:time-ms clock) beat (:beat clock)
          operation-time (get-in step [(:kind step) :time-ms])]
      (when-not (and (map? clock) (= #{:time-ms :beat} (set (keys clock)))
                     (finite? time-ms) (<= (:time-ms model) time-ms)
                     (<= (get-in model [:transport :time-ms] (:time-ms model)) time-ms)
                     (finite? beat) (<= (get-in model [:transport :beat] beat) beat)
                     (or (nil? operation-time) (== time-ms operation-time))
                     (or (nil? (get-in step [:frame :beat])) (== beat (get-in step [:frame :beat]))))
        (fail! ::invalid-clock "Clock capture needs nondecreasing time/beat matching the operation" {}))
      (update model :transport assoc :time-ms time-ms :beat beat))
    model))

(defn render-output
  "Default pure renderer [model frame contributions previous-output]. Callers
  may inject this signature to reuse compiled patches or select a backend.
  Master/blackout and prior rich/compact movement history come from the model
  and completed output. The returned buffers are never sent to a device."
  [model frame contributions previous-output]
  (render/resolve-contributions (:fixtures frame) contributions
                                {:master (:master model) :blackout? (:blackout? model)
                                 :include-values? false :compact-values? true
                                 :previous-values (or (:values previous-output) {})
                                 :previous-compact (:compact previous-output)}))

(defn- execute [model previous-output step compile-effect options]
  (let [model (capture-clock model step)]
    (case (:kind step)
      :command {:result (control/apply-command model (:command step)) :output previous-output}
      :frame (let [frame (merge {:show-id (:show-id model) :epoch (:epoch model)
                                 :fixtures (get-in model [:rig :fixtures] [])}
                                (:frame step))
                   result (engine/advance model frame compile-effect (get options :map-work mapv))
                   output ((get options :render-output render-output)
                           (:model result) frame (:contributions result) previous-output)]
               {:result result :output output}))))

(defn- execute-at [index model output step compile-effect options]
  (try
    (execute model output step compile-effect options)
    (catch Exception cause
      (throw (ex-info "Replay operation failed; no partial result was returned"
                      {:type ::step-failed :step-index index :kind (:kind step)
                       :cause-data (ex-data cause)} cause)))))

(defn record
  "Execute an ordered vector of command/frame inputs once and record results.
  Returns {:recording ... :model ... :output <portable frame or nil>}.
  compile-effect is the same definition->step compiler used by engine/advance.
  Options: :map-work (default mapv), :render-output, :initial-output, :metadata.
  Clocks/beats are never inferred; optional :clock captures update only transport
  time/beat before that input. Other transport changes use real commands."
  ([model steps compile-effect] (record model steps compile-effect {}))
  ([model steps compile-effect options]
   (when-not (and (vector? steps) (ifn? compile-effect))
     (fail! ::invalid-input "Recording needs a vector of inputs and a compiler" {}))
   (let [inputs (mapv input-step steps)
         recording (new-recording model {:output (:initial-output options)
                                         :metadata (:metadata options {})})]
     (loop [index 0 model (get-in recording [:initial :model])
            output (get-in recording [:initial :output]) portable-frame output
            recording recording]
       (if (= index (count inputs))
         {:recording recording :model (portable model) :output portable-frame}
         (let [step (nth inputs index)
               {result :result output :output} (execute-at index model output step compile-effect options)
               portable-frame (if (= :frame (:kind step)) (portable-output output) portable-frame)]
           (recur (inc index) (:model result) output portable-frame
                  (append-portable recording step result portable-frame))))))))

(defn replay
  "Execute a recording and compare every model, instance state, ack/event/intent
  and full rendered output digest. Returns portable final :model/:output and
  :verified-steps. First mismatch throws ::mismatch with index and changed fields;
  execution failure throws ::step-failed. Nothing is published or sent to IO.
  Use the same compiler/backend revisions; metadata is descriptive, not loaded
  as code. Serial and explicitly supplied threaded mappers share this contract."
  ([recording compile-effect] (replay recording compile-effect {}))
  ([recording compile-effect options]
   (validate-recording! recording)
   (when-not (ifn? compile-effect) (fail! ::invalid-input "Replay needs a compiler" {}))
   (let [steps (:steps recording)]
     (loop [index 0 model (get-in recording [:initial :model])
            output (get-in recording [:initial :output]) portable-frame output]
       (if (= index (count steps))
         {:model (portable model) :output portable-frame :verified-steps index}
         (let [entry (nth steps index)
               step (input-step (dissoc entry :expected))
               {result :result output :output} (execute-at index model output step compile-effect options)
               portable-frame (if (= :frame (:kind step)) (portable-output output) portable-frame)
               actual (observation (:kind step) result portable-frame)
               expected (:expected entry)]
           (when-not (= expected actual)
             (fail! ::mismatch "Recorded behavior changed"
                    {:step-index index :kind (:kind step)
                     :fields (vec (sort (filter #(not= (get expected %) (get actual %))
                                               (into (set (keys expected)) (keys actual)))))
                     :expected expected :actual actual}))
           (recur (inc index) (:model result) output portable-frame)))))))
