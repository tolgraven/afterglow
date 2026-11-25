(ns afterglow.render.gpu.expressions
  "Evaluate Afterglow's declarative expression batches on a private desktop GPU
  context. A host owns each plan and passes captured clocks and parameters."
  (:require [afterglow.render.gpu.native-context :as context]
            [afterglow.render.ir :as ir])
  (:import [com.jogamp.opengl GL GL2ES3 GL3]
           [java.nio FloatBuffer]))

(defn- position-count [positions]
  (cond
    (instance? (class (double-array 0)) positions)
    (let [length (alength ^doubles positions)]
      (when-not (zero? (rem length 3)) (throw (ex-info "Flat positions must contain xyz triples" {})))
      (quot length 3))
    (vector? positions) (count positions)
    :else (throw (ex-info "Supply a vector of positions or a flat double array" {}))))

(defn- snapshot-positions [positions]
  (let [append (fn [flat value] (conj flat (context/finite-float value)))
        flat (vector-of :float)]
    (if (vector? positions)
      (reduce (fn [result xyz]
                (when-not (and (vector? xyz) (= 3 (count xyz)))
                  (throw (ex-info "Expected an xyz position vector" {:position xyz})))
                (reduce append result xyz))
              flat positions)
      (reduce append flat positions))))

(defn- phase-keys [uniforms]
  (into {}
        (for [clock [:beat :elapsed-beats]]
          [clock (first (remove #(contains? uniforms %)
                                (map #(keyword (namespace ::phase) (str (name clock) "-phase-" %))
                                     (range))))])))

(defn- lower-beat-phase [node clock-keys]
  (let [args (:args node)
        phase (when (vector? args) (first args))
        terms (:args phase)]
    (cond
      ;; A step can turn an insignificant floating difference into a large
      ;; discrete move. Its existing native arithmetic stays intact.
      (#{:floor :fract} (:op node)) node
      (and (#{:sin :cos} (:op node)) (= :add (:op phase))
           (= 2 (count terms)) (= #{:beat :position} (set (map :op terms))))
      (assoc-in node [:args 0 :args]
                (mapv (fn [term]
                        (if (= :beat (:op term))
                          {:op :param :type :number
                           :key (clock-keys (if (= :absolute (:clock term)) :beat :elapsed-beats))}
                          term))
                      terms))
      (vector? args) (assoc node :args (mapv #(lower-beat-phase % clock-keys) args))
      :else node)))

(defn- native-plan [outputs plan options xyz]
  (let [aims (select-keys outputs [:aim :direction])]
    (if (seq aims)
      (let [clock-keys (phase-keys (:uniforms plan))
            lowered (update-vals aims #(lower-beat-phase % clock-keys))]
        (if (= aims lowered)
          plan
          (assoc (ir/emit-glsl-batch (merge outputs lowered) options)
                 :phase-sources (into {} (map (fn [[clock key]] [key [clock]])) clock-keys)
                 :position-ceiling (reduce (fn [largest v] (max largest (abs (double v)))) 0.0 xyz))))
      plan)))

(defn- uniform-specs [{:keys [inputs uniforms phase-sources position-ceiling]}]
  (let [clocks (for [[key uniform] (dissoc inputs :position :surface-uv)
                     :let [meter? (#{:beats-per-bar :bars-per-phrase} key)]]
                 {:path (if meter? [:meter key] [key]) :type :number :meter? meter? :name uniform})
        params (for [[key spec] uniforms]
                 (if-let [path (get phase-sources key)]
                   (assoc spec :path path :phase-position-ceiling position-ceiling)
                   (assoc spec :path [:params key])))]
    (into [] (concat clocks params))))

(defn release-program! [^GL3 gl {:keys [program vao buffers]}]
  (.glUseProgram gl 0)
  (.glBindVertexArray gl 0)
  (.glDeleteBuffers gl 2 ^ints buffers 0)
  (.glDeleteVertexArrays gl 1 (int-array [vao]) 0)
  (.glDeleteProgram gl program))

(defn- configure! [^GL3 gl plan ^FloatBuffer points n]
  (let [stride (:stride plan)
        chart? (contains? (:inputs plan) :surface-uv)
        vertex-bytes (if chart? 20 12)
        limit (int-array 1)]
    (.glGetIntegerv gl GL2ES3/GL_MAX_TRANSFORM_FEEDBACK_INTERLEAVED_COMPONENTS limit 0)
    (when (> stride (aget limit 0))
      (throw (ex-info "Expression batch exceeds the driver's interleaved output limit"
                      {:type ::context/invalid-program :stride stride :max-components (aget limit 0)})))
    (let [program (context/shader-program gl (:source plan) (map :varying (:outputs plan)))
          vao (int-array 1) buffers (int-array 2)]
      (try
        (.glGenVertexArrays gl 1 vao 0)
        (.glBindVertexArray gl (aget vao 0))
        (.glUseProgram gl program)
        (.glGenBuffers gl 2 buffers 0)
        (.glBindBuffer gl GL/GL_ARRAY_BUFFER (aget buffers 0))
        (.glBufferData gl GL/GL_ARRAY_BUFFER (* n vertex-bytes) points GL/GL_STATIC_DRAW)
        (.glEnableVertexAttribArray gl 0)
        (.glVertexAttribPointer gl 0 3 GL/GL_FLOAT false vertex-bytes (long 0))
        (when chart?
          (.glEnableVertexAttribArray gl 1)
          (.glVertexAttribPointer gl 1 2 GL/GL_FLOAT false vertex-bytes (long 12)))
        (.glBindBuffer gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER (aget buffers 1))
        (.glBufferData gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER (* n stride 4) nil GL2ES3/GL_STREAM_READ)
        (.glEnable gl GL2ES3/GL_RASTERIZER_DISCARD)
        (context/check-gl! gl :configure)
        {:program program :vao (aget vao 0) :buffers buffers :output (aget buffers 1)
         :bindings (mapv #(assoc % :location (.glGetUniformLocation gl program ^String (:name %)))
                           (uniform-specs plan))}
        (catch Throwable error
          (release-program! gl {:program program :vao (aget vao 0) :buffers buffers})
          (throw error))))))

(defn- snapshot-uvs [xyz uvs]
  (if (instance? double/1 uvs)
    (into (vector-of :float) (map context/finite-float) uvs)
    (reduce-kv (fn [flat i uv]
                 (let [x (* 3 i)
                       pair (if (nil? uv) [(nth xyz x) (nth xyz (inc x))] uv)]
                   (when-not (and (vector? pair) (= 2 (count pair)))
                     (throw (ex-info "Expected a surface UV pair" {:index i :surface-uv uv})))
                   (into flat (map context/finite-float) pair)))
               (vector-of :float) uvs)))

(defrecord Group [outputs positions plan])

(defn group
  "Compile an immutable group descriptor. Ordered positions are copied so the
  key has value equality even when the caller supplies a mutable double array."
  ([outputs positions] (group outputs positions nil))
  ([outputs positions surface-uvs]
   (let [n (position-count positions)
         _ (ir/validate-surface-uv-count! surface-uvs n)
         chart? (or (instance? double/1 surface-uvs) (some some? surface-uvs))
         options {:surface-uv? chart?}
         original (ir/emit-glsl-batch outputs options)
         xyz (snapshot-positions positions)
         plan (native-plan outputs original options xyz)]
     (when (> (* (long n) (:stride plan)) 4000000)
       (throw (ex-info "Batch exceeds four million output components" {})))
     (cond-> (assoc (->Group outputs xyz plan) :bindings (uniform-specs plan))
       (contains? (:inputs plan) :surface-uv)
       (assoc :surface-uvs
              (snapshot-uvs xyz surface-uvs))))))

(defn- draw-count [plan heads]
  (let [inputs (:inputs plan)]
    (if (or (:position inputs) (:surface-uv inputs)) heads (min 1 heads))))

(defn compile-program! [^GL3 gl {:keys [positions surface-uvs plan]}]
  (let [n (quot (count positions) 3)
        vertices (draw-count plan n)
        points (context/floats-buffer (* vertices (if surface-uvs 5 3)))
        readback (context/floats-buffer (* vertices (:stride plan)))]
    (if surface-uvs
      (dotimes [i vertices]
        (dotimes [axis 3] (.put points (float (nth positions (+ (* i 3) axis)))))
        (dotimes [axis 2] (.put points (float (nth surface-uvs (+ (* i 2) axis))))))
      (dotimes [i (* 3 vertices)] (.put points (float (nth positions i)))))
    (.flip points)
    (assoc (configure! gl plan points vertices) :plan plan :count n :vertices vertices :readback readback)))

(defn open!
  "Compile a map of named expression trees and upload ordered fixture positions
  once. Optional :surface-uvs contains ordered UV pairs, with nil for any head
  using world x/y. Use with-open. Rebuild when fields or coordinates change."
  ([outputs positions] (open! outputs positions {}))
  ([outputs positions {:keys [surface-uvs timeout-ms] :or {timeout-ms 1000}}]
   (let [group (group outputs positions surface-uvs)]
     (context/open! ::expressions timeout-ms #(compile-program! % group)))))

(defn- captured-phase [value ceiling path]
  (when-not (and (number? value) (Double/isFinite (double value)))
    (throw (ex-info "Beat phase requires a finite clock" {:type ::beat-phase :path path})))
  (let [beat (double value)]
    ;; After this point the CPU's original position + beat can itself round
    ;; by more than one float32 step at unit scale. Use the original CPU
    ;; expression rather than changing which bits of that sum survive.
    (when (> (Math/ulp (+ (abs beat) (double ceiling))) (Math/ulp (float 1.0)))
      (throw (ex-info "Beat phase addition needs the CPU reference" {:type ::beat-phase :path path})))
    (Math/atan2 (Math/sin beat) (Math/cos beat))))

(defn- uniform-values [env {:keys [path type meter? phase-position-ceiling]}]
  (let [raw (get-in env path)
        value (if (some? phase-position-ceiling) (captured-phase raw phase-position-ceiling path) raw)]
    (if (= type :number)
      (let [v (context/finite-float value)]
        (when (and meter? (not (pos? v))) (throw (ex-info "Meter must remain positive at float32 precision" {:path path})))
        [v])
      (let [size ({:vec2 2 :vec3 3 :vec4 4} type)]
        (when-not (and (vector? value) (= size (count value)))
          (throw (ex-info "Shader parameter has the wrong shape" {:path path :type type})))
        (mapv context/finite-float value)))))

(defn- upload! [^GL3 gl location values]
  (let [[x y z w] values]
    (case (count values)
      1 (.glUniform1f gl location x)
      2 (.glUniform2f gl location x y)
      3 (.glUniform3f gl location x y z)
      4 (.glUniform4f gl location x y z w))))

(defn- broadcast! [^doubles values components]
  ;; The first tuple has already been checked and widened from GPU float32.
  (loop [filled (long components)]
    (when (< filled (alength values))
      (let [more (min filled (- (alength values) filled))]
        (System/arraycopy values 0 values filled more)
        (recur (+ filled more))))))

(defn expand-uniform
  "Expand one validated native tuple into independently owned arrays for n heads."
  [sample n]
  (let [expand (fn [{:keys [components] :as field}]
                 (let [tuple ^doubles (:values field)
                       values (java.util.Arrays/copyOf tuple (int (* n components)))]
                   (broadcast! values components)
                   (assoc field :values values)))]
    (assoc sample :count n :outputs (update-vals (:outputs sample) expand))))

(defn- output-field [^FloatBuffer data n vertices stride {:keys [type components offset attribute]}]
  (let [width (long components) offset (long offset) stride (long stride)
        values (double-array (* n width))]
    (dotimes [head vertices]
      (let [start (+ (* head stride) offset) dest (* head width)]
        (dotimes [component width]
          (let [value (.get data (int (+ start component)))]
            (when-not (Float/isFinite value)
              (throw (ex-info "Expression produced a nonfinite GPU value"
                              {:attribute attribute :head head :component component})))
            (aset-double values (int (+ dest component)) (double value))))))
    (when (< vertices n) (broadcast! values width))
    [attribute {:type type :components components :values values}]))

(defn capture-inputs [bindings env]
  (when-not (map? env) (throw (ex-info "Supply a map with captured clocks and parameters" {})))
  (mapv #(uniform-values env %) bindings))

(defn run-program! [owner {:keys [program vao output bindings readback plan vertices] n :count} inputs]
  (when (pos? n)
    (context/invoke! owner
      (fn [^GL3 gl]
        (.glUseProgram gl program)
        (.glBindVertexArray gl vao)
        (doseq [[binding values] (map vector bindings inputs)] (upload! gl (:location binding) values))
        (context/capture! gl output vertices readback (:timeout-ms owner)))))
  {:count n :outputs (into {} (map #(output-field readback n vertices (:stride plan) %)) (:outputs plan))})

(defn evaluate!
  "Evaluate one complete batch using explicit CPU-oracle environment keys.
  Returns the evaluate-batch field layout with newly owned double arrays holding
  widened GPU float32 results. Concurrent calls report ::busy."
  [runner env]
  (let [program (:resources runner)]
    (context/exclusively! runner #(run-program! runner program (capture-inputs (:bindings program) env)))))
