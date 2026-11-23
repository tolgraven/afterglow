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

(defn- uniform-specs [{:keys [inputs uniforms]}]
  (let [clocks (for [[key uniform] (dissoc inputs :position :surface-uv)
                     :let [meter? (#{:beats-per-bar :bars-per-phrase} key)]]
                 {:path (if meter? [:meter key] [key]) :type :number :meter? meter? :name uniform})
        params (for [[key spec] uniforms] (assoc spec :path [:params key]))]
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
         plan (ir/emit-glsl-batch outputs {:surface-uv? chart?})
         xyz (snapshot-positions positions)]
     (when (> (* (long n) (:stride plan)) 4000000)
       (throw (ex-info "Batch exceeds four million output components" {})))
     (cond-> (assoc (->Group outputs xyz plan) :bindings (uniform-specs plan))
       (contains? (:inputs plan) :surface-uv)
       (assoc :surface-uvs
              (snapshot-uvs xyz surface-uvs))))))

(defn compile-program! [^GL3 gl {:keys [positions surface-uvs plan]}]
  (let [n (quot (count positions) 3)
        points (context/floats-buffer (+ (count positions) (count surface-uvs)))
        readback (context/floats-buffer (* n (:stride plan)))]
    (if surface-uvs
      (dotimes [i n]
        (dotimes [axis 3] (.put points (float (nth positions (+ (* i 3) axis)))))
        (dotimes [axis 2] (.put points (float (nth surface-uvs (+ (* i 2) axis))))))
      (doseq [value positions] (.put points (float value))))
    (.flip points)
    (assoc (configure! gl plan points n) :plan plan :count n :readback readback)))

(defn open!
  "Compile a map of named expression trees and upload ordered fixture positions
  once. Optional :surface-uvs contains ordered UV pairs, with nil for any head
  using world x/y. Use with-open. Rebuild when fields or coordinates change."
  ([outputs positions] (open! outputs positions {}))
  ([outputs positions {:keys [surface-uvs timeout-ms] :or {timeout-ms 1000}}]
   (let [group (group outputs positions surface-uvs)]
     (context/open! ::expressions timeout-ms #(compile-program! % group)))))

(defn- uniform-values [env {:keys [path type meter?]}]
  (let [value (get-in env path)]
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

(defn- output-field [^FloatBuffer data n stride {:keys [type components offset attribute]}]
  (let [width (long components) offset (long offset) stride (long stride)
        values (double-array (* n width))]
    (dotimes [head n]
      (let [start (+ (* head stride) offset) dest (* head width)]
        (dotimes [component width]
          (let [value (.get data (int (+ start component)))]
            (when-not (Float/isFinite value)
              (throw (ex-info "Expression produced a nonfinite GPU value"
                              {:attribute attribute :head head :component component})))
            (aset-double values (int (+ dest component)) (double value))))))
    [attribute {:type type :components components :values values}]))

(defn capture-inputs [bindings env]
  (when-not (map? env) (throw (ex-info "Supply a map with captured clocks and parameters" {})))
  (mapv #(uniform-values env %) bindings))

(defn run-program! [owner {:keys [program vao output bindings readback plan] n :count} inputs]
  (when (pos? n)
    (context/invoke! owner
      (fn [^GL3 gl]
        (.glUseProgram gl program)
        (.glBindVertexArray gl vao)
        (doseq [[binding values] (map vector bindings inputs)] (upload! gl (:location binding) values))
        (context/capture! gl output n readback (:timeout-ms owner)))))
  {:count n :outputs (into {} (map #(output-field readback n (:stride plan) %)) (:outputs plan))})

(defn evaluate!
  "Evaluate one complete batch using explicit CPU-oracle environment keys.
  Returns the evaluate-batch field layout with newly owned double arrays holding
  widened GPU float32 results. Concurrent calls report ::busy."
  [runner env]
  (let [program (:resources runner)]
    (context/exclusively! runner #(run-program! runner program (capture-inputs (:bindings program) env)))))
