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

(defn- position-buffer ^FloatBuffer [positions n]
  (let [buffer (context/floats-buffer (* 3 n))]
    (if (vector? positions)
      (doseq [xyz positions]
        (when-not (and (vector? xyz) (= 3 (count xyz)))
          (throw (ex-info "Expected an xyz position vector" {:position xyz})))
        (doseq [x xyz] (.put buffer (context/finite-float x))))
      (let [^doubles xyz positions]
        (dotimes [i (alength xyz)] (.put buffer (context/finite-float (aget xyz i))))))
    (.flip buffer)))

(defn- uniform-bindings [^GL3 gl program {:keys [inputs uniforms]}]
  (let [clocks (for [[key uniform] (dissoc inputs :position)
                     :let [meter? (#{:beats-per-bar :bars-per-phrase} key)]]
                 {:path (if meter? [:meter key] [key]) :type :number :meter? meter? :name uniform})
        params (for [[key spec] uniforms] (assoc spec :path [:params key]))]
    (mapv #(assoc % :location (.glGetUniformLocation gl program ^String (:name %))) (concat clocks params))))

(defn- configure! [^GL3 gl plan ^FloatBuffer points n]
  (let [stride (:stride plan)
        limit (int-array 1)]
    (.glGetIntegerv gl GL2ES3/GL_MAX_TRANSFORM_FEEDBACK_INTERLEAVED_COMPONENTS limit 0)
    (when (> stride (aget limit 0))
      (throw (ex-info "Expression batch exceeds the driver's interleaved output limit"
                      {:stride stride :max-components (aget limit 0)})))
    (let [program (context/shader-program gl (:source plan) (map :varying (:outputs plan)))
          vao (int-array 1) buffers (int-array 2)]
      (.glGenVertexArrays gl 1 vao 0)
      (.glBindVertexArray gl (aget vao 0))
      (.glUseProgram gl program)
      (.glGenBuffers gl 2 buffers 0)
      (.glBindBuffer gl GL/GL_ARRAY_BUFFER (aget buffers 0))
      (.glBufferData gl GL/GL_ARRAY_BUFFER (* n 12) points GL/GL_STATIC_DRAW)
      (.glEnableVertexAttribArray gl 0)
      (.glVertexAttribPointer gl 0 3 GL/GL_FLOAT false 0 (long 0))
      (.glBindBuffer gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER (aget buffers 1))
      (.glBufferData gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER (* n stride 4) nil GL2ES3/GL_STREAM_READ)
      (.glEnable gl GL2ES3/GL_RASTERIZER_DISCARD)
      (context/check-gl! gl :configure)
      {:program program :vao (aget vao 0) :output (aget buffers 1)
       :bindings (uniform-bindings gl program plan)})))

(defn open!
  "Compile a map of named expression trees and upload ordered fixture positions
  once. Accepts the same position formats and output-size bound as evaluate-batch.
  Use with-open. Rebuild for changes to the expressions or positions."
  ([outputs positions] (open! outputs positions {}))
  ([outputs positions {:keys [timeout-ms] :or {timeout-ms 1000}}]
   (let [plan (ir/emit-glsl-batch outputs)
         n (position-count positions)
         components (* (long n) (:stride plan))]
     (when (> components 4000000) (throw (ex-info "Batch exceeds four million output components" {})))
     (let [points (position-buffer positions n)
           readback (context/floats-buffer components)]
       (assoc (context/open! ::expressions timeout-ms #(configure! % plan points n))
              :plan plan :count n :readback readback)))))

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

(defn evaluate!
  "Evaluate one complete batch using explicit CPU-oracle environment keys.
  Returns the evaluate-batch field layout with newly owned double arrays holding
  widened GPU float32 results. Concurrent calls report ::busy."
  [runner env]
  (when-not (map? env) (throw (ex-info "Supply a map with captured clocks and parameters" {})))
  (context/exclusively! runner
    (fn []
      (let [{:keys [program vao output bindings]} (:resources runner)
            inputs (mapv #(uniform-values env %) bindings)
            n (:count runner) data (:readback runner) plan (:plan runner)]
        (when (pos? n)
          (context/invoke! runner
            (fn [^GL3 gl]
              (.glUseProgram gl program)
              (.glBindVertexArray gl vao)
              (doseq [[binding values] (map vector bindings inputs)] (upload! gl (:location binding) values))
              (context/capture! gl output n data (:timeout-ms runner)))))
        {:count n :outputs (into {} (map #(output-field data n (:stride plan) %)) (:outputs plan))}))))
