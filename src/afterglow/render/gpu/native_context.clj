(ns afterglow.render.gpu.native-context
  "Offscreen desktop GL ownership and transform feedback for numerical shaders."
  (:require [clojure.string :as str])
  (:import [com.jogamp.opengl GL GL2ES2 GL2ES3 GL3 GL3ES3 GLAutoDrawable GLCapabilities
            GLDrawableFactory GLProfile GLRunnable]
           [java.io Closeable]
           [java.nio ByteBuffer ByteOrder FloatBuffer]
           [java.nio.charset StandardCharsets]
           [java.util.concurrent.locks ReentrantLock]))

(defn floats-buffer ^FloatBuffer [n]
  (.asFloatBuffer (.order (ByteBuffer/allocateDirect (Math/multiplyExact (int n) (int Float/BYTES)))
                          (ByteOrder/nativeOrder))))

(defn finite-float [value]
  (when-not (and (number? value) (Float/isFinite (unchecked-float value)))
    (throw (ex-info "Value must fit a finite shader float" {:value value})))
  (unchecked-float value))

(defn- with-context [^GLAutoDrawable drawable f]
  (let [result (volatile! nil)]
    (when-not (.invoke drawable true
                       (reify GLRunnable
                         (run [_ d]
                           ;; Keep the original Clojure exception across JOGL's callback.
                           (vreset! result (try [:ok (f (.getGL3 (.getGL ^GLAutoDrawable d)))]
                                               (catch Throwable error [:error error])))
                           true)))
      (throw (ex-info "OpenGL drawable is unavailable" {:type ::context-lost})))
    (let [[status value] @result]
      (case status
        :ok value
        :error (throw value)
        (throw (ex-info "OpenGL drawable did not execute work" {:type ::context-lost}))))))

(defn check-gl! [^GL3 gl stage]
  (let [error (.glGetError gl)]
    (when-not (= error GL/GL_NO_ERROR)
      (throw (ex-info "Native shader OpenGL operation failed" {:stage stage :gl-error error})))))

(defn- check-compiled! [^GL3 gl handle program?]
  (let [status (int-array 1)]
    (if program?
      (.glGetProgramiv gl handle GL2ES2/GL_LINK_STATUS status 0)
      (.glGetShaderiv gl handle GL2ES2/GL_COMPILE_STATUS status 0))
    (when (zero? (aget status 0))
      (let [log (byte-array 8192) n (int-array 1)]
        (if program?
          (.glGetProgramInfoLog gl handle (alength log) n 0 log 0)
          (.glGetShaderInfoLog gl handle (alength log) n 0 log 0))
        (throw (ex-info "GLSL compilation or link failed"
                        {:type ::invalid-program :stage (if program? :link :compile)
                         :log (String. log 0 (aget n 0) StandardCharsets/UTF_8)}))))))

(defn- attach! [^GL3 gl program kind source]
  (let [shader (.glCreateShader gl kind)]
    (try
      (.glShaderSource gl shader 1 (into-array String [source]) nil)
      (.glCompileShader gl shader)
      (check-compiled! gl shader false)
      (.glAttachShader gl program shader)
      (finally (.glDeleteShader gl shader)))))

(defn shader-program [^GL3 gl source varyings]
  (let [program (.glCreateProgram gl)]
    (try
      (attach! gl program GL2ES2/GL_VERTEX_SHADER (str/replace-first source "#version 300 es" "#version 330 core"))
      (attach! gl program GL2ES2/GL_FRAGMENT_SHADER "#version 330 core\nout vec4 color; void main(){color=vec4(0.0);}")
      (.glTransformFeedbackVaryings gl program (count varyings) (into-array String varyings) GL2ES3/GL_INTERLEAVED_ATTRIBS)
      (.glLinkProgram gl program)
      (check-compiled! gl program true)
      program
      (catch Throwable error (.glDeleteProgram gl program) (throw error)))))

(defrecord Context [^GLAutoDrawable drawable resources ^ReentrantLock lock closed? timeout-ms kind]
  Closeable
  (close [_]
    (.lock lock)
    (try
      (when (compare-and-set! closed? false true) (.destroy drawable))
      (finally (.unlock lock)))))

(defn open!
  "Acquire a private context, run configure! once, and retain its resources.
  The context owns all allocated buffers and programs until it is closed."
  [kind timeout-ms configure!]
  (when-not (and (integer? timeout-ms) (<= 1 timeout-ms 10000))
    (throw (ex-info "Fence timeout must be 1..10000 ms" {:timeout-ms timeout-ms})))
  (let [profile (GLProfile/get GLProfile/GL3)
        caps (doto (GLCapabilities. profile) (.setOnscreen false) (.setDoubleBuffered false))
        drawable (.createOffscreenAutoDrawable (GLDrawableFactory/getFactory profile) nil caps nil 1 1)]
    (try
      (.display drawable)
      (let [resources (with-context drawable
                        (fn [^GL3 gl]
                          (assoc (configure! gl)
                                 :renderer (.glGetString gl GL/GL_RENDERER)
                                 :version (.glGetString gl GL/GL_VERSION))))]
        (->Context drawable resources (ReentrantLock.) (atom false) timeout-ms kind))
      (catch Throwable error (.destroy drawable) (throw error)))))

(defn exclusively! [owner f]
  (let [^ReentrantLock lock (:lock owner)
        category (namespace (:kind owner))]
    (when-not (.tryLock lock)
      (throw (ex-info "Native shader context is busy" {:type (keyword category "busy")})))
    (try
      (when @(:closed? owner)
        (throw (ex-info "Native shader context is closed" {:type (keyword category "closed")})))
      (f)
      (finally (.unlock lock)))))

(defn invoke! [^Context owner f]
  (try
    (with-context (:drawable owner) f)
    (catch Throwable error (.close owner) (throw error))))

(defn prepare!
  "Compile owned resources. A rejected shader leaves existing programs usable."
  [^Context owner f]
  (try
    (with-context (:drawable owner) f)
    (catch Throwable error
      (when-not (= ::invalid-program (:type (ex-data error))) (.close owner))
      (throw error))))

(defn- await-fence! [^GL3 gl timeout-ms]
  (let [fence (.glFenceSync gl GL3ES3/GL_SYNC_GPU_COMMANDS_COMPLETE 0)]
    (when (zero? fence) (throw (ex-info "Could not fence the shader" {})))
    (try
      (let [status (.glClientWaitSync gl fence GL3ES3/GL_SYNC_FLUSH_COMMANDS_BIT (* 1000000 (long timeout-ms)))]
        (when-not (or (= status GL3ES3/GL_ALREADY_SIGNALED) (= status GL3ES3/GL_CONDITION_SATISFIED))
          (throw (ex-info "Shader readback did not finish" {:status status :timeout-ms timeout-ms}))))
      (finally (.glDeleteSync gl fence)))))

(defn capture!
  "Draw n points with the bound program/VAO into output. Wait for the draw
  before copying into the reusable, caller-owned direct float buffer."
  [^GL3 gl output n ^FloatBuffer data timeout-ms]
  (.glBindBufferBase gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER 0 output)
  (.glBeginTransformFeedback gl GL/GL_POINTS)
  (.glDrawArrays gl GL/GL_POINTS 0 n)
  (.glEndTransformFeedback gl)
  (.glBindBufferBase gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER 0 0)
  (await-fence! gl timeout-ms)
  (.glBindBuffer gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER output)
  (.clear data)
  (.glGetBufferSubData gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER 0 (* 4 (.remaining data)) data)
  (check-gl! gl :readback))
