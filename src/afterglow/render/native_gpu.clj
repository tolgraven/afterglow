(ns afterglow.render.native-gpu
  "Optional desktop OpenGL moving-head solver. A caller opens and closes a private
  offscreen context. Requiring this namespace does not initialize native OpenGL."
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.gpu :as gpu]
            [clojure.string :as str])
  (:import [com.jogamp.opengl GL GL2ES2 GL2ES3 GL3 GL3ES3 GLAutoDrawable GLCapabilities
            GLDrawableFactory GLProfile GLRunnable]
           [java.io Closeable]
           [java.nio ByteBuffer ByteOrder FloatBuffer]
           [java.nio.charset StandardCharsets]
           [java.util.concurrent.locks ReentrantLock]))

(defn- floats-buffer ^FloatBuffer [n]
  (.asFloatBuffer (.order (ByteBuffer/allocateDirect (Math/multiplyExact (int n) (int Float/BYTES)))
                          (ByteOrder/nativeOrder))))

(defn- finite-float [value]
  (when-not (and (number? value) (Float/isFinite (unchecked-float value)))
    (throw (ex-info "Value must fit a finite shader float" {:value value})))
  (unchecked-float value))

(defn- coefficients [cal axis]
  (if (vector? cal)
    [(/ (first cal) 255.0) (/ (second cal) (* 180.0 255))]
    (let [{:keys [min-deg max-deg]} (or cal (if (= axis :pan) {:min-deg -180 :max-deg 180}
                                                {:min-deg -90 :max-deg 90}))
          scale (/ 1.0 (- max-deg min-deg))]
      [(* (- min-deg) scale) scale])))

(defn- mounts [fixtures]
  (let [data (floats-buffer (* 13 (count fixtures)))]
    (doseq [{:keys [position rotation-deg calibration]} fixtures
            :let [angles (mapv #(Math/toRadians (- (double %))) (or rotation-deg [0 0 0]))]
            v (concat position (map #(Math/cos %) angles) (map #(Math/sin %) angles)
                      (coefficients (:pan calibration) :pan) (coefficients (:tilt calibration) :tilt))]
      (.put data (finite-float v)))
    (.flip data)))

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

(defn- check-gl! [^GL3 gl stage]
  (let [error (.glGetError gl)]
    (when-not (= error GL/GL_NO_ERROR)
      (throw (ex-info "Native moving-head OpenGL operation failed" {:stage stage :gl-error error})))))

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
        (throw (ex-info "Moving-head GLSL compilation or link failed"
                        {:stage (if program? :link :compile)
                         :log (String. log 0 (aget n 0) StandardCharsets/UTF_8)}))))))

(defn- attach! [^GL3 gl program kind source]
  (let [shader (.glCreateShader gl kind)]
    (try
      (.glShaderSource gl shader 1 (into-array String [source]) nil)
      (.glCompileShader gl shader)
      (check-compiled! gl shader false)
      (.glAttachShader gl program shader)
      (finally (.glDeleteShader gl shader)))))

(defn- shader-program [^GL3 gl]
  (let [program (.glCreateProgram gl)
        source (gpu/source :moving-head-vertex)]
    (attach! gl program GL2ES2/GL_VERTEX_SHADER (str/replace-first source "#version 300 es" "#version 330 core"))
    (attach! gl program GL2ES2/GL_FRAGMENT_SHADER "#version 330 core\nout vec4 color; void main(){color=vec4(0.0);}")
    (.glTransformFeedbackVaryings gl program 1 (into-array String ["axes"]) GL2ES3/GL_INTERLEAVED_ATTRIBS)
    (.glLinkProgram gl program)
    (check-compiled! gl program true)
    program))

(defn- configure! [^GL3 gl ^FloatBuffer rig-data count]
  (let [program (shader-program gl)
        vao (int-array 1) buffers (int-array 3)
        output-bytes (* count 16)]
    (.glGenVertexArrays gl 1 vao 0)
    (.glBindVertexArray gl (aget vao 0))
    (.glUseProgram gl program)
    (.glGenBuffers gl 3 buffers 0)
    (.glBindBuffer gl GL/GL_ARRAY_BUFFER (aget buffers 0))
    (.glBufferData gl GL/GL_ARRAY_BUFFER (* 4 (.remaining rig-data)) rig-data GL/GL_STATIC_DRAW)
    (doseq [[slot size offset] [[1 3 0] [2 3 3] [3 3 6] [4 4 9]]]
      (.glEnableVertexAttribArray gl slot)
      (.glVertexAttribPointer gl slot size GL/GL_FLOAT false 52 (long (* offset 4))))
    (.glBindBuffer gl GL/GL_ARRAY_BUFFER (aget buffers 1))
    (.glBufferData gl GL/GL_ARRAY_BUFFER (* count 20) nil GL2ES2/GL_STREAM_DRAW)
    (.glEnableVertexAttribArray gl 0)
    (.glVertexAttribPointer gl 0 4 GL/GL_FLOAT false 20 (long 0))
    (.glEnableVertexAttribArray gl 5)
    (.glVertexAttribPointer gl 5 1 GL/GL_FLOAT false 20 (long 16))
    (.glBindBuffer gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER (aget buffers 2))
    (.glBufferData gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER output-bytes nil GL2ES3/GL_STREAM_READ)
    (.glEnable gl GL2ES3/GL_RASTERIZER_DISCARD)
    (check-gl! gl :configure)
    {:program program :vao (aget vao 0) :input (aget buffers 1) :output (aget buffers 2)
     :renderer (.glGetString gl GL/GL_RENDERER) :version (.glGetString gl GL/GL_VERSION)}))

(defrecord MovingHeadSolver [^GLAutoDrawable drawable patch ids ids-set resources
                             input-buffer output-buffer ^ReentrantLock lock closed? timeout-ms]
  Closeable
  (close [_]
    (.lock lock)
    (try
      (when (compare-and-set! closed? false true) (.destroy drawable))
      (finally (.unlock lock)))))

(defn open!
  "Open a private OpenGL 3.3+ solver for the pan/tilt fixtures of a compiled
  Afterglow patch. :timeout-ms (default 1000) bounds native fence waiting.
  The returned Closeable exposes driver :renderer and :version under :resources."
  ([patch] (open! patch {}))
  ([patch {:keys [timeout-ms] :or {timeout-ms 1000}}]
   (when-not (and (= :afterglow.render.frame/patch (:type patch))
                  (integer? timeout-ms) (<= 1 timeout-ms 10000))
     (throw (ex-info "Supply a compiled patch and a fence timeout of 1..10000 ms" {})))
   (let [fixtures (filterv #(and (contains? (:channels %) :pan) (contains? (:channels %) :tilt)) (:fixtures patch))
         ids (mapv :id fixtures)
         n (count ids)]
     (when (zero? n) (throw (ex-info "Patch has no pan/tilt fixtures" {})))
     (let [data (mounts fixtures)
           profile (GLProfile/get GLProfile/GL3)
           caps (doto (GLCapabilities. profile) (.setOnscreen false) (.setDoubleBuffered false))
           drawable (.createOffscreenAutoDrawable (GLDrawableFactory/getFactory profile) nil caps nil 1 1)]
       (try
         (.display drawable)
         (->MovingHeadSolver drawable patch ids (set ids) (with-context drawable #(configure! % data n))
                             (floats-buffer (* n 5)) (floats-buffer (* n 4))
                             (ReentrantLock.) (atom false) timeout-ms)
         (catch Throwable error (.destroy drawable) (throw error)))))))

(defn- target-buffer! [{:keys [patch ids ids-set input-buffer]} targets history]
  (when-not (and (map? targets) (= ids-set (set (keys targets))))
    (throw (ex-info "Supply one aim or direction for every moving head in the patch" {:expected ids})))
  (let [^FloatBuffer data input-buffer
        pans (frame/previous-pans patch ids history)]
    (.clear data)
    (doseq [[id pan] (map vector ids pans)
            :let [assignment (get targets id)
                  direction? (and (map? assignment) (nil? (:aim assignment)))
                  target (if (map? assignment) (or (:aim assignment) (:direction assignment)) assignment)]]
      (when-not (and (vector? target) (= 3 (count target)))
        (throw (ex-info "Expected a world-space aim or direction vector" {:fixture-id id :target target})))
      (doseq [coord target] (.put data (finite-float coord)))
      (.put data (float (or pan -1)))
      (.put data (float (if direction? 1 0))))
    (.flip data)))

(defn- await-fence! [^GL3 gl timeout-ms]
  (let [fence (.glFenceSync gl GL3ES3/GL_SYNC_GPU_COMMANDS_COMPLETE 0)]
    (when (zero? fence) (throw (ex-info "Could not fence the moving-head shader" {})))
    (try
      (let [status (.glClientWaitSync gl fence GL3ES3/GL_SYNC_FLUSH_COMMANDS_BIT (* 1000000 (long timeout-ms)))]
        (when-not (or (= status GL3ES3/GL_ALREADY_SIGNALED) (= status GL3ES3/GL_CONDITION_SATISFIED))
          (throw (ex-info "Moving-head shader readback did not finish" {:status status :timeout-ms timeout-ms}))))
      (finally (.glDeleteSync gl fence)))))

(defn- dispatch! [^GL3 gl solver ^FloatBuffer targets]
  (let [{:keys [program vao input output]} (:resources solver)
        ^FloatBuffer data (:output-buffer solver)
        n (count (:ids solver))
        bytes (* n 16)]
    (.glUseProgram gl program)
    (.glBindVertexArray gl vao)
    (.glBindBuffer gl GL/GL_ARRAY_BUFFER input)
    (.glBufferSubData gl GL/GL_ARRAY_BUFFER 0 (* n 20) targets)
    (.glBindBufferBase gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER 0 output)
    (.glBeginTransformFeedback gl GL/GL_POINTS)
    (.glDrawArrays gl GL/GL_POINTS 0 n)
    (.glEndTransformFeedback gl)
    (.glBindBufferBase gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER 0 0)
    (await-fence! gl (:timeout-ms solver))
    (.glBindBuffer gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER output)
    (.clear data)
    (.glGetBufferSubData gl GL2ES3/GL_TRANSFORM_FEEDBACK_BUFFER 0 bytes data)
    (check-gl! gl :readback)))

(defn- values [ids ^FloatBuffer data]
  (into {} (map (fn [id]
                  (let [pan (.get data) tilt (.get data) reachable (.get data) valid (.get data)]
                    (when-not (and (= valid 1.0) (<= 0.0 pan 1.0) (<= 0.0 tilt 1.0)
                                   (or (= reachable 0.0) (= reachable 1.0)))
                      (throw (ex-info "Invalid aim result or zero-distance target" {:fixture-id id})))
                    [id {:pan (double pan) :tilt (double tilt) :aim-reachable? (= reachable 1.0)}])))
        ids))

(defn solve!
  "Solve one batch of world-space targets/directions keyed by fixture ID. A
  vector is an aim. Maps support :aim or :direction, with :aim taking precedence.
  Uses the caller's
  last committed :previous-values and/or :previous-compact. Returns a detached
  map of fixture IDs to normalized pan, tilt and reachability. Never publishes."
  ([solver targets] (solve! solver targets {}))
  ([^MovingHeadSolver solver targets history]
   (let [^ReentrantLock lock (:lock solver)]
     (when-not (.tryLock lock) (throw (ex-info "Moving-head solver is busy" {:type ::busy})))
     (try
       (when @(:closed? solver) (throw (ex-info "Moving-head solver is closed" {:type ::closed})))
       (let [input (target-buffer! solver targets history)]
         (try
           (with-context (:drawable solver) #(dispatch! % solver input))
           (catch Throwable error (.close solver) (throw error)))
         (values (:ids solver) (:output-buffer solver)))
       (finally (.unlock lock))))))
