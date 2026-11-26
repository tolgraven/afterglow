(ns afterglow.render.gpu.shader-frames
  "Render fragment-shader frames on a private desktop GL context and read
  them back as owned BGRA8 pixels.

  One renderer owns one context and one worker thread. Every GL call, program,
  framebuffer and readback buffer stays on that thread; callers receive a
  Future. A caller that must stay responsive (a lighting frame) never waits on
  it. A shader that does not compile throws ::invalid-program with the driver
  log and leaves every resident program usable, so a host can keep rendering
  the last working version. Programs and render targets are bounded LRU caches.

  Each returned frame owns a fresh byte array, top-down, BGRA8. The direct
  readback buffer is private to the worker and reused."
  (:require [afterglow.render.gpu.lifecycle :as lifecycle]
            [afterglow.render.gpu.native-context :as context]
            [afterglow.render.shader-frames :as frames])
  (:import [com.jogamp.opengl GL GL2ES2 GL2GL3 GL3 GL3ES3]
           [java.io Closeable]
           [java.nio ByteBuffer ByteOrder]
           [java.util LinkedHashMap]
           [java.util.concurrent ArrayBlockingQueue Callable ExecutionException Future FutureTask
            RejectedExecutionException ThreadFactory ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy TimeUnit]))

(defn- release-program! [^GL3 gl {:keys [program]}]
  (.glUseProgram gl 0)
  (.glDeleteProgram gl (int program)))

(defn- release-target! [^GL3 gl {:keys [framebuffer texture]}]
  (.glBindFramebuffer gl GL/GL_FRAMEBUFFER 0)
  (.glDeleteFramebuffers gl 1 (int-array [framebuffer]) 0)
  (.glDeleteTextures gl 1 (int-array [texture]) 0))

(defn- compile-shader! [^GL3 gl kind ^String source]
  (let [shader (.glCreateShader gl kind)]
    (.glShaderSource gl shader 1 (into-array String [source]) nil)
    (.glCompileShader gl shader)
    shader))

(defn- info-log [^GL3 gl handle program?]
  (let [log (byte-array 16384) n (int-array 1)]
    (if program?
      (.glGetProgramInfoLog gl handle (alength log) n 0 log 0)
      (.glGetShaderInfoLog gl handle (alength log) n 0 log 0))
    (String. log 0 (aget n 0) java.nio.charset.StandardCharsets/UTF_8)))

(defn- status? [^GL3 gl handle program?]
  (let [out (int-array 1)]
    (if program?
      (.glGetProgramiv gl handle GL2ES2/GL_LINK_STATUS out 0)
      (.glGetShaderiv gl handle GL2ES2/GL_COMPILE_STATUS out 0))
    (not (zero? (aget out 0)))))

(defn- build-program! [^GL3 gl shader]
  (let [fragment-text (frames/fragment-source shader :glsl-330)
        vertex (compile-shader! gl GL2ES2/GL_VERTEX_SHADER frames/vertex-source)
        fragment (compile-shader! gl GL2ES2/GL_FRAGMENT_SHADER fragment-text)
        program (.glCreateProgram gl)]
    (try
      (when-not (status? gl vertex false)
        (throw (ex-info "The full-screen vertex shader did not compile" {:log (info-log gl vertex false)})))
      (when-not (status? gl fragment false)
        (throw (ex-info "GLSL compilation failed"
                        {:type ::context/invalid-program :stage :compile :log (info-log gl fragment false)})))
      (.glAttachShader gl program vertex)
      (.glAttachShader gl program fragment)
      (.glLinkProgram gl program)
      (when-not (status? gl program true)
        (throw (ex-info "GLSL link failed"
                        {:type ::context/invalid-program :stage :link :log (info-log gl program true)})))
      (let [names (list* frames/resolution-uniform frames/origin-uniform (keys (:uniforms shader)))]
        {:program program
         :locations (into {} (for [n names] [n (.glGetUniformLocation gl program ^String n)]))})
      (catch Throwable e
        (.glDeleteProgram gl program)
        (throw e))
      (finally
        (.glDeleteShader gl vertex)
        (.glDeleteShader gl fragment)))))

(defn- build-target! [^GL3 gl width height]
  (let [fb (int-array 1) tex (int-array 1)]
    (.glGenFramebuffers gl 1 fb 0)
    (.glGenTextures gl 1 tex 0)
    (try
      (.glBindTexture gl GL/GL_TEXTURE_2D (aget tex 0))
      (.glTexImage2D gl GL/GL_TEXTURE_2D 0 GL/GL_RGBA8 (int width) (int height) 0 GL/GL_RGBA GL/GL_UNSIGNED_BYTE nil)
      (.glTexParameteri gl GL/GL_TEXTURE_2D GL/GL_TEXTURE_MIN_FILTER GL/GL_NEAREST)
      (.glTexParameteri gl GL/GL_TEXTURE_2D GL/GL_TEXTURE_MAG_FILTER GL/GL_NEAREST)
      (.glBindFramebuffer gl GL/GL_FRAMEBUFFER (aget fb 0))
      (.glFramebufferTexture2D gl GL/GL_FRAMEBUFFER GL/GL_COLOR_ATTACHMENT0 GL/GL_TEXTURE_2D (aget tex 0) 0)
      (let [status (.glCheckFramebufferStatus gl GL/GL_FRAMEBUFFER)]
        (when-not (= status GL/GL_FRAMEBUFFER_COMPLETE)
          (throw (ex-info "Render target is incomplete" {:status status :width width :height height}))))
      (context/check-gl! gl :render-target)
      {:framebuffer (aget fb 0) :texture (aget tex 0) :width width :height height
       :readback (.order (ByteBuffer/allocateDirect (* 4 (int width) (int height))) (ByteOrder/nativeOrder))}
      (catch Throwable e
        (release-target! gl {:framebuffer (aget fb 0) :texture (aget tex 0)})
        (throw e)))))

(defn- set-uniform! [^GL3 gl location type values]
  (when-not (neg? (long location))
    (case type
      (:int :bool) (.glUniform1i gl location (aget ^ints values 0))
      :float (.glUniform1f gl location (aget ^floats values 0))
      :vec2 (.glUniform2fv gl location 1 ^floats values 0)
      :vec3 (.glUniform3fv gl location 1 ^floats values 0)
      :vec4 (.glUniform4fv gl location 1 ^floats values 0))))

(defn- await-fence! [^GL3 gl timeout-ms]
  (let [fence (.glFenceSync gl GL3ES3/GL_SYNC_GPU_COMMANDS_COMPLETE 0)]
    (try
      (let [status (.glClientWaitSync gl fence GL3ES3/GL_SYNC_FLUSH_COMMANDS_BIT (* 1000000 (long timeout-ms)))]
        (when-not (or (= status GL3ES3/GL_ALREADY_SIGNALED) (= status GL3ES3/GL_CONDITION_SATISFIED))
          (throw (ex-info "Shader frame did not finish" {:type ::timeout :status status :timeout-ms timeout-ms}))))
      (finally (.glDeleteSync gl fence)))))

(defn- draw! [^GL3 gl {:keys [program locations]} target packed request query timeout-ms]
  (let [{:keys [width height]} request
        [vx vy vw vh] (frames/gl-viewport request)
        started (System/nanoTime)]
    (.glBindFramebuffer gl GL/GL_FRAMEBUFFER (:framebuffer target))
    (.glViewport gl 0 0 width height)
    (.glClearColor gl 0 0 0 1)
    (.glClear gl GL/GL_COLOR_BUFFER_BIT)
    (.glViewport gl vx vy vw vh)
    (.glUseProgram gl (int program))
    (let [resolution (get locations frames/resolution-uniform -1)]
      (when-not (neg? (long resolution)) (.glUniform2f gl resolution (float vw) (float vh))))
    (let [origin (get locations frames/origin-uniform -1)]
      (when-not (neg? (long origin)) (.glUniform2f gl origin (float vx) (float vy))))
    (doseq [[name type values] packed]
      (set-uniform! gl (get locations name -1) type values))
    (.glBeginQuery gl GL2ES2/GL_TIME_ELAPSED query)
    (.glDrawArrays gl GL/GL_TRIANGLES 0 3)
    (.glEndQuery gl GL2ES2/GL_TIME_ELAPSED)
    (await-fence! gl timeout-ms)
    (let [drawn (System/nanoTime)
          ^ByteBuffer buffer (:readback target)]
      (.clear buffer)
      (.glPixelStorei gl GL/GL_PACK_ALIGNMENT 4)
      (.glReadPixels gl 0 0 (int width) (int height) GL/GL_BGRA GL2GL3/GL_UNSIGNED_INT_8_8_8_8_REV buffer)
      (context/check-gl! gl :readback)
      (let [pixels (frames/copy-bottom-up buffer width height)
            elapsed (long-array 1)]
        (.glGetQueryObjecti64v gl query GL2ES2/GL_QUERY_RESULT elapsed 0)
        {:pixels pixels :width width :height height
         ;; Apple's GL-over-Metal driver can report a negative elapsed time;
         ;; a timer value is only reported when the driver gives a usable one.
         :gpu-ms (when (pos? (aget elapsed 0)) (/ (aget elapsed 0) 1.0e6))
         :draw-ms (/ (- drawn started) 1.0e6)
         :readback-ms (/ (- (System/nanoTime) drawn) 1.0e6)}))))

(defn- shutdown! [^ThreadPoolExecutor executor gate]
  (locking gate
    (when-not (.isShutdown executor)
      (let [waiting (java.util.ArrayList.)]
        (.drainTo (.getQueue executor) waiting)
        (doseq [^Future f waiting] (.cancel f false)))
      (.shutdown executor))))

(defrecord Renderer [owner ^ThreadPoolExecutor executor ^LinkedHashMap programs ^LinkedHashMap targets
                     max-programs max-targets stats gate done]
  Closeable
  (close [_]
    (shutdown! executor gate)
    (when-let [failure @done] (throw failure))))

(defn open!
  "Acquire one GL context and its worker. Defaults: 16 resident programs,
  8 render targets, 8 waiting jobs and a 1000 ms fence timeout per frame."
  ([] (open! {}))
  ([{:keys [max-programs max-targets queue-capacity timeout-ms]
     :or {max-programs 16 max-targets 8 queue-capacity 8 timeout-ms 1000}}]
   (when-not (and (pos-int? max-programs) (pos-int? max-targets) (pos-int? queue-capacity))
     (throw (ex-info "Program, target and queue capacities must be positive integers" {})))
   (let [gate (Object.) done (promise)
         programs (LinkedHashMap. 16 0.75 true)
         targets (LinkedHashMap. 8 0.75 true)
         stats (atom {:renders 0 :compiles 0 :compile-failures 0 :evictions 0 :programs 0 :targets 0})
         owner (context/open! ::renderer timeout-ms
                              (fn [^GL3 gl]
                                (let [vao (int-array 1) query (int-array 1)]
                                  (.glGenVertexArrays gl 1 vao 0)
                                  (.glBindVertexArray gl (aget vao 0))
                                  (.glGenQueries gl 1 query 0)
                                  {:vao (aget vao 0) :query (aget query 0)})))
         factory (reify ThreadFactory
                   (newThread [_ run] (doto (Thread. run "afterglow-shader-frames") (.setDaemon true))))]
     (try
       (let [executor (proxy [ThreadPoolExecutor]
                          [1 1 0 TimeUnit/MILLISECONDS (ArrayBlockingQueue. (int queue-capacity)) factory
                           (ThreadPoolExecutor$AbortPolicy.)]
                        (terminated []
                          (lifecycle/finish! done
                                             #(try
                                                (when-not @(:closed? owner)
                                                  (context/invoke! owner
                                                                   (fn [^GL3 gl]
                                                                     (doseq [p (vals programs)] (release-program! gl p))
                                                                     (doseq [t (vals targets)] (release-target! gl t)))))
                                                (finally
                                                  (.clear programs) (.clear targets)
                                                  (swap! stats assoc :programs 0 :targets 0)
                                                  (.close ^Closeable owner))))))]
         (.prestartCoreThread executor)
         (->Renderer owner executor programs targets max-programs max-targets stats gate done))
       (catch Throwable e (.close ^Closeable owner) (throw e))))))

(defn status
  "Counters, resident programs and targets, driver strings and queue depth."
  [{:keys [owner stats] :as renderer}]
  (let [^ThreadPoolExecutor executor (:executor renderer)]
    (merge @stats (select-keys (:resources owner) [:renderer :version])
           {:queued (.size (.getQueue executor)) :closed? (.isShutdown executor)
            :terminated? (realized? (:done renderer))})))

(defn- enqueue! [{:keys [owner executor gate] :as renderer} task]
  (let [^ThreadPoolExecutor pool executor
        job (FutureTask. ^Callable (fn []
                                     (try (task)
                                          (finally (when @(:closed? owner) (shutdown! pool gate))))))]
    (locking gate
      (when (.isShutdown pool) (throw (ex-info "Shader renderer is closed" {:type ::closed})))
      (try (.execute pool job)
           (catch RejectedExecutionException _
             (throw (ex-info "Shader renderer queue is full" {:type ::busy :queued (:queued (status renderer))})))))
    job))

(defn- program-key [shader]
  (frames/fragment-source shader :glsl-330))

(defn- resident-program! [{:keys [owner ^LinkedHashMap programs max-programs stats]} shader]
  (let [k (program-key shader)]
    (or (.get programs k)
        (let [program (try (context/prepare! owner #(build-program! % shader))
                           (catch Throwable e
                             (when (= ::context/invalid-program (:type (ex-data e)))
                               (swap! stats update :compile-failures inc))
                             (throw e)))]
          (swap! stats update :compiles inc)
          (when (>= (.size programs) (long max-programs))
            (let [eldest (.next (.iterator (.keySet programs)))]
              (context/invoke! owner #(release-program! % (.remove programs eldest)))
              (swap! stats update :evictions inc)))
          (.put programs k program)
          (swap! stats assoc :programs (.size programs))
          program))))

(defn- resident-target! [{:keys [owner ^LinkedHashMap targets max-targets stats]} width height]
  (let [k [width height]]
    (or (.get targets k)
        (let [target (context/invoke! owner #(build-target! % width height))]
          (when (>= (.size targets) (long max-targets))
            (let [eldest (.next (.iterator (.keySet targets)))]
              (context/invoke! owner #(release-target! % (.remove targets eldest)))))
          (.put targets k target)
          (swap! stats assoc :targets (.size targets))
          target))))

(defn compile!
  "Compile shader on the worker. The Future yields {:compiled? true} or
  fails with ex-data {:type ::context/invalid-program :stage :log}. A failure
  never disturbs resident programs."
  [renderer shader]
  (frames/validate-shader! shader)
  (enqueue! renderer #(do (resident-program! renderer shader) {:compiled? true})))

(defn render!
  "Render one frame. request: {:width :height :viewport [x y w h] :uniforms
  {name value}}. Values are checked before submission. The Future yields
  {:pixels (owned top-down BGRA8) :width :height :gpu-ms :draw-ms
  :readback-ms}. :draw-ms runs from the first GL call to the signalled
  fence, so it bounds the GPU execution time; :gpu-ms is the driver's timer
  query, or nil when the driver does not give a usable one."
  [renderer shader request]
  (frames/validate-shader! shader)
  (let [errors (frames/target-errors request)]
    (when (seq errors) (throw (ex-info "Invalid render target" {:type ::invalid-target :errors errors}))))
  (let [packed (frames/pack-uniforms shader (:uniforms request {}))
        {:keys [owner stats]} renderer]
    (enqueue! renderer
              (fn []
                (let [program (resident-program! renderer shader)
                      target (resident-target! renderer (:width request) (:height request))
                      result (context/invoke! owner
                                              #(draw! % program target packed request
                                                      (get-in owner [:resources :query]) (:timeout-ms owner)))]
                  (swap! stats #(-> % (update :renders inc) (assoc :last-gpu-ms (:gpu-ms result))))
                  result)))))

(defn release!
  "Release shader's program after preceding work. The Future yields true
  when it was resident."
  [{:keys [owner ^LinkedHashMap programs stats] :as renderer} shader]
  (enqueue! renderer
            (fn []
              (if-let [program (.remove programs (program-key shader))]
                (do (context/invoke! owner #(release-program! % program))
                    (swap! stats assoc :programs (.size programs))
                    true)
                false))))

(defn await!
  "Wait for a Future from this namespace, unwrapping its cause."
  ([^Future future] (try (.get future) (catch ExecutionException e (throw (.getCause e)))))
  ([^Future future timeout-ms]
   (try (.get future timeout-ms TimeUnit/MILLISECONDS)
        (catch ExecutionException e (throw (.getCause e))))))

(defn close!
  "Stop admission, cancel waiting work and release every GL object after the
  active call. With a timeout, false means cleanup continues on the owner."
  ([renderer] (.close ^Closeable renderer) true)
  ([renderer timeout-ms]
   (shutdown! (:executor renderer) (:gate renderer))
   (let [result (deref (:done renderer) timeout-ms ::pending)]
     (cond (= ::pending result) false (some? result) (throw result) :else true))))
