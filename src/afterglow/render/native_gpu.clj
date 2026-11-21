(ns afterglow.render.native-gpu
  "Optional desktop OpenGL moving-head solver. A caller opens and closes a private
  offscreen context. Requiring this namespace does not initialize native OpenGL."
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.gpu :as gpu]
            [afterglow.render.gpu.native-context :as context])
  (:import [com.jogamp.opengl GL GL2ES2 GL2ES3 GL3]
           [java.nio FloatBuffer]))

(defn- coefficients [cal axis]
  (if (vector? cal)
    [(/ (first cal) 255.0) (/ (second cal) (* 180.0 255))]
    (let [{:keys [min-deg max-deg]} (or cal (if (= axis :pan) {:min-deg -180 :max-deg 180}
                                                {:min-deg -90 :max-deg 90}))
          scale (/ 1.0 (- max-deg min-deg))]
      [(* (- min-deg) scale) scale])))

(defn- mounts [fixtures]
  (let [data (context/floats-buffer (* 13 (count fixtures)))]
    (doseq [{:keys [position rotation-deg calibration]} fixtures
            :let [angles (mapv #(Math/toRadians (- (double %))) (or rotation-deg [0 0 0]))]
            v (concat position (map #(Math/cos %) angles) (map #(Math/sin %) angles)
                      (coefficients (:pan calibration) :pan) (coefficients (:tilt calibration) :tilt))]
      (.put data (context/finite-float v)))
    (.flip data)))

(defn- configure! [^GL3 gl ^FloatBuffer rig-data count]
  (let [program (context/shader-program gl (gpu/source :moving-head-vertex) ["axes" "requestedAnglesAndStable"])
        vao (int-array 1) buffers (int-array 3)
        output-bytes (* count 28)]
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
    (context/check-gl! gl :configure)
    {:program program :vao (aget vao 0) :input (aget buffers 1) :output (aget buffers 2)}))

(defn open!
  "Open a private OpenGL 3.3+ solver for the pan/tilt fixtures of a compiled
  Afterglow patch. :timeout-ms (default 1000) bounds native fence waiting.
  The returned Closeable exposes driver :renderer and :version under :resources."
  ([patch] (open! patch {}))
  ([patch {:keys [timeout-ms] :or {timeout-ms 1000}}]
   (when-not (= :afterglow.render.frame/patch (:type patch))
     (throw (ex-info "Supply a compiled Afterglow patch" {})))
   (let [fixtures (filterv #(and (contains? (:channels %) :pan) (contains? (:channels %) :tilt)) (:fixtures patch))
         ids (mapv :id fixtures)
         n (count ids)]
     (when (zero? n) (throw (ex-info "Patch has no pan/tilt fixtures" {})))
     (let [data (mounts fixtures)
           inputs (context/floats-buffer (* n 5))
           outputs (context/floats-buffer (* n 7))]
       (assoc (context/open! ::moving-heads timeout-ms #(configure! % data n))
              :patch patch :ids ids :ids-set (set ids) :input-buffer inputs :output-buffer outputs)))))

(defn- target-buffer! [{:keys [patch ids ids-set input-buffer]} targets history all?]
  (when-not (and (map? targets) (every? #(contains? ids-set %) (keys targets))
                 (or (not all?) (= (count ids) (count targets))))
    (throw (ex-info "Supply valid moving-head targets for the compiled patch" {:expected ids})))
  (let [^FloatBuffer data input-buffer
        active (vec (keys targets))
        pans (zipmap active (frame/previous-pans patch active history))]
    (.clear data)
    (doseq [id ids
            ;; Idle slots share the static mount buffer. Their output is discarded.
            :let [assignment (get targets id {:direction [0 0 1]})
                  direction? (and (map? assignment) (nil? (:aim assignment)))
                  target (if (map? assignment) (or (:aim assignment) (:direction assignment)) assignment)]]
      (when-not (and (vector? target) (= 3 (count target)))
        (throw (ex-info "Expected a world-space aim or direction vector" {:fixture-id id :target target})))
      (doseq [coord target] (.put data (context/finite-float coord)))
      (.put data (float (or (get pans id) -1)))
      (.put data (float (if direction? 1 0))))
    (.flip data)))

(defn- dispatch! [^GL3 gl solver ^FloatBuffer targets]
  (let [{:keys [program vao input output]} (:resources solver)
        ^FloatBuffer data (:output-buffer solver)
        n (count (:ids solver))]
    (.glUseProgram gl program)
    (.glBindVertexArray gl vao)
    (.glBindBuffer gl GL/GL_ARRAY_BUFFER input)
    (.glBufferSubData gl GL/GL_ARRAY_BUFFER 0 (* n 20) targets)
    (context/capture! gl output n data (:timeout-ms solver))))

(defn- values [ids targets ^FloatBuffer data angles?]
  (reduce (fn [result id]
            (let [pan (.get data) tilt (.get data) reachable (.get data) valid (.get data)
                  yaw (.get data) elevation (.get data) stable (.get data)]
              (if (and (contains? targets id) (or (not angles?) (= stable 1.0)))
                (do
                  (when-not (and (= valid 1.0) (<= 0.0 pan 1.0) (<= 0.0 tilt 1.0)
                                 (Float/isFinite yaw) (Float/isFinite elevation)
                                 (or (= reachable 0.0) (= reachable 1.0)))
                    (throw (ex-info "Invalid aim result or zero-distance target" {:fixture-id id})))
                  (assoc result id (cond-> {:pan (double pan) :tilt (double tilt) :aim-reachable? (= reachable 1.0)}
                                     angles? (assoc :pan-deg (double yaw) :tilt-deg (double elevation)))))
                result))) {} ids))

(defn- solve-batch! [solver targets history all?]
  (context/exclusively! solver
    (fn []
      (let [input (target-buffer! solver targets history all?)]
        (context/invoke! solver #(dispatch! % solver input))
        (values (:ids solver) targets (:output-buffer solver) (not all?))))))

(defn solve!
  "Solve one batch of world-space targets/directions keyed by fixture ID. A
  vector is an aim. Maps support :aim or :direction, with :aim taking precedence.
  Uses the caller's last committed :previous-values and/or :previous-compact. Returns a detached
  map of fixture IDs to normalized pan, tilt and reachability. Never publishes."
  ([solver targets] (solve! solver targets {}))
  ([solver targets history]
   (solve-batch! solver targets history true)))

(defn solve-selected!
  "Solve active targets by stable fixture ID for this frame. In addition to
  normalized axes, return the requested pan/tilt degrees for rich fixture state.
  Omit ambiguous wraps, mechanical stops and singulars for CPU resolution."
  [solver targets history]
  (solve-batch! solver targets history false))
