(ns afterglow.render.shader-frames
  "Fragment-shader video frames without a GPU: shader validation, typed
  uniform packing, GLSL assembly and the readback pixel layout.

  A shader is portable data:

    {:source   \"void main() { fragColor = vec4(u_tint, 1.0); }\"
     :uniforms {\"u_tint\" :vec3 \"u_speed\" :float}}

  The source is a GLSL 3.30 fragment body, compiled on the desktop GL 3.3
  context (`afterglow.render.gpu.shader-frames`). Afterglow declares every
  listed uniform, the viewport size `u_resolution` (vec2, pixels) and the
  output `fragColor` (vec4) before it; author #extension lines are moved
  ahead of those declarations. `u_origin`
  (vec2) is the viewport's lower-left corner in window pixels. The source
  must not declare them again. `fragColor` holds display (sRGB-encoded)
  values in [0,1], as a video frame does; the frame stores them as BGRA8.

  Frames are top-down: row 0 of the returned pixels is the top of the image,
  although gl_FragCoord.y grows upwards in the shader."
  (:require [clojure.string :as str]))

(def uniform-types
  "Declared uniform types, their GLSL names and component counts. A :bool is
  sent as 0 or 1 and an :int must have an integral value."
  {:float {:glsl "float" :components 1}
   :int {:glsl "int" :components 1}
   :bool {:glsl "bool" :components 1}
   :vec2 {:glsl "vec2" :components 2}
   :vec3 {:glsl "vec3" :components 3}
   :vec4 {:glsl "vec4" :components 4}})

(def resolution-uniform
  "The viewport size in pixels, set by the renderer on every draw."
  "u_resolution")

(def origin-uniform
  "The viewport's lower-left corner in window pixels (GL, bottom-up), so
  `(gl_FragCoord.xy - u_origin) / u_resolution` runs 0–1 across the viewport."
  "u_origin")

(def max-source-chars 65536)

(def max-uniforms 32)

(def max-dimension
  "Largest render target width or height."
  4096)

(def max-pixels
  "Largest render target area (4096 × 2160)."
  (* 4096 2160))

(def ^:private identifier #"[A-Za-z_][A-Za-z0-9_]{0,63}")

(defn- error [path message] {:path path :message message})

(defn shader-errors
  "Path/message errors for a shader map; [] when valid. The GPU compiler
  reports GLSL errors separately, with its log."
  [shader]
  (if-not (map? shader)
    [(error [] "A shader is a map with :source and :uniforms")]
    (let [{:keys [source uniforms]} shader]
      (vec
       (concat
        (when-not (and (string? source) (not (str/blank? source)))
          [(error [:source] "A shader needs GLSL source text")])
        (when (and (string? source) (> (count source) max-source-chars))
          [(error [:source] (str "Shader source is limited to " max-source-chars " characters"))])
        (when (and (string? source)
                   (let [lines (str/split-lines source)
                         versions (keep-indexed (fn [i l] (when (re-matches #"\s*#\s*version\b.*" l) i)) lines)]
                     (or (> (count versions) 1)
                         (and (seq versions) (not (every? str/blank? (take (first versions) lines)))))))
          [(error [:source] "Only the first line may name the GLSL version")])
        (when-not (or (nil? uniforms) (map? uniforms))
          [(error [:uniforms] "Uniforms are a map from GLSL name to type")])
        (when (and (map? uniforms) (> (count uniforms) max-uniforms))
          [(error [:uniforms] (str "A shader declares at most " max-uniforms " uniforms"))])
        (when (map? uniforms)
          (mapcat (fn [[name type]]
                    (cond
                      (not (and (string? name) (re-matches identifier name)))
                      [(error [:uniforms name] "A uniform name is a GLSL identifier")]
                      (or (str/starts-with? name "gl_") (#{resolution-uniform origin-uniform "fragColor"} name))
                      [(error [:uniforms name] "This name is reserved")]
                      (not (contains? uniform-types type))
                      [(error [:uniforms name] "Uniform type is :float, :int, :bool, :vec2, :vec3 or :vec4")]))
                  uniforms)))))))

(defn validate-shader!
  "Return shader or throw ex-info with :errors."
  [shader]
  (let [errors (shader-errors shader)]
    (when (seq errors)
      (throw (ex-info "Invalid shader" {:type ::invalid-shader :errors errors})))
    shader))

(defn- directive? [line kind]
  (re-matches (re-pattern (str "\\s*#\\s*" kind "\\b.*")) line))

(defn- version-line
  "Index of an author's #version line, when only blank lines precede it."
  [lines]
  (let [i (first (keep-indexed (fn [i l] (when (directive? l "version") i)) lines))]
    (when (and i (every? str/blank? (take i lines))) i)))

(defn- split-source
  "The author's #extension lines, which GLSL requires before any declaration,
  and the body. Each removed line (an author #version and the blank lines
  before it, or an #extension) stays as an empty line, so `#line 1` numbers
  the body exactly as the author's text."
  [source]
  (let [lines (str/split source #"\n" -1)
        version (version-line lines)]
    (reduce (fn [{:keys [extensions body]} [i line]]
              (cond
                (and version (<= i version)) {:extensions extensions :body (conj body "")}
                (directive? line "extension") {:extensions (conj extensions (str/trim line)) :body (conj body "")}
                :else {:extensions extensions :body (conj body line)}))
            {:extensions [] :body []}
            (map-indexed vector lines))))

(defn fragment-source
  "Complete fragment shader text for :glsl-330 (desktop GL 3.3 core) or
  :glsl-es-300. Author #extension lines come first, then the declarations
  in name order; `#line 1` keeps driver log line numbers equal to the
  author's. Only the desktop dialect is compiled and tested. GLSL ES 3.00 is
  stricter (no implicit int to float conversion, for one), so the ES text
  declares the same interface but the same body is not guaranteed to
  compile in WebGL2."
  ([shader] (fragment-source shader :glsl-330))
  ([shader dialect]
   (let [{:keys [source uniforms]} (validate-shader! shader)
         {:keys [extensions body]} (split-source source)]
     (str (case dialect :glsl-330 "#version 330 core\n" :glsl-es-300 "#version 300 es\n")
          (apply str (map #(str % "\n") extensions))
          (when (= :glsl-es-300 dialect) "precision highp float;\nprecision highp int;\n")
          "uniform vec2 " resolution-uniform ";\n"
          "uniform vec2 " origin-uniform ";\n"
          (apply str (for [[name type] (sort-by key uniforms)]
                       (str "uniform " (get-in uniform-types [type :glsl]) " " name ";\n")))
          "out vec4 fragColor;\n"
          "#line 1\n"
          (str/join "\n" body)
          "\n"))))

(def vertex-source
  "A full-screen triangle from gl_VertexID; no vertex buffers."
  (str "#version 330 core\n"
       "void main() {\n"
       "  vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));\n"
       "  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);\n"
       "}\n"))

(defn- finite? [x] (and (number? x) (Double/isFinite (double x))))

(defn- float32 [path x]
  (when-not (and (finite? x) (Float/isFinite (unchecked-float x)))
    (throw (ex-info "A uniform value must fit a finite shader float" {:type ::invalid-uniform :path path :value x})))
  (unchecked-float x))

(defn pack-uniforms
  "Check values (GLSL name -> number, boolean or vector) against the declared
  types. Returns [[name type values]] in name order, with values a float
  array for float vectors and an int array for :int and :bool. Every declared
  uniform needs a value; unknown names are refused."
  [shader values]
  (let [uniforms (:uniforms shader {})]
    (when-let [unknown (seq (remove #(contains? uniforms %) (keys values)))]
      (throw (ex-info "Values name undeclared uniforms" {:type ::invalid-uniform :names (vec unknown)})))
    (vec
     (for [[name type] (sort-by key uniforms)]
       (let [v (get values name ::missing)
             n (get-in uniform-types [type :components])]
         (when (= ::missing v)
           (throw (ex-info "A declared uniform has no value" {:type ::invalid-uniform :path [name]})))
         (case type
           :bool (do (when-not (or (boolean? v) (#{0 1} v))
                       (throw (ex-info "A :bool uniform takes true, false, 0 or 1" {:type ::invalid-uniform :path [name] :value v})))
                     [name type (int-array [(if (or (true? v) (= 1 v)) 1 0)])])
           :int (do (when-not (and (finite? v) (== v (Math/rint (double v))) (<= Integer/MIN_VALUE v Integer/MAX_VALUE))
                      (throw (ex-info "An :int uniform takes an integral value" {:type ::invalid-uniform :path [name] :value v})))
                    [name type (int-array [(long v)])])
           (let [xs (if (= 1 n) [v] v)]
             (when-not (and (sequential? xs) (= n (count xs)))
               (throw (ex-info (str "A " (clojure.core/name type) " uniform takes " n " numbers")
                               {:type ::invalid-uniform :path [name] :value v})))
             [name type (float-array (map-indexed #(float32 [name %1] %2) xs))])))))))

(defn target-errors
  "Errors for a render request's :width, :height and optional :viewport
  [x y w h] in top-down pixels inside the target."
  [{:keys [width height viewport]}]
  (vec
   (concat
    (when-not (and (pos-int? width) (pos-int? height) (<= width max-dimension) (<= height max-dimension))
      [(error [:size] (str "Render target sides are 1–" max-dimension " pixels"))])
    (when (and (pos-int? width) (pos-int? height) (> (* width height) max-pixels))
      [(error [:size] (str "A render target holds at most " max-pixels " pixels"))])
    (when (some? viewport)
      (let [[x y w h] viewport]
        (when-not (and (vector? viewport) (= 4 (count viewport)) (every? int? viewport)
                       (<= 0 x) (<= 0 y) (pos? w) (pos? h)
                       (pos-int? width) (pos-int? height)
                       (<= (+ x w) width) (<= (+ y h) height))
          [(error [:viewport] "A viewport is [x y width height] in pixels inside the target")]))))))

(defn gl-viewport
  "The GL viewport [x y w h] (bottom-up) for a top-down viewport."
  [{:keys [width height viewport]}]
  (let [[x y w h] (or viewport [0 0 width height])]
    [x (- height y h) w h]))

(defn flip-rows!
  "Reverse the row order of an owned width × height BGRA array in place (GL
  reads bottom-up; frames are top-down). Returns the array."
  ^bytes [^bytes pixels width height]
  (let [row (* 4 (long width))
        scratch (byte-array row)]
    (dotimes [y (quot (long height) 2)]
      (let [top (* row y) bottom (* row (- (long height) 1 y))]
        (System/arraycopy pixels top scratch 0 row)
        (System/arraycopy pixels bottom pixels top row)
        (System/arraycopy scratch 0 pixels bottom row)))
    pixels))
