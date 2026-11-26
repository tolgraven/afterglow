(ns afterglow.render.shader-frames-test
  (:require [afterglow.render.shader-frames :as frames]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]])
  )

(def plasma {:source "void main() { fragColor = vec4(u_tint * u_level, 1.0); }"
             :uniforms {"u_tint" :vec3 "u_level" :float "u_on" :bool "u_steps" :int}})

(deftest shaders-are-validated-before-a-gpu-sees-them
  (is (= [] (frames/shader-errors plasma)))
  (is (= [] (frames/shader-errors (assoc plasma :source (str "#version 300 es\n" (:source plasma)))))
      "An author's first-line version is accepted and replaced")
  (testing "refusals carry paths"
    (is (= [[:source]] (map :path (frames/shader-errors {:source " "}))))
    (is (= [[:source]] (map :path (frames/shader-errors {:source (apply str (repeat 70000 "x"))}))))
    (is (= [[:source]] (map :path (frames/shader-errors {:source "void main(){}\n#version 330 core\n"}))))
    (is (= [[:uniforms "u_resolution"]] (map :path (frames/shader-errors {:source "x" :uniforms {"u_resolution" :vec2}}))))
    (is (= [[:uniforms "u_origin"]] (map :path (frames/shader-errors {:source "x" :uniforms {"u_origin" :vec2}}))))
    (is (= [[:uniforms "gl_Thing"]] (map :path (frames/shader-errors {:source "x" :uniforms {"gl_Thing" :float}}))))
    (is (= [[:uniforms "u x"]] (map :path (frames/shader-errors {:source "x" :uniforms {"u x" :float}}))))
    (is (= [[:uniforms "u_m"]] (map :path (frames/shader-errors {:source "x" :uniforms {"u_m" :mat4}}))))
    (is (= [[:uniforms]] (map :path (frames/shader-errors {:source "x" :uniforms (into {} (for [i (range 33)] [(str "u" i) :float]))}))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid shader" (frames/validate-shader! {:source nil})))))

(deftest both-dialects-declare-the-same-uniforms-before-the-author-source
  (let [desktop (frames/fragment-source (assoc plasma :source (str "#version 300 es\n" (:source plasma))))
        web (frames/fragment-source plasma :glsl-es-300)
        declarations ["uniform vec2 u_resolution;" "uniform vec2 u_origin;" "uniform float u_level;" "uniform bool u_on;"
                      "uniform int u_steps;" "uniform vec3 u_tint;" "out vec4 fragColor;"]]
    (is (str/starts-with? desktop "#version 330 core\n"))
    (is (str/starts-with? web "#version 300 es\nprecision highp float;"))
    (is (= 1 (count (re-seq #"#version" desktop))) "The author's version line is dropped")
    (doseq [text [desktop web]]
      (is (= declarations (filterv #(or (str/starts-with? % "uniform") (str/starts-with? % "out"))
                                   (str/split-lines text)))
          "Uniforms are declared once, in name order")
      (is (str/includes? text "#line 1\n") "Log lines count from the author's first line"))
    (is (str/includes? desktop "#line 1\n\nvoid main()") "The dropped version line stays as an empty line")
    (is (str/includes? web "#line 1\nvoid main()"))))

(deftest uniforms-are-packed-by-declared-type
  (let [packed (frames/pack-uniforms plasma {"u_tint" [1 0.5 0.25] "u_level" 0.75 "u_on" true "u_steps" 3})]
    (is (= ["u_level" "u_on" "u_steps" "u_tint"] (mapv first packed)))
    (is (= [[0.75] [1] [3] [1.0 0.5 0.25]] (mapv (comp vec #(nth % 2)) packed))))
  (is (= [0] (vec (nth (second (frames/pack-uniforms plasma {"u_tint" [0 0 0] "u_level" 0 "u_on" 0 "u_steps" -2})) 2))))
  (doseq [[values path] [[{"u_tint" [1 0] "u_level" 0 "u_on" true "u_steps" 1} ["u_tint"]]
                         [{"u_tint" [1 0 0] "u_level" ##NaN "u_on" true "u_steps" 1} ["u_level" 0]]
                         [{"u_tint" [1 0 0] "u_level" 1e39 "u_on" true "u_steps" 1} ["u_level" 0]]
                         [{"u_tint" [1 0 0] "u_level" 0 "u_on" 2 "u_steps" 1} ["u_on"]]
                         [{"u_tint" [1 0 0] "u_level" 0 "u_on" true "u_steps" 1.5} ["u_steps"]]
                         [{"u_tint" [1 0 0] "u_level" 0 "u_on" true} ["u_steps"]]]]
    (is (= path (:path (ex-data (try (frames/pack-uniforms plasma values) (catch Exception e e))))) (pr-str values)))
  (is (= ["u_extra"] (:names (ex-data (try (frames/pack-uniforms {:source "x"} {"u_extra" 1}) (catch Exception e e)))))))

(deftest render-targets-and-viewports-are-bounded
  (is (= [] (frames/target-errors {:width 200 :height 1})))
  (is (= [] (frames/target-errors {:width 640 :height 360 :viewport [40 20 320 180]})))
  (is (= [[:size]] (map :path (frames/target-errors {:width 0 :height 1}))))
  (is (= [[:size]] (map :path (frames/target-errors {:width 4097 :height 1}))))
  (is (= [[:size]] (map :path (frames/target-errors {:width 4096 :height 4096}))))
  (is (= [[:viewport]] (map :path (frames/target-errors {:width 64 :height 64 :viewport [32 0 33 10]}))))
  (is (= [[:viewport]] (map :path (frames/target-errors {:width 64 :height 64 :viewport [0 0 10]}))))
  (testing "a top-down viewport becomes GL's bottom-up rectangle"
    (is (= [0 0 200 1] (frames/gl-viewport {:width 200 :height 1})))
    (is (= [40 160 320 180] (frames/gl-viewport {:width 640 :height 360 :viewport [40 20 320 180]})))))

(deftest rows-are-flipped-in-place-into-top-down-order
  (let [pixels (byte-array (range 24))]
    (is (identical? pixels (frames/flip-rows! pixels 2 3)))
    (is (= (concat (range 16 24) (range 8 16) (range 0 8)) (seq pixels))))
  (let [one-row (byte-array (range 8))]
    (is (= (range 8) (seq (frames/flip-rows! one-row 2 1))))))

(defn- body-lines
  "Lines after #line 1, numbered from 1."
  [text]
  (vec (rest (drop-while #(not= "#line 1" %) (str/split text #"\n" -1)))))

(deftest log-line-numbers-match-the-authors-text
  (testing "an author's version line and the blank lines before it keep their line numbers"
    (let [text (frames/fragment-source {:source "\n\n#version 300 es\nvoid main() {\n  fragColor = vec4(1.0);\n}"})]
      (is (= 1 (count (re-seq #"#version" text))))
      (is (= "void main() {" (nth (body-lines text) 3)) "author line 4 is body line 4")))
  (testing "#extension lines move ahead of the declarations and leave a blank line behind"
    (let [text (frames/fragment-source {:source "#extension GL_ARB_shading_language_packing : enable\nvoid main() {}\n"
                                        :uniforms {"u_a" :float}})
          lines (str/split-lines text)]
      (is (= "#extension GL_ARB_shading_language_packing : enable" (second lines)))
      (is (< 1 (.indexOf lines "uniform float u_a;")))
      (is (= ["" "void main() {}"] (subvec (body-lines text) 0 2)))))
  (testing "CRLF and CR line endings are handled like LF"
    (doseq [eol ["\r\n" "\r"]]
      (let [text (frames/fragment-source {:source (str "#version 300 es" eol "#extension GL_X : enable" eol "void main() {}" eol)})
            lines (str/split-lines text)]
        (is (= ["#version 330 core" "#extension GL_X : enable"] (subvec lines 0 2)) (pr-str eol))
        (is (= ["" "" "void main() {}"] (subvec (body-lines text) 0 3)))
        (is (not (str/includes? text "\r")))))
    (is (= [[:source]] (map :path (frames/shader-errors {:source "void main(){}\r\n#version 330 core"})))))
  (is (= [[:source]] (map :path (frames/shader-errors {:source "void main(){}\n#version 330 core"}))))
  (is (= [[:source]] (map :path (frames/shader-errors {:source "#version 330 core\n#version 330 core\nvoid main(){}"})))))
