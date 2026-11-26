(ns afterglow.render.gpu-shader-frames-test
  (:require [afterglow.render.gpu.shader-frames :as renderer]
            [afterglow.render.gpu.native-context :as context]
            [clojure.test :refer [deftest is testing]]))

(def gradient
  {:source "void main() {\n  vec2 uv = gl_FragCoord.xy / u_resolution;\n  fragColor = vec4(uv.x, uv.y, u_blue, 1.0);\n}"
   :uniforms {"u_blue" :float}})

(defn- bgra [frame x y]
  (let [i (* 4 (+ x (* y (:width frame)))) px ^bytes (:pixels frame)]
    (mapv #(bit-and 0xff (aget px (+ i %))) [0 1 2 3])))

(defn- render [r shader request] (renderer/await! (renderer/render! r shader request) 5000))

(deftest frames-are-top-down-bgra-with-uniforms-and-resolution
  (with-open [r (renderer/open!)]
    (let [frame (render r gradient {:width 4 :height 2 :uniforms {"u_blue" 0.5}})]
      (is (= [4 2 32] [(:width frame) (:height frame) (alength ^bytes (:pixels frame))]))
      ;; Pixel centres: u = (x + 0.5) / 4, v = (y + 0.5) / 2 counted from the bottom.
      (is (= [128 191 32 255] (bgra frame 0 0)) "Row 0 is the top of the image")
      (is (= [128 64 223 255] (bgra frame 3 1)))
      (is (= [0 191 32 255] (bgra (render r gradient {:width 4 :height 2 :uniforms {"u_blue" 0}}) 0 0))
          "A new uniform value reaches the next frame"))))

(deftest a-200-pixel-row-is-addressed-pixel-for-pixel
  (with-open [r (renderer/open!)]
    (let [shader {:source "void main() { float i = floor(gl_FragCoord.x); fragColor = vec4(i / 255.0, u_row, 0.0, 1.0); }"
                  :uniforms {"u_row" :float}}
          frame (render r shader {:width 200 :height 1 :uniforms {"u_row" 1.0}})]
      (is (= (vec (range 200)) (mapv #(nth (bgra frame % 0) 2) (range 200)))
          "Red carries each pixel's own index"))))

(deftest a-viewport-confines-the-draw-and-clears-the-rest-to-black
  (with-open [r (renderer/open!)]
    (let [shader {:source "void main() { fragColor = vec4((gl_FragCoord.xy - u_origin) / u_resolution, 1.0, 1.0); }"}
          frame (render r shader {:width 8 :height 8 :viewport [2 1 4 2]})]
      (is (= [0 0 0 255] (bgra frame 0 0)))
      (is (= [0 0 0 255] (bgra frame 7 7)))
      (is (= [0 0 0 255] (bgra frame 1 1)) "Outside the viewport stays black")
      (testing "u_origin and u_resolution give viewport coordinates"
        ;; Top-down [2 1 4 2] in an 8 × 8 target is GL [2 5 4 2]. Its top-left
        ;; pixel centre is 0.5/4 across and 1.5/2 up the viewport.
        (is (= [255 191 32 255] (bgra frame 2 1)))
        (is (= [255 64 223 255] (bgra frame 5 2)))))))

(deftest a-failed-compile-keeps-the-last-working-program
  (with-open [r (renderer/open!)]
    (let [good (render r gradient {:width 2 :height 2 :uniforms {"u_blue" 1.0}})
          failure (try (renderer/await! (renderer/compile! r {:source "void main() { fragColor = vec4(oops); }"}) 5000)
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= ::context/invalid-program (:type failure)))
      (is (= :compile (:stage failure)))
      (is (re-find #"0:1" (:log failure)) "Log lines count from the author's source")
      (testing "after an author version line, blank lines and an #extension"
        (let [late (try (renderer/await! (renderer/compile! r {:source "\n#version 300 es\n#extension GL_ARB_shading_language_packing : enable\nvoid main() {\n  fragColor = vec4(oops);\n}"}) 5000)
                        (catch clojure.lang.ExceptionInfo e (ex-data e)))]
          (is (re-find #"0:5[:(]" (:log late)) (:log late))))
      (testing "with CRLF line endings"
        (let [crlf (try (renderer/await! (renderer/compile! r {:source "#version 300 es\r\n#extension GL_ARB_shading_language_packing : enable\r\nvoid main() {\r\n  fragColor = vec4(oops);\r\n}\r\n"}) 5000)
                        (catch clojure.lang.ExceptionInfo e (ex-data e)))]
          (is (re-find #"0:4[:(]" (:log crlf)) (:log crlf))))
      (is (= (vec (:pixels good))
             (vec (:pixels (render r gradient {:width 2 :height 2 :uniforms {"u_blue" 1.0}}))))
          "The resident program still renders")
      (is (= [1 3 1] ((juxt :programs :compile-failures :compiles) (renderer/status r)))))))

(deftest frames-own-their-pixels-and-caches-are-bounded
  (with-open [r (renderer/open! {:max-programs 2 :max-targets 2})]
    (let [a (render r gradient {:width 2 :height 1 :uniforms {"u_blue" 0}})
          b (render r gradient {:width 2 :height 1 :uniforms {"u_blue" 1}})]
      (aset-byte ^bytes (:pixels a) 0 (byte 7))
      (is (= 255 (first (bgra b 0 0))) "The worker's readback buffer never escapes")
      (doseq [i (range 3)]
        (render r (assoc gradient :source (str (:source gradient) "\n// variant " i)) {:width (+ 3 i) :height 1 :uniforms {"u_blue" 0}}))
      (is (= [2 2 2 2] ((juxt :programs :targets :evictions :target-evictions) (renderer/status r))))
      (is (true? (renderer/await! (renderer/release! r (assoc gradient :source (str (:source gradient) "\n// variant 2"))))))
      (is (= 1 (:programs (renderer/status r)))))))

(deftest closing-releases-the-context-and-refuses-work
  (let [r (renderer/open!)]
    (render r gradient {:width 2 :height 2 :uniforms {"u_blue" 0}})
    (is (true? (renderer/close! r 5000)))
    (is (= [0 0 true true] ((juxt :programs :targets :closed? :terminated?) (renderer/status r))))
    (is (= ::renderer/closed (:type (ex-data (try (renderer/render! r gradient {:width 2 :height 2 :uniforms {"u_blue" 0}})
                                                  (catch Exception e e))))))))
