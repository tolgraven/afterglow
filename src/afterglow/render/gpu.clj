(ns afterglow.render.gpu
  "Packaged GPU rendering assets. Requiring this namespace creates no graphics context."
  (:require [clojure.java.io :as io]))

(def resources
  {:moving-head-vertex "gpu/mover-aim.vert"
   :moving-head-solver "gpu/mover-aim.mjs"
   :expression-runner "gpu/compute.js"})

(defn source
  "Read the source of a packaged renderer by keyword for a native or web adapter."
  [asset]
  (if-let [path (get resources asset)]
    (slurp (io/resource path) :encoding "UTF-8")
    (throw (ex-info "Unknown GPU renderer asset" {:asset asset :available (keys resources)}))))
