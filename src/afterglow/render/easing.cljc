(ns afterglow.render.easing
  "Normalized timeline easing shared by render workers and live curve editors.
  The input is time in [0,1]. Outputs may overshoot for HDR or spring motion."
  (:require #?(:clj [clojure.math :as math] :cljs [cljs.math :as math])))

(defn- finite? [v]
  (and (number? v) #?(:clj (Double/isFinite (double v)) :cljs (js/Number.isFinite v))))

(defn- invalid! [curve]
  (throw (ex-info "Invalid easing curve or control points" {:curve curve})))

(defn- cubic [a b t]
  (let [u (- 1.0 t)]
    (* t (+ (* 3.0 u u a) (* 3.0 u t b) (* t t)))))

(defn- bezier [{:keys [points] :as spec}]
  (when-not (and (vector? points) (= 4 (count points)) (every? finite? points)
                 (<= 0 (points 0) 1) (<= 0 (points 2) 1))
    (invalid! spec))
  (let [[x1 y1 x2 y2] (mapv double points)]
    (fn [x]
      ;; Invert x(t), including horizontal tangents and reversed handles.
      ;; Stopping on t avoids flattening very short leading/trailing segments.
      (loop [lo 0.0 hi 1.0 i 0]
        (let [mid (* 0.5 (+ lo hi)) px (cubic x1 x2 mid)]
          (cond (or (== px x) (= i 36)) (cubic y1 y2 mid)
                (< px x) (recur mid hi (inc i))
                :else (recur lo mid (inc i))))))))

(defn- oscillator [w damping]
  (cond
    (< damping 1.0)
    (let [a (* w damping) b (* w (math/sqrt (- 1.0 (* damping damping))))]
      (fn [t] (- 1.0 (* (math/exp (* (- a) t))
                        (+ (math/cos (* b t)) (* (/ a b) (math/sin (* b t))))))))
    (> damping 1.0)
    (let [q (math/sqrt (- (* damping damping) 1.0))
          slow (/ (- w) (+ damping q)) fast (* (- w) (+ damping q))]
      (fn [t] (- 1.0 (/ (- (* fast (math/exp (* slow t))) (* slow (math/exp (* fast t))))
                         (- fast slow)))))
    :else (fn [t] (- 1.0 (* (+ 1.0 (* w t)) (math/exp (* (- w) t)))))))

(defn- smooth [x] (* x x (- 3.0 (* 2.0 x))))

(defn- spring [{:keys [frequency damping] :or {frequency 1.5 damping 0.45} :as spec}]
  (when-not (and (finite? frequency) (< 0 frequency) (<= frequency 16)
                 (finite? damping) (<= 0 damping 8))
    (invalid! spec))
  (let [response (oscillator (* 2.0 math/PI frequency) damping)
        residual (- 1.0 (response 1.0))]
    (fn [t] (+ (response t) (* residual (smooth t))))))

(defn evaluator
  "Validate authored curve data and return a sampler. Compile when settings
  change to keep the same function for every head affected by an effect."
  [curve]
  (let [shape (if (map? curve) (:type curve) (or curve :linear))
        evaluate (case shape
                   :linear identity
                   :smoothstep smooth
                   :sine #(* 0.5 (- 1.0 (math/cos (* math/PI %))))
                   :ease-in #(* % %)
                   :ease-out #(- 1.0 (* (- 1.0 %) (- 1.0 %)))
                   :ease-in-out #(if (< % 0.5) (* 2.0 % %) (- 1.0 (* 2.0 (- 1.0 %) (- 1.0 %))))
                   :step (constantly 0.0)
                   :power (let [power (:exponent curve)]
                            (when-not (and (finite? power) (pos? power)) (invalid! curve))
                            #(math/pow % power))
                   :cubic-bezier (bezier curve)
                   :spring (spring (if (map? curve) curve {}))
                   (invalid! curve))]
    (fn [fraction]
      (when-not (finite? fraction) (throw (ex-info "Tween progress must be finite" {:fraction fraction})))
      (cond (<= fraction 0) 0.0 (>= fraction 1) 1.0 :else (evaluate (double fraction))))))

(defn sample [curve fraction] ((evaluator curve) fraction))
