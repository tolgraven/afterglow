(ns afterglow.render.hdr.packed
  "Fast HDR lane operations for ordinary RGB strips and virtual RGBW colors.
  Arrays belong to the current render. Physical white overrides, specialty
  emitters and the rich representation use the reference emitter decoder.")

(deftype Storage [^doubles values ^booleans present ^long stride ^objects general])

(defn eligible? [^Storage store head]
  (when (and store (:simple-rgb? head))
    (let [i (int (:index head)) base (* i (.-stride store))
          p (.-present store) general (.-general store)]
      (and (or (nil? general) (nil? (aget general i)))
           (not (aget p (+ base 7)))
           (or (not (:extract? head))
               (not (or (aget p (+ base 4)) (aget p (+ base 5)) (aget p (+ base 6)))))))))

(defmacro raw [a p base c]
  `(let [at# (+ ~base ~c 4)] (if (aget ~p at#) (aget ~a at#) (aget ~a (+ ~base ~c)))))

(defn excess!
  "Put unclipped source excess into a three-component scratch buffer."
  [^Storage store head options ^doubles out]
  (let [base (* (long (:index head)) (.-stride store)) a (.-values store) p (.-present store)
        factor (min Double/MAX_VALUE (* (double (first options)) (if (aget p (+ base 3)) (aget a (+ base 3)) 1.0)))
        limit (double (second options))]
    (dotimes [c 3]
      (let [x (min Double/MAX_VALUE (* factor (raw a p base c)))]
        (aset out c (min limit (max 0.0 (- x 1.0))))))))

(defn write!
  "Map absolute light back into a bounded dimmer and virtual RGB. Explicit
  primary emitter overrides are folded into RGB before packing."
  [^Storage store head ^doubles incident controls]
  (let [i (long (:index head)) base (* i (.-stride store)) at (* i 3)
        a (.-values store) p (.-present store)
        [gain source-white spill-white] controls
        factor (min Double/MAX_VALUE (* (double gain) (if (aget p (+ base 3)) (aget a (+ base 3)) 1.0)))]
    (loop [c 0 d (min 1.0 factor)]
      (if (< c 3)
        (let [v (min 1.0 (* factor (raw a p base c)))
              whitened (+ v (* (double source-white) (- 1.0 v)))
              lit (min 1.0 (+ whitened (aget incident (+ at c))))
              final (+ lit (* (double spill-white) (- 1.0 lit)))]
          (aset a (+ base c) final)
          (aset p (+ base c) true)
          (aset p (+ base c 4) false)
          (recur (inc c) (max d final)))
        (do (aset a (+ base 3) d)
            (aset p (+ base 3) true)
            (when (and (pos? d) (< d 1.0))
              (dotimes [k 3] (aset a (+ base k) (/ (aget a (+ base k)) d)))))))))
