(ns afterglow.render.hdr.packed
  "Packed HDR for RGB and RGBW emitters. Explicit physical channels override
  the virtual color using the same precedence as the reference decoder.")

(deftype Storage [^doubles values ^booleans present ^long stride ^objects general])

(defn eligible? [^Storage store head]
  (and store (:simple-rgb? head)
       (let [^objects general (.-general store)]
         (or (nil? general) (nil? (aget general (int (:index head))))))))

(defn- physical? [^booleans present ^long base]
  (or (aget present (+ base 4)) (aget present (+ base 5))
      (aget present (+ base 6)) (aget present (+ base 7))))

(defn- extracted ^double [^doubles values ^long base head]
  (if (:extract? head)
    (min (aget values base) (aget values (inc base)) (aget values (+ base 2)))
    0.0))

(defmacro primary [values present base c extraction]
  `(let [slot# (+ ~base ~c 4)]
     (if (aget ~present slot#) (aget ~values slot#)
       (- (aget ~values (+ ~base ~c)) ~extraction))))

(defn excess!
  "Put the visible excess of physical emitters into a three-component scratch
  buffer. Overflow on a dedicated white channel radiates equally in RGB."
  [^Storage store head options ^doubles out]
  (let [base (* (long (:index head)) (.-stride store)) ^doubles a (.-values store) ^booleans p (.-present store)
        factor (min Double/MAX_VALUE (* (double (first options)) (if (aget p (+ base 3)) (aget a (+ base 3)) 1.0)))
        physical (physical? p base)
        extraction (if physical (extracted a base head) 0.0)
        white (if (and physical (:white? head)) (if (aget p (+ base 7)) (aget a (+ base 7)) extraction) 0.0)
        white-excess (max 0.0 (- (min Double/MAX_VALUE (* factor white)) 1.0))
        limit (double (second options))]
    (dotimes [c 3]
      (let [x (min Double/MAX_VALUE (* factor (primary a p base c extraction)))]
        (aset-double out c (min limit (+ white-excess (max 0.0 (- x 1.0)))))))))

(defn write!
  "Write normalized primary and white levels back into the frame. Virtual
  color is extracted by the DMX packer when no physical overrides are owned."
  [^Storage store head ^doubles incident controls]
  (let [i (long (:index head)) base (* i (.-stride store)) at (* i 3)
        ^doubles a (.-values store) ^booleans p (.-present store)
        [gain source-white spill-white] controls
        factor (min Double/MAX_VALUE (* (double gain) (if (aget p (+ base 3)) (aget a (+ base 3)) 1.0)))
        physical (physical? p base)
        offset (if physical (+ base 4) base)
        extraction (if physical (extracted a base head) 0.0)
        white? (and physical (:white? head))
        white (if white? (min 1.0 (* factor (if (aget p (+ base 7)) (aget a (+ base 7)) extraction))) 0.0)]
    (loop [c 0 d (max (min 1.0 factor) white)]
      (if (< c 3)
        (let [v (min 1.0 (* factor (primary a p base c extraction)))
              whitened (+ v (* (double source-white) (- 1.0 v)))
              lit (min 1.0 (+ whitened (aget incident (+ at c))))
              final (+ lit (* (double spill-white) (- 1.0 lit)))]
          (aset-double a (+ offset c) final)
          (aset-boolean p (+ offset c) true)
          (when physical
            (aset-double a (+ base c) (min 1.0 (aget a (+ base c)))))
          (recur (inc c) (max d final)))
        (do (aset-double a (+ base 3) d)
            (aset-boolean p (+ base 3) true)
            (when white?
              (aset-double a (+ base 7) (if (pos? d) (/ white d) 0.0))
              (aset-boolean p (+ base 7) true))
            (when (and (pos? d) (< d 1.0))
              (dotimes [k 3] (aset-double a (+ offset k) (/ (aget a (+ offset k)) d)))))))))
