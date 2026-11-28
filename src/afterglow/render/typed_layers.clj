(ns afterglow.render.typed-layers
  "Colour-only native layer groups composed from typed colour columns into
  owned primitive arrays (tolgraven/tolglow#908).

  `afterglow.render.layers/compose-fields` remains the oracle. This path takes
  one member whose transforms all write `:color` from `:previous`, `:incoming`
  and `:field` colour through `:multiply`, `:rotate-hue`, `:color-grade` and
  `:color-guard`. It reads the lower colour from the typed columns and
  assignments emitted earlier in the stream, evaluates the program per head
  with the general path's arithmetic in the same operation order, and returns
  one typed batch in place of the general path's assignment rows.

  Anything it cannot reproduce exactly returns nil, and the caller composes
  the whole stream on the general path instead: an out-of-range or non-finite
  value, a missing field, duplicate targets, exact ratio products, other
  attributes or operators. Every array is allocated by and owned by one call;
  the per-head loop allocates nothing."
  (:require [thi.ng.math.core :as m])
  (:import [clojure.lang IFn$LL IFn$OL]))

;; Registers 0-8 hold this head's previous, incoming and field colour. Bit 1,
;; 2 and 4 of the presence mask say whether each one has a value.
(def ^:private ^:const previous-base 0)

(def ^:private ^:const incoming-base 3)

(def ^:private ^:const field-base 6)

(def ^:private ^:const first-free 9)

(def ^:private ^:const op-read 0)

(def ^:private ^:const op-mul-tt 1)

(def ^:private ^:const op-mul-ts 2)

(def ^:private ^:const op-mul-st 3)

(def ^:private ^:const op-hue 4)

(def ^:private ^:const op-grade 5)

(def ^:private ^:const op-guard 6)

(def ^:private ^:const width 5)

(def ^:private reads {:previous [previous-base 1] :incoming [incoming-base 2] :field [field-base 4]})

(defn- finite? [x] (and (number? x) (Double/isFinite (double x))))

(defn- color-record? [x] (and (record? x) (contains? x :r) (contains? x :g) (contains? x :b)))

(defn- exact-product-operand?
  "A literal whose product with another literal is computed in doubles by the
  general path too: doubles, or small integers whose product is exact."
  [x]
  (or (instance? Double x)
      (and (instance? Long x) (<= (Math/abs (long x)) 1048576))))

(defn- literal-triple
  "Components of a literal colour or XYZ triple, or nil."
  [x]
  (cond
    (color-record? x) [(:r x) (:g x) (:b x)]
    (and (vector? x) (= 3 (count x)) (every? finite? x)) x))

;; ------------------------------------------------------------------ program

(defn- const-node [state value]
  (let [{:keys [registers consts]} state]
    (cond
      (finite? value)
      [(-> state (update :registers inc) (assoc-in [:consts registers] value)) {:at registers :shape :scalar :value value}]

      (literal-triple value)
      (let [v (literal-triple value)]
        [(-> state (update :registers + 3)
             (update :consts assoc registers (nth v 0) (inc registers) (nth v 1) (+ 2 registers) (nth v 2)))
         {:at registers :shape :triple :value v}])

      :else nil)))

(defn- emit [state op a b out x]
  (update state :code into [op a b out x]))

(defn- reads? [expr]
  (and (map? expr) (not (color-record? expr))
       (or (contains? reads (:op expr)) (some reads? (:args expr)))))

(declare ^:private compile-node)

(defn- compile-read [state {:keys [op attribute] :as expr}]
  (when (= :color attribute)
    (let [[base bit] (reads op)]
      (if (contains? expr :default)
        (let [default (literal-triple (:default expr))]
          ;; A default meets per-head operands in exact arithmetic when used.
          (when (and default (every? exact-product-operand? default) (not (reads? (:default expr))))
            (when-let [[state d] (const-node state default)]
              (let [out (:registers state)]
                [(-> state (update :registers + 3) (emit op-read base bit out (:at d)))
                 {:at out :shape :triple :literal default}]))))
        (let [out (:registers state)]
          [(-> state (update :registers + 3) (emit op-read base bit out -1)) {:at out :shape :triple}])))))

(defn- literal-operand? [node]
  (or (contains? node :value) (contains? node :literal)))

(defn- literal-components [node]
  (let [v (or (:value node) (:literal node))] (if (vector? v) v [v])))

(defn- literal-product
  "The product the general path computes for two literal operands. An absent
  read's default is a plain vector there, not a colour record, so it stays
  exact until the transform's result is typed."
  [a b]
  (let [x (or (:value a) (:literal a)) y (or (:value b) (:literal b))]
    (cond (and (vector? x) (vector? y)) (mapv * x y)
          (vector? x) (mapv #(* % y) x)
          (vector? y) (mapv #(* x %) y)
          :else (* x y))))

(defn- compile-op [state {:keys [op args]} fold]
  (when-let [[state a] (compile-node state (first args) fold)]
    (when-let [[state b] (compile-node state (second args) fold)]
      (case op
        :multiply
        ;; Two literals multiply exactly in the general path: keep to
        ;; operands whose products are the same in doubles. The product is
        ;; itself a literal for the next operation, so a nested multiply is
        ;; checked against the exact value the general path carries.
        (let [literal? (and (literal-operand? a) (literal-operand? b))]
          (when (or (not literal?)
                    (every? exact-product-operand? (concat (literal-components a) (literal-components b))))
            (let [out (:registers state)
                  code (case [(:shape a) (:shape b)]
                         [:triple :triple] op-mul-tt
                         [:triple :scalar] op-mul-ts
                         [:scalar :triple] op-mul-st
                         nil)]
              (when code
                [(-> state (update :registers + 3) (emit code (:at a) (:at b) out 0))
                 (cond-> {:at out :shape :triple} literal? (assoc :literal (literal-product a b)))]))))

        :rotate-hue
        ;; Turns are a literal: the theta and its wrapped hue offset are
        ;; computed once, by the same expressions as the general path.
        (when (and (= :triple (:shape a)) (= :scalar (:shape b)) (contains? b :value))
          (let [turns (:value b)
                theta (* 2.0 Math/PI turns)
                offset (/ (rem theta m/TWO_PI) m/TWO_PI)
                at (:registers state)
                out (inc at)]
            [(-> state (update :registers + 4) (assoc-in [:consts at] offset) (emit op-hue (:at a) at out 0))
             {:at out :shape :triple}]))

        (:color-grade :color-guard)
        (when (and (= :triple (:shape a)) (= :triple (:shape b)))
          (let [out (:registers state)]
            [(-> state (update :registers + 3) (emit (if (= op :color-grade) op-grade op-guard) (:at a) (:at b) out 0))
             {:at out :shape :triple}]))

        nil))))

(defn- compile-node [state expr fold]
  (cond
    (not (reads? expr))
    (when-let [value (try (fold expr) (catch Exception _ nil))]
      (const-node state value))

    (contains? reads (:op expr)) (compile-read state expr)

    (and (map? expr) (#{:multiply :rotate-hue :color-grade :color-guard} (:op expr))
         (vector? (:args expr)) (= 2 (count (:args expr))))
    (compile-op state expr fold)

    :else nil))

(defn program
  "Compile a validated transform program, or nil when the typed path cannot
  reproduce it. `fold` evaluates a subexpression without reads on the general
  path, so literals keep the general path's exact arithmetic."
  [transforms fold]
  (when (and (seq transforms) (every? #(= :color (:attribute %)) transforms))
    (loop [state {:registers first-free :consts {} :code []}, remaining transforms, roots []]
      (if-let [{:keys [value]} (first remaining)]
        (let [start (count (:code state))]
          (when-let [[state root] (compile-node state value fold)]
            (when (= :triple (:shape root))
              (recur state (next remaining) (conj roots [start (count (:code state)) (:at root)])))))
        (let [registers (:registers state)
              initial (double-array registers)]
          (doseq [[at value] (:consts state)] (aset initial (int at) (double value)))
          {:code (int-array (:code state)) :initial initial
           :roots (int-array (mapcat identity roots)) :transforms (count roots)})))))


;; ---------------------------------------------------------- colour kernels

(defmacro ^:private finite-color?
  "Whether three registers hold a light colour as `layers/typed` accepts it:
  finite, nonnegative and, unless `high?`, at most one."
  [regs at high?]
  `(let [r# (aget ~regs ~at) g# (aget ~regs (+ ~at 1)) b# (aget ~regs (+ ~at 2))]
     (and (Double/isFinite r#) (Double/isFinite g#) (Double/isFinite b#)
          (not (neg? r#)) (not (neg? g#)) (not (neg? b#))
          (or ~high? (and (<= r# 1.0) (<= g# 1.0) (<= b# 1.0))))))

(defn- turns ^double [^double x] (- x (Math/floor x)))

(defn- unit-clamp ^double [^double x] (min 1.0 (max 0.0 x)))

(defn- smoothstep ^double [^double t]
  (let [t (unit-clamp t)] (* t t (- 3.0 (* 2.0 t)))))

(defmacro ^:private with-hsv
  "Bind h, s and v as `layers/rgb->hsv` computes them from r, g and b."
  [[h s v] [r g b] & body]
  `(let [v# (max ~r ~g ~b)
         c# (- v# (min ~r ~g ~b))
         h# (if (zero? c#) 0.0
                (if (== v# ~r) (/ (- ~g ~b) c#)
                    (if (== v# ~g) (+ 2.0 (/ (- ~b ~r) c#))
                        (+ 4.0 (/ (- ~r ~g) c#)))))
         ~h (turns (/ h# 6.0))
         ~s (if (pos? v#) (/ c# v#) 0.0)
         ~v v#]
     ~@body))

(defmacro ^:private write-rgb! [regs out r g b]
  `(do (aset ~regs ~out ~r) (aset ~regs (+ ~out 1) ~g) (aset ~regs (+ ~out 2) ~b)))

(defmacro ^:private write-hsv!
  "Write `layers/hsv->rgb` of h, s and v to three registers."
  [regs out h s v]
  `(let [v# (double ~v) s# (double ~s)
         h6# (* 6.0 (turns ~h)) sector# (long (Math/floor h6#)) f# (- h6# sector#)
         p# (* v# (- 1.0 s#)) q# (* v# (- 1.0 (* s# f#))) t# (* v# (- 1.0 (* s# (- 1.0 f#))))]
     (case (Math/floorMod sector# 6)
       0 (write-rgb! ~regs ~out v# t# p#)
       1 (write-rgb! ~regs ~out q# v# p#)
       2 (write-rgb! ~regs ~out p# v# t#)
       3 (write-rgb! ~regs ~out p# q# v#)
       4 (write-rgb! ~regs ~out t# p# v#)
       (write-rgb! ~regs ~out v# p# q#))))

(defn- grade!
  "`layers/color-grade` of the colour at `a` by the settings at `s`."
  [^doubles regs ^long a ^long s ^long out]
  (let [hue (aget regs (+ s 2))
        r0 (aget regs a) g0 (aget regs (+ a 1)) b0 (aget regs (+ a 2))]
    (if (zero? hue)
      (write-rgb! regs out r0 g0 b0)
      (with-hsv [h sat v] [r0 g0 b0]
        (write-hsv! regs out (+ h hue) sat v)))
    (let [r (aget regs out) g (aget regs (+ out 1)) b (aget regs (+ out 2))
          k (unit-clamp (aget regs (+ s 1)))
          lum (+ (+ (* 0.2126 r) (* 0.7152 g)) (* 0.0722 b))
          top (max r g b)
          gain (- 1.0 (unit-clamp (aget regs s)))]
      (write-rgb! regs out
                  (* gain (min top (max 0.0 (+ r (* k (- lum r))))))
                  (* gain (min top (max 0.0 (+ g (* k (- lum g))))))
                  (* gain (min top (max 0.0 (+ b (* k (- lum b))))))))))

(defn- guard!
  "`layers/color-guard` of the colour at `a` by the settings at `s`."
  [^doubles regs ^long a ^long s ^long out]
  (let [floor (unit-clamp (aget regs s))
        half (* 0.5 (- 1.0 (unit-clamp (aget regs (+ s 1)))))
        r (aget regs a) g (aget regs (+ a 1)) b (aget regs (+ a 2))]
    (with-hsv [h sat v] [r g b]
      (let [centre (turns (aget regs (+ s 2)))
            offset (- (turns (+ (- h centre) 0.5)) 0.5)
            h (if (and (pos? sat) (> (Math/abs offset) half))
                (turns (+ centre (if (neg? offset) (- half) half)))
                h)
            sat (if (and (pos? floor) (< sat floor))
                  (+ sat (* (- floor sat) (smoothstep (/ sat floor))))
                  sat)]
        (write-hsv! regs out h sat v)))))

(defn- clamp01 ^double [^double x] (if (< x 0.0) 0.0 (if (> x 1.0) 1.0 x)))

(defn- rotate-hue!
  "thi.ng's `rotate-hue` of an RGBA colour, as the general path calls it. The
  colour is clamped to [0,1] and converted to HSV, the hue moves by the
  wrapped offset at `delta`, and the result converts back. Saturation and
  value within thi.ng's epsilon of zero count as zero."
  [^doubles regs ^long a ^long delta ^long out]
  (let [eps (double m/*eps*)
        r (clamp01 (aget regs a)) g (clamp01 (aget regs (+ a 1))) b (clamp01 (aget regs (+ a 2)))
        v (max r g b)
        d (- v (min r g b))
        s (if (<= (Math/abs (- 0.0 v)) eps) 0.0 (/ d v))
        h (if (<= (Math/abs (- 0.0 s)) eps)
            0.0
            (if (== r v) (/ (- g b) d)
                (if (== g v) (+ 2.0 (/ (- b r) d))
                    (+ 4.0 (/ (- r g) d)))))
        h (/ h 6.0)
        h (if (neg? h) (inc h) h)
        h (+ h (aget regs delta))
        h (if (neg? h) (inc h) (if (>= h 1.0) (dec h) h))]
    (if (<= (Math/abs (- 0.0 s)) eps)
      (write-rgb! regs out v v v)
      (let [h (rem (* h 6.0) 6.0)
            i (int h)
            f (- h i)
            p (* v (- 1.0 s))
            q (* v (- 1.0 (* s f)))
            t (* v (- 1.0 (* (- 1.0 f) s)))]
        (case i
          0 (write-rgb! regs out v t p)
          1 (write-rgb! regs out q v p)
          2 (write-rgb! regs out p v t)
          3 (write-rgb! regs out p q v)
          4 (write-rgb! regs out t p v)
          (write-rgb! regs out v p q))))))

(defn- run-segment
  "Evaluate the instructions in `span`, start << 32 | end, for one head.
  `flags` holds the presence mask, plus 256 on the HDR path. False when the
  general path would fault or this path cannot match it."
  [^ints code ^doubles regs ^long span ^long flags]
  (let [start (bit-shift-right span 32) end (bit-and span 0xffffffff)
        present (bit-and flags 7) high? (not (zero? (bit-and flags 256)))]
    (loop [pc start]
      (if (>= pc end)
        true
        (let [op (aget code pc) a (aget code (+ pc 1)) b (aget code (+ pc 2)) out (aget code (+ pc 3))]
          (case op
            0 (let [default (long (aget code (+ pc 4)))
                    from (if (zero? (bit-and present b)) default (long a))]
                (if (neg? from)
                  false
                  (do (write-rgb! regs out (aget regs from) (aget regs (+ from 1)) (aget regs (+ from 2)))
                      (recur (+ pc width)))))
            1 (do (write-rgb! regs out (* (aget regs a) (aget regs b))
                              (* (aget regs (+ a 1)) (aget regs (+ b 1)))
                              (* (aget regs (+ a 2)) (aget regs (+ b 2))))
                  (if (finite-color? regs out high?) (recur (+ pc width)) false))
            2 (let [y (aget regs b)]
                (write-rgb! regs out (* (aget regs a) y) (* (aget regs (+ a 1)) y) (* (aget regs (+ a 2)) y))
                (if (finite-color? regs out high?) (recur (+ pc width)) false))
            3 (let [y (aget regs a)]
                (write-rgb! regs out (* y (aget regs b)) (* y (aget regs (+ b 1))) (* y (aget regs (+ b 2))))
                (if (finite-color? regs out high?) (recur (+ pc width)) false))
            4 (if (finite-color? regs a high?)
                (do (rotate-hue! regs a b out) (recur (+ pc width)))
                false)
            (5 6) (if (and (finite-color? regs a high?) (Double/isFinite (aget regs b))
                           (Double/isFinite (aget regs (+ b 1))) (Double/isFinite (aget regs (+ b 2))))
                    (do (if (== op op-grade) (grade! regs a b out) (guard! regs a b out))
                        (if (finite-color? regs out high?) (recur (+ pc width)) false))
                    false)))))))

;; --------------------------------------------------------------- blending

(defn- blend-code ^long [blend] (case blend :replace 0 :max 1 :add 2))

(defn- blend-component
  "One component as `frame/blend-value` blends it onto `before`, which is 0
  when there is no earlier value."
  ^double [^double before ^double value ^long blend ^double opacity]
  (let [composite (case blend 0 value 1 (max before value) (+ before value))]
    (if (== 1.0 opacity) composite (+ before (* opacity (- composite before))))))

(defn- valid-color?
  "A colour as `layers/typed` and `frame/validate-assignment!` accept it: one
  above one only where `extended` (HDR on a head with emitters) is nonzero."
  [^doubles regs ^long at ^long extended]
  (finite-color? regs at (not (zero? extended))))

(defn- blend-color!
  "Blend the colour in scratch[0..2] at opacity scratch[3] into `dest` at `at`
  as `layers/set-assignment` does, validating the value and the result.
  `control` holds the blend code in bits 0-1, 4 when `dest` holds an earlier
  value and 8 when HDR lets the colour exceed one. False when the general path
  would fault."
  [^doubles dest ^long at ^doubles scratch ^long control]
  (let [blend (bit-and control 3) had? (not (zero? (bit-and control 4))) ext (bit-and control 8)
        opacity (aget scratch 3)]
    (and (valid-color? scratch 0 ext)
         (let [r (blend-component (if had? (aget dest at) 0.0) (aget scratch 0) blend opacity)
               g (blend-component (if had? (aget dest (+ at 1)) 0.0) (aget scratch 1) blend opacity)
               b (blend-component (if had? (aget dest (+ at 2)) 0.0) (aget scratch 2) blend opacity)]
           (write-rgb! scratch 4 r g b)
           (and (valid-color? scratch 4 ext)
                (do (write-rgb! dest at r g b) true))))))

(def ^:private blends #{:replace :max :add})

(defn- unit? [x] (and (finite? x) (<= 0 x 1)))

(defn- index ^long [^IFn$OL index-of id] (.invokePrim index-of id))

(defn- flag ^long [^IFn$LL f ^long i] (if (zero? (.invokePrim f i)) 0 8))

(defn- lower-batch!
  "Fold one emitted typed batch's colour column into `prior`."
  [compiled ^ints row-of ^doubles prior ^booleans has ^doubles scratch extended?]
  (let [{:keys [target-ids target-indices columns blend opacity]} compiled
        ^ints target-indices target-indices
        ^doubles opacities (:afterglow.render.layers/opacities compiled)
        n (count target-ids)
        blend (blend-code blend)]
    (if-let [{:keys [values source-stride]} (some #(when (= :color (:attribute %)) %) columns)]
      (let [^doubles values values, stride (long source-stride), scalar (double opacity)]
        (loop [k 0]
          (if (= k n)
            true
            (let [fi (if target-indices (long (aget target-indices k)) k)
                  row (if (< fi (alength row-of)) (long (aget row-of fi)) -1)
                  o (if opacities (aget opacities k) scalar)
                  at (* k stride)]
              (if (or (neg? row) (zero? o))
                (recur (inc k))
                (do (write-rgb! scratch 0 (aget values at) (aget values (+ at 1)) (aget values (+ at 2)))
                    (aset scratch 3 o)
                    (if (blend-color! prior (* 3 row) scratch
                                      (bit-or blend (if (aget has row) 4 0) (flag extended? fi)))
                      (do (aset has row true) (recur (inc k)))
                      false)))))))
      true)))

(defn- lower-assignments!
  "Fold one emitted assignment block's colour writes into `prior`."
  [assignments ^ints row-of ^doubles prior ^booleans has ^doubles scratch {:keys [index-of extended?]}]
  (reduce
   (fn [_ {:keys [target-id attribute value] :as a}]
     (if (not= :color attribute)
       true
       (let [fi (index index-of target-id)
             row (if (and (>= fi 0) (< fi (alength row-of))) (long (aget row-of fi)) -1)]
         (if (neg? row)
           true
           (let [opacity (get a :opacity 1) blend (get a :blend :replace)
                 v (literal-triple value)]
             (cond
               (not (and v (unit? opacity) (blends blend))) (reduced false)
               (zero? opacity) true
               :else
               (do (write-rgb! scratch 0 (double (nth v 0)) (double (nth v 1)) (double (nth v 2)))
                   (aset scratch 3 (double opacity))
                   (if (blend-color! prior (* 3 row) scratch
                                     (bit-or (blend-code blend) (if (aget has row) 4 0) (flag extended? fi)))
                     (do (aset has row true) true)
                     (reduced false)))))))))
   true assignments))

(defn- lower-colors!
  "Fold the colour writes of `entries`, the blocks emitted ahead of the group,
  into `prior` for the group's rows. False when the general path would
  fault on one of them or this path cannot read it."
  [entries ^ints row-of ^doubles prior ^booleans has ^doubles scratch ctx]
  (reduce (fn [_ {:keys [kind compiled assignments]}]
            (if (if (= :batch kind)
                  (lower-batch! compiled row-of prior has scratch (:extended? ctx))
                  (lower-assignments! assignments row-of prior has scratch ctx))
              true
              (reduced false)))
          true entries))

;; ------------------------------------------------------------------ groups

(defn- run-transforms
  "Run each transform for one head, validating its colour and writing it to
  the field registers. `flags` holds the presence mask, 256 on the HDR path
  and 512 where HDR lets this head's colour exceed one."
  [^ints code ^ints roots ^doubles regs ^long flags]
  (let [transforms (quot (alength roots) 3)
        segment-flags (bit-and flags 256)
        extended (if (zero? (bit-and flags 512)) 0 1)]
    (loop [t 0, present (bit-and flags 7)]
      (if (= t transforms)
        true
        (let [start (aget roots (* 3 t)) end (aget roots (+ 1 (* 3 t))) root (aget roots (+ 2 (* 3 t)))]
          (if (and (run-segment code regs (bit-or (bit-shift-left start 32) end) (bit-or present segment-flags))
                   (valid-color? regs root extended))
            (do (write-rgb! regs field-base (aget regs root) (aget regs (+ root 1)) (aget regs (+ root 2)))
                (recur (inc t) (bit-or present 4)))
            false))))))

(definterface TypedRows
  (^long composeRow [^long row]))

;; One group's rows for one call. Every array belongs to that call: `regs`
;; and `scratch` are per-head scratch, `out` and `row-opacity` become the
;; output batch.
(deftype ^:private Rows [^ints code ^ints roots ^doubles regs ^doubles scratch
                         ^doubles prior ^booleans has ^doubles out ^doubles row-opacity
                         ^ints indices ids ^doubles values ^long stride ^long blend ^double batch-opacity
                         ^boolean batch? ^double mo ^double group-opacity weights gain gain-target?
                         ^IFn$LL extended? ^IFn$LL color? ^boolean high?]
  TypedRows
  ;; 1 when the row is written, 0 when skipped, -1 to fall back.
  (composeRow [_ row]
    (let [fi (if indices (long (aget indices row)) row)
          id (nth ids row)
          weight (when weights (get weights id 0))]
      (if (or (and weights (not (pos? weight))) (and (not batch?) (zero? (.invokePrim color? fi))))
        0
        (let [ext (flag extended? fi)
              at (* 3 row)
              had? (aget has row)
              _ (when had?
                  (write-rgb! regs previous-base (aget prior at) (aget prior (+ at 1)) (aget prior (+ at 2)))
                  (write-rgb! regs field-base (aget prior at) (aget prior (+ at 1)) (aget prior (+ at 2))))
              incoming (if batch?
                         (let [v (* row stride)]
                           (write-rgb! scratch 0 (aget values v) (aget values (+ v 1)) (aget values (+ v 2)))
                           (if (zero? batch-opacity)
                             ;; A hidden row is still validated, and writes nothing.
                             (do (aset scratch 3 1.0) (if (blend-color! regs incoming-base scratch ext) 0 -1))
                             ;; :incoming accumulates against nothing, :field against the colour beneath.
                             (do (aset scratch 3 batch-opacity)
                                 (if (and (blend-color! regs incoming-base scratch (bit-or blend ext))
                                          (blend-color! regs field-base scratch (bit-or blend ext (if had? 4 0))))
                                   1 -1))))
                         0)]
          (if (or (neg? incoming)
                  (not (run-transforms code roots regs
                                       (bit-or (if had? 5 0) (if (pos? incoming) 6 0) (if high? 256 0)
                                               (if (zero? ext) 0 512)))))
            -1
            (do
              ;; HDR member gain scales the result once, after the transforms.
              (when (and gain (gain-target? id))
                (let [g (double gain)]
                  (write-rgb! regs field-base (* (aget regs field-base) g)
                              (* (aget regs (+ field-base 1)) g) (* (aget regs (+ field-base 2)) g))))
              (let [pr (aget regs field-base) pg (aget regs (+ field-base 1)) pb (aget regs (+ field-base 2))
                    br (if had? (aget prior at) 0.0)
                    bg (if had? (aget prior (+ at 1)) 0.0)
                    bb (if had? (aget prior (+ at 2)) 0.0)]
                ;; The member's opacity mixes its result over the colour beneath once.
                (write-rgb! out at
                            (if (== 1.0 mo) pr (+ br (* mo (- pr br))))
                            (if (== 1.0 mo) pg (+ bg (* mo (- pg bg))))
                            (if (== 1.0 mo) pb (+ bb (* mo (- pb bb)))))
                (if (and (finite-color? regs field-base high?) (finite-color? out at high?))
                  (do (aset row-opacity row (if weights (* group-opacity (double weight)) group-opacity))
                      1)
                  -1)))))))))

(defn- unique-rows? [^ints indices ^long fixtures]
  (or (nil? indices)
      (let [seen (boolean-array fixtures)]
        (loop [row 0]
          (or (= row (alength indices))
              (let [i (aget indices row)]
                (and (< i fixtures) (not (aget seen i))
                     (do (aset seen i true) (recur (inc row))))))))))

(defn- descriptor-rows
  "Fixture indices of a transform-only member's explicit targets, or nil
  when one is unknown or repeated."
  [target-ids ^long fixtures index-of]
  (let [n (count target-ids) indices (int-array n) seen (boolean-array fixtures)]
    (loop [row 0]
      (if (= row n)
        indices
        (let [i (index index-of (nth target-ids row))]
          (when (and (>= i 0) (< i fixtures) (not (aget seen i)))
            (aset seen i true) (aset indices row (int i)) (recur (inc row))))))))

(defn- covered-targets?
  "Whether every explicit target that a colour transform would visit is also
  a row of the member's batch."
  [target-ids batch-ids ^ints batch-indices fixtures {:keys [index-of color?]} weights]
  (or (identical? target-ids batch-ids) (= target-ids batch-ids)
      (let [fixtures (long fixtures) in-batch (boolean-array fixtures)]
        (dotimes [row (count batch-ids)]
          (aset in-batch (if batch-indices (aget batch-indices row) row) true))
        (every? (fn [id]
                  (let [i (index index-of id)]
                    (and (>= i 0) (< i fixtures)
                         (or (aget in-batch i) (zero? (flag color? i))
                             (and weights (not (pos? (get weights id 0))))))))
                target-ids))))

(defn compose-group
  "Compose one typed colour group against `entries`, the blocks already
  emitted ahead of it. Returns the output blocks ([] when the group writes
  nothing) or nil to fall back to the general path.

  `group` carries the member's :descriptor, :batch (validated, or nil for a
  transform-only member over explicit targets), :program, :source and the
  member's HDR :gain and :gain-target?. `ctx` supplies the patch's
  :fixtures count, :index-of (IFn$OL, -1 when unknown) and, per fixture index,
  :extended? (IFn$LL, nonzero when HDR lets its colour exceed one) and
  :color? (IFn$LL, nonzero when it implements colour)."
  [{:keys [descriptor batch program source gain gain-target?]} entries high? {:keys [fixtures color? extended?] :as ctx}]
  (let [{:keys [member-opacity opacity target-ids target-weights] :or {member-opacity 1 opacity 1}} descriptor
        fixtures (long fixtures)
        weights target-weights]
    (cond
      (or (zero? opacity) (zero? member-opacity)) []
      (and weights (not-any? pos? (vals weights))) []
      :else
      (let [ids (if batch (:target-ids batch) target-ids)
            ^ints indices (if batch (:target-indices batch) (descriptor-rows target-ids fixtures (:index-of ctx)))]
        (when (and (vector? ids) (seq ids) (or batch indices)
                   (or (nil? batch) (unique-rows? indices fixtures))
                   (or (nil? batch) (empty? target-ids)
                       (covered-targets? target-ids ids indices fixtures ctx weights)))
          (let [n (count ids)
                row-of (int-array fixtures -1)
                _ (dotimes [row n] (aset row-of (if indices (aget indices row) row) (int row)))
                prior (double-array (* 3 n))
                has (boolean-array n)
                scratch (double-array 7)]
            (when (lower-colors! entries row-of prior has scratch ctx)
              (let [{:keys [^ints code ^doubles initial ^ints roots]} program
                    {:keys [values source-stride]} (some #(when (= :color (:attribute %)) %) (:columns batch))
                    out (double-array (* 3 n))
                    row-opacity (double-array n)
                    rows (Rows. code roots (aclone initial) scratch prior has out row-opacity indices ids
                                values (long (or source-stride 0)) (if batch (blend-code (:blend batch)) 0)
                                (double (:opacity batch 1)) (some? batch) (double member-opacity) (double opacity)
                                weights gain gain-target? extended? color? (boolean high?))]
                (loop [row 0, written 0, partial? (some? weights)]
                  (if (= row n)
                    (when (pos? written)
                      [{:kind :batch :source source
                        :compiled (cond-> {:target-ids ids :target-indices indices
                                           :columns [{:attribute :color :components 3 :values out
                                                      :source-stride 3 :slot 0}]
                                           :blend :replace :opacity opacity}
                                    partial? (assoc :afterglow.render.layers/opacities row-opacity))}])
                    (case (.composeRow ^TypedRows rows row)
                      1 (recur (inc row) (inc written) partial?)
                      0 (recur (inc row) written true)
                      nil)))))))))))
