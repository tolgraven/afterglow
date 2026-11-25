(ns afterglow.control.devices.push-pad-editor
  "Pure 8×8 compound pad editing. A surface supplies its own encoder touches
  and uniquely owned pad events. Drafts stay local until the encoder is released."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.parameter-edit :as edit]
            [afterglow.control.params :as params]))

(def ^:private beat-presets
  {6 [1/16 1/8 1/6 1/4 1/3 1/2 2/3 3/4]
   7 [1 3/2 2 3 4 8 16 32]})

(defn initial-state [] {:edits {} :order [] :voices {}})

(defn active? [state] (boolean (seq (:order state))))

(defn owns-pads? [state] (boolean (seq (:voices state))))

(defn xyz-bounds?
  "Does this configuration give finite inclusive ranges for X, Y and Z?"
  [bounds]
  (and (vector? bounds) (= 3 (count bounds))
       (every? #(and (vector? %) (= 2 (count %))
                     (every? params/finite-number? %) (apply <= %)) bounds)))

(defn- xyz-ranges [schema configured]
  (if-let [[low high :as bounds] (:bounds schema)]
    (if configured
      (let [ranges (mapv (fn [[a b]] [(max a low) (min b high)]) configured)]
        (when (xyz-bounds? ranges) ranges))
      [bounds bounds bounds])
    configured))

(defn- valid-preset? [schema value]
  (try
    (params/valid-value? schema value)
    (catch ArithmeticException _
      ;; The shared schema cannot compare a repeating fraction to decimal bounds.
      false)))

(defn- editor [schema configured]
  (case (:type schema)
    (:color :gradient) {:type (:type schema) :picks []}
    :number (when (and (= :beats (:unit schema)) (:bounds schema)
                       (not (neg? (first (:bounds schema))))
                       (some #(valid-preset? schema %) (mapcat val beat-presets)))
              {:type :beat-ratio})
    :vector (when (= 3 (:size schema))
              (when-let [ranges (xyz-ranges schema configured)]
                {:type :xyz :ranges ranges}))
    nil))

(defn- draft [{:keys [type schema value picks] :as touch}]
  (if (seq picks)
    (let [colors (mapv #(edit/hsl->rgb schema (:hsl %)) picks)]
      (case type
        :color (first colors)
        :gradient (mapv (fn [index color]
                          {:position (/ index (double (max 1 (dec (count colors)))))
                           :color color})
                        (range) colors)))
    (get touch :draft value)))

(defn encoder-touch
  "Handle a touch edge. The caller supplies the touch generation as :gesture-id
  and its initial binding as :target {:instance-id :param :schema :value};
  :xyz-bounds optionally supplies three coordinate ranges from the binding.
  Release produces at most one parameter command for that captured target."
  [state {:keys [encoder-id pressed? gesture-id target]}]
  (if pressed?
    (let [{:keys [instance-id param schema value xyz-bounds]} target
          touch (when (and encoder-id gesture-id instance-id param
                           (not (contains? (:edits state) encoder-id))
                           (params/valid-value? schema value))
                  (editor schema xyz-bounds))]
      {:state (if touch
                (-> state (assoc-in [:edits encoder-id] (assoc (merge target touch) :gesture-id gesture-id))
                    (update :order conj encoder-id))
                state)})
    (if-let [{:keys [instance-id param value] :as touch} (get-in state [:edits encoder-id])]
      (let [next-value (draft touch)]
        {:state (-> state (update :edits dissoc encoder-id)
                    (update :order #(into [] (remove #{encoder-id}) %)))
         :commands (when (not= value next-value)
                     [{:op :param/set :instance-id instance-id :param param :value next-value}])})
      {:state state})))

(defn- turn-number [[low high :as bounds] value delta step fine?]
  (let [step (if (and (params/finite-number? step) (pos? step)) step
                 (- (/ high 100.0) (/ low 100.0)))
        decimal-bounds? (some decimal? bounds)
        step (cond decimal-bounds? (double step) (decimal? step) (rationalize step) :else step)
        current (cond decimal-bounds? (double value) (decimal? value) (rationalize value) :else value)
        step (if fine? (/ step 10) step)
        adjusted (+' current (*' delta step))
        clamped (max low (min high adjusted))]
    (if (== current (if decimal-bounds? (double clamped) clamped)) value clamped)))

(defn encoder-turn
  "Update the touched beat ratio or Z coordinate in its draft. Return nil when
  the encoder keeps its normal routing."
  [state encoder-id delta {:keys [step fine?]}]
  (let [path [:edits encoder-id]
        {:keys [type schema ranges] :as touch} (get-in state path)
        step (or step (:step schema))]
    (case type
      :beat-ratio (assoc-in state (conj path :draft) (turn-number (:bounds schema) (draft touch) delta step fine?))
      :xyz (let [value (draft touch)
                 z (turn-number (nth ranges 2) (nth value 2) delta step fine?)]
             (assoc-in state (conj path :draft) (assoc value 2 z)))
      nil)))

(defn- cell? [cell]
  (and (vector? cell) (= 2 (count cell))
       (every? #(and (integer? %) (<= 0 % 7)) cell)))

(defn- ratio-at [schema cell]
  (let [ratio (get-in beat-presets cell)]
    (when (valid-preset? schema ratio) ratio)))

(defn- coordinate [index [low high :as bounds]]
  (cond
    (or (zero? index) (== low high)) low
    (= 7 index) high
    :else (let [t (/ index 7.0)]
            (bindings/clamp (+ (* (- 1.0 t) low) (* t high)) bounds))))

(defn- xyz-at [touch [x y]]
  (let [[x-bounds y-bounds] (:ranges touch)]
    [(coordinate x x-bounds) (coordinate y y-bounds) (nth (draft touch) 2)]))

(defn- select-pad [state encoder voice-id [x y :as cell]]
  (let [path [:edits encoder]
        {:keys [type picks gesture-id schema] :as touch} (get-in state path)
        voice-path [:voices voice-id]
        state (assoc-in state voice-path {:encoder-id encoder :gesture-id gesture-id})]
    (case type
      (:color :gradient)
      (let [pick {:voice-id voice-id :cell cell :hsl (edit/rgb->hsl (edit/color-grid-value x y))}
            gradient? (= :gradient type)
            index (if gradient? (count picks) 0)]
        (-> state (assoc-in (conj path :picks) (if gradient? (conj picks pick) [pick]))
            (assoc-in (conj voice-path :index) index)))
      :beat-ratio (if-let [ratio (ratio-at schema cell)]
                    (assoc-in state (conj path :draft) ratio)
                    state)
      :xyz (assoc-in state path (assoc touch :draft (xyz-at touch cell) :selected-cell cell)))))

(defn- move-pad [state voice-id {:keys [encoder-id gesture-id index]} axis value]
  (let [touch (get-in state [:edits encoder-id])
        path [:edits encoder-id :picks index]
        {:keys [hsl cell] :as pick} (get-in state path)]
    (if (and (some? index) (= gesture-id (:gesture-id touch)) (= voice-id (:voice-id pick))
             (params/finite-number? value))
      (case axis
        :glide (let [base-hue (/ (first cell) 8.0)
                     offset (/ (max -1.0 (min 1.0 value)) 16.0)]
                 (assoc-in state (conj path :hsl) (assoc hsl 0 (mod (+ base-hue offset) 1.0))))
        :slide (assoc-in state (conj path :hsl) (assoc hsl 2 (max 0.0 (min 1.0 value))))
        state)
      state)))

(defn pad-event
  "Return a transition when the editor owns the pad event, or nil for the
  surface's normal routing. Press takes :cell [x y]; press, axis and release
  share :voice-id. Glide is relative fine hue. Slide is normalized lightness.
  Ownership survives encoder release until that exact pad voice also ends."
  [state {:keys [type voice-id cell axis value]}]
  (let [voice (get-in state [:voices voice-id])
        encoder (peek (:order state))]
    (case type
      :note-on (cond
                 voice {:state state}
                 (and encoder voice-id (cell? cell)) {:state (select-pad state encoder voice-id cell)})
      :axis (when voice {:state (move-pad state voice-id voice axis value)})
      :note-off (when voice {:state (update state :voices dissoc voice-id)})
      nil)))

(defn view
  "Project the most recently touched editor's cells and draft. Earlier
  touched editors keep their own drafts and resume on its release."
  [state]
  (when-let [id (peek (:order state))]
    (let [{:keys [type schema picks selected-cell] :as touch} (get-in state [:edits id])
          picked (into {} (map (juxt :cell :hsl)) picks)
          value (draft touch)]
      (merge (select-keys touch [:instance-id :param :ranges])
             {:encoder-id id :type type :value value
              :cells (mapv (fn [[x y :as cell]]
                             (merge {:x x :y y}
                                    (case type
                                      (:color :gradient)
                                      (let [hsl (get picked cell)]
                                        {:selected? (some? hsl)
                                         :color (if hsl (edit/hsl->rgb schema hsl)
                                                    (edit/color-grid-value schema x y))})
                                      :beat-ratio (if-let [ratio (ratio-at schema cell)]
                                                    {:value ratio :selected? (== (if (decimal? value) (rationalize value) value)
                                                                                 ratio)}
                                                    {:disabled? true :selected? false})
                                      :xyz {:value (xyz-at touch cell) :selected? (= selected-cell cell)})))
                           (for [y (range 8) x (range 8)] [x y]))}))))
