(ns afterglow.control.devices.push-pad-editor
  "Pure 8×8 compound pad editing. A surface supplies its own encoder touches
  and uniquely owned pad events. Drafts stay local until the encoder is released."
  (:require [afterglow.control.parameter-edit :as edit]
            [afterglow.control.params :as params]))

(defn initial-state [] {:edits {} :order [] :voices {}})

(defn active? [state] (boolean (seq (:order state))))

(defn- draft [{:keys [schema value picks]}]
  (if (seq picks)
    (let [colors (mapv #(edit/hsl->rgb schema (:hsl %)) picks)]
      (case (:type schema)
        :color (first colors)
        :gradient (mapv (fn [index color]
                          {:position (/ index (double (max 1 (dec (count colors)))))
                           :color color})
                        (range) colors)))
    value))

(defn encoder-touch
  "Handle a touch edge. The caller supplies the touch generation as :gesture-id
  and its initial binding as :target {:instance-id :param :schema :value}.
  Release produces at most one parameter command for that captured target."
  [state {:keys [encoder-id pressed? gesture-id target]}]
  (if pressed?
    (let [{:keys [instance-id param schema value]} target]
      {:state (if (and encoder-id gesture-id instance-id param
                       (#{:color :gradient} (:type schema)) (params/valid-value? schema value)
                       (not (contains? (:edits state) encoder-id)))
                (-> state
                    (assoc-in [:edits encoder-id] (assoc target :gesture-id gesture-id :picks []))
                    (update :order conj encoder-id))
                state)})
    (if-let [{:keys [instance-id param value] :as touch} (get-in state [:edits encoder-id])]
      (let [next-value (draft touch)]
        {:state (-> state (update :edits dissoc encoder-id)
                    (update :order #(into [] (remove #{encoder-id}) %)))
         :commands (when (not= value next-value)
                     [{:op :param/set :instance-id instance-id :param param :value next-value}])})
      {:state state})))

(defn- cell? [cell]
  (and (vector? cell) (= 2 (count cell))
       (every? #(and (integer? %) (<= 0 % 7)) cell)))

(defn- select-pad [state encoder voice-id [x y :as cell]]
  (let [{:keys [picks gesture-id schema]} (get-in state [:edits encoder])
        pick {:voice-id voice-id :cell cell :hsl (edit/rgb->hsl (edit/color-grid-value x y))}
        gradient? (= :gradient (:type schema))
        index (if gradient? (count picks) 0)]
    (-> state
        (assoc-in [:edits encoder :picks] (if gradient? (conj picks pick) [pick]))
        (assoc-in [:voices voice-id] {:encoder-id encoder :gesture-id gesture-id :index index}))))

(defn- move-pad [state voice-id {:keys [encoder-id gesture-id index]} axis value]
  (let [touch (get-in state [:edits encoder-id])
        path [:edits encoder-id :picks index]
        {:keys [hsl cell] :as pick} (get-in state path)]
    (if (and (= gesture-id (:gesture-id touch)) (= voice-id (:voice-id pick))
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
  "Project the most recently touched editor's palette and draft. Earlier
  touched editors keep their own drafts and resume on its release."
  [state]
  (when-let [id (peek (:order state))]
    (let [{:keys [schema picks] :as touch} (get-in state [:edits id])
          picked (into {} (map (juxt :cell :hsl)) picks)]
      (merge (select-keys touch [:instance-id :param])
             {:encoder-id id :type (:type schema) :value (draft touch)
              :cells (mapv (fn [[x y :as cell]]
                             (let [hsl (get picked cell)]
                               {:x x :y y :selected? (some? hsl)
                                :color (if hsl (edit/hsl->rgb schema hsl)
                                           (edit/color-grid-value schema x y))}))
                           (for [y (range 8) x (range 8)] [x y]))}))))
