(require '[afterglow.control.model :as control]
         '[afterglow.render.frame :as render]
         '[afterglow.runtime :as runtime]
         '[afterglow.runtime.engine :as engine]
         '[afterglow.runtime.keyframes :as keyframes]
         '[afterglow.runtime.keyframes.values :as values]
         '[clojure.java.io :as io]
         '[clojure.string :as str])
(import '[java.io BufferedOutputStream DataOutputStream]
        '[java.util Arrays])
(set! *warn-on-reflection* true)

(def ids (mapv #(keyword (str "wash-" %)) (range 64)))
(def fixtures (mapv (fn [i id]
                     {:id id :universe 1 :address (+ 1 (* i 8))
                      :channels {:dimmer {:offset 1 :fine-offset 2} :red 3 :green 4 :blue 5
                                 :white 6 :focus 7 :zoom 8}})
                   (range 64) ids))
(def patch (render/compile-patch fixtures))
(defn slot [^bytes data i] (bit-and 255 (aget data (int i))))

(defn launch [ids]
  (let [effects {:reactive {:id :reactive :version 1 :params {} :layer {:transforms []}}
                 :predictive {:id :predictive :version 1 :params {} :keyframes {:interval {:beats 1/2}}}}
        cues (into {} (map (fn [id] [id {:id id :version 1 :effect-id id}]) ids))]
    (reduce (fn [model cue]
              (let [result (control/apply-command model {:op :cue/launch :cue-id cue :time-ms 0 :source :capture
                                                         :command-id (str "capture-launch-" (name cue))
                                                         :show-id (:show-id model) :epoch (:epoch model)})]
                (assert (= :accepted (get-in result [:ack :status])))
                (:model result)))
            (control/new-show {:registry {:effects effects :cues cues}}) ids)))

(defn field [components entries]
  {:type (if (= components 3) :vec3 :number) :components components :values (double-array entries)})

(defn block [fields]
  {:kind :batch :batch {:target-ids ids :count (count ids) :outputs fields}})

(defn read-field [frame id field]
  (first (:result (keyframes/inspect (get-in frame [:keyframes id]) (first ids) field))))

(def source-path "/workspace/artifacts/afterglow-reactive-effect-settling-534/trace.csv")

(defn captured-inputs []
  (let [[header & rows] (str/split-lines (slurp source-path))
        columns (mapv keyword (str/split header #","))]
    (mapv (fn [row]
            (let [data (zipmap columns (str/split row #"," -1))]
              (reduce (fn [data col] (update data col parse-double)) data
                      [:beat :time_ms :level :bias :declared_ratio :native_level :native_ratio]))) rows)))

(defn write-native! [^DataOutputStream writer frame]
  (doseq [{:keys [batch]} (:contributions frame)
          [attr {:keys [values]}] (sort-by key (:outputs batch))]
    (let [^doubles xs values]
      (.writeUTF writer (name attr))
      (.writeInt writer (alength xs))
      (dotimes [i (alength xs)]
        (.writeLong writer (Double/doubleToRawLongBits (aget xs i)))))))

(defn capture! [prefix]
  (let [state (launch [:reactive :predictive])
        calculations (volatile! 0)
        predictions (volatile! 0)
        stats (volatile! {})
        react (keyframes/dependency-driven
               {:inputs [:level :profile] :transition {:beats 1}}
               (fn [{:keys [level profile]}]
                 (vswap! calculations inc)
                 {:contributions [(block {:dimmer (field 1 (map #(* (+ level (:bias profile)) (- 1.0 (/ % 100.0))) (range 64)))
                                          :beat-ratio (field 1 (repeat 64 (:ratio profile)))})]}))
        predict (keyframes/predictable
                 (fn [{:keys [frame] :as ctx}]
                   (vswap! predictions inc)
                   (let [phase (/ (+ 1.0 (Math/sin (* (double (:beat frame)) 1.6))) 2.0)]
                     (runtime/append-contributions ctx
                       [(block {:color (field 3 (mapcat (fn [i] [(* 0.4 phase) (/ i 64.0) (- 1.0 phase)]) (range 64)))
                                :focus (field 1 (repeat 64 phase)) :zoom (field 1 (repeat 64 (- 1.0 phase)))})]))))
        column-var (ns-resolve 'afterglow.runtime.keyframes.values 'valid-column?)
        original @column-var
        record-validation (fn [attr ^doubles xs hdr?]
                            (vswap! stats update attr (fnil + 0) (alength xs))
                            (original attr xs hdr?))
        compiled (fn [{:keys [id]}] (case id :reactive react :predictive predict))]
    (with-open [writer (io/writer (str prefix "-trace.csv"))
                packed (DataOutputStream. (BufferedOutputStream. (io/output-stream (str prefix "-dmx.bin"))))
                native (DataOutputStream. (BufferedOutputStream. (io/output-stream (str prefix "-native.bin"))))]
      (.write writer "frame,beat,time_ms,event,dimmer,ratio,red,green,blue,focus,dmx_coarse,dmx_fine,calculations,predictions\n")
      (let [result (with-redefs-fn {column-var record-validation}
                     #(reduce
                       (fn [previous {:keys [frame beat time_ms event level bias declared_ratio native_level native_ratio]}]
                         (let [beat (double beat)
                               model (assoc-in (or (:model previous) state) [:transport :beat] beat)
                               output (engine/advance model {:time-ms time_ms :keyframes (:keyframes previous)
                                                            :reactive-inputs {:level level :profile {:bias bias :ratio declared_ratio}}
                                                            :fixtures fixtures} compiled)
                               stream (:contributions output)
                               rich (render/resolve-contributions patch stream)
                               compact (render/resolve-contributions patch stream {:include-values? false :compact-values? true})
                               ^bytes bytes (get-in rich [:universes 1])
                               dimmer (read-field output "0:1" :dimmer)
                               ratio (read-field output "0:1" :beat-ratio)
                               preview (get-in rich [:values (first ids)])]
                           (assert (empty? (:fault-events output)))
                           (assert (= 2 (count stream) (count (:keyframes output))))
                           (assert (= 512 (alength bytes)))
                           (assert (Arrays/equals bytes ^bytes (get-in compact [:universes 1])))
                           (assert (= (Double/doubleToRawLongBits dimmer) (Double/doubleToRawLongBits native_level)))
                           (assert (== ratio native_ratio))
                           (assert (== dimmer (:dimmer preview)))
                           (.write packed bytes)
                           (write-native! native output)
                           (.write writer ^String (str (str/join "," [frame beat time_ms event dimmer ratio
                                                                       (slot bytes 2) (slot bytes 3) (slot bytes 4)
                                                                       (read-field output "0:2" :focus)
                                                                       (slot bytes 0) (slot bytes 1) @calculations @predictions]) "\n"))
                           output)) nil (captured-inputs)))
            checked (reduce + (vals @stats))]
        (assert (= 3 @calculations))
        (assert (get-in result [:keyframes "0:1" :settled?]))
        (assert (pos? checked))
        (prn {:input-frames (count (captured-inputs)) :fixtures (count fixtures)
              :fixture-dmx-bytes-per-frame 512 :reactive-calculations @calculations
              :predictive-calculations @predictions :validated-components @stats
              :total-validated-components checked :last-frame (:frame-number result)})))))

(apply capture! *command-line-args*)
