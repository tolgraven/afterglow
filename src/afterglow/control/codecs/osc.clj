(ns afterglow.control.codecs.osc
  "Pure translation of decoded OSC messages through explicit trusted mappings.
  This namespace does not parse network packets, listen, send, read clocks or eval.")

(defn- invalid! [message data]
  (throw (ex-info message (assoc data :type ::invalid-message))))

(defn- finite? [value]
  (and (number? value) (Double/isFinite (double value))))

(defn command
  "Translate {:path string :args vector} using a path->mapping map and an explicit
  command envelope. Unknown paths return nil. Supported mappings contain :op and
  its fixed target (:cue-id, :instance-id, :param), plus optional :launch/:force?.
  Launch/end take no args. A launch with :priority-arg? true takes one finite
  priority and uses it as :launch :priority. Parameter, priority, master and
  blackout set take exactly one arg.
  The caller assigns unique IDs and logical time; no IDs or time are fabricated."
  [mappings {:keys [path args] :as message} envelope]
  (when-not (and (map? mappings) (map? message) (string? path)
                 (.startsWith ^String path "/") (vector? args))
    (invalid! "Expected an OSC path and argument vector" {:message message}))
  (when-let [{:keys [op cue-id instance-id param launch force?] :as mapping} (get mappings path)]
    (when-not (and (map? mapping) (map? envelope)
                   (every? #(contains? envelope %) [:command-id :show-id :epoch :source :time-ms])
                   (some? (:command-id envelope)) (some? (:show-id envelope))
                   (integer? (:epoch envelope)) (not (neg? (:epoch envelope)))
                   (finite? (:time-ms envelope)) (not (neg? (:time-ms envelope))))
      (invalid! "OSC command requires an explicit identity, epoch, source and logical time"
                {:path path}))
    (let [launch-priority? (and (= :cue/launch op) (true? (:priority-arg? mapping)))
          priority? (or launch-priority? (= :instance/set-priority op))
          expected (if (or priority? (#{:param/set :master/set :blackout/set} op)) 1 0)
          value (first args)]
      (when-not (= expected (count args))
        (invalid! "Wrong OSC argument count" {:path path :expected expected :actual (count args)}))
      (when (and priority? (not (finite? value)))
        (invalid! "OSC priority must be finite" {:path path :value value}))
      (merge (select-keys envelope [:command-id :show-id :epoch :source :time-ms
                                    :expected-revision :gesture-id])
             (case op
               :cue/launch
               (do (when-not (some? cue-id) (invalid! "Cue mapping requires :cue-id" {:path path}))
                   (when (and launch-priority? (some? launch) (not (map? launch)))
                     (invalid! "Launch options must be a map" {:path path}))
                   (cond-> {:op op :cue-id cue-id}
                     launch (assoc :launch launch)
                     launch-priority? (assoc-in [:launch :priority] value)))
               :instance/set-priority
               (do (when-not (some? instance-id) (invalid! "Priority mapping requires :instance-id" {:path path}))
                   {:op op :instance-id instance-id :priority value})
               :instance/end
               (do (when-not (some? instance-id) (invalid! "End mapping requires :instance-id" {:path path}))
                   (cond-> {:op op :instance-id instance-id}
                     (contains? mapping :force?) (assoc :force? force?)))
               :param/set
               (do (when-not (and (some? instance-id) (keyword? param))
                     (invalid! "Parameter mapping requires :instance-id and keyword :param" {:path path}))
                   ;; Typed/range validation belongs to the shared parameter schema.
                   {:op op :instance-id instance-id :param param :value value})
               :master/set
               (do (when-not (and (finite? value) (<= 0 value 1))
                     (invalid! "Master OSC value must be finite in [0,1]" {:path path :value value}))
                   {:op op :value value})
               :blackout/set
               (let [value (cond
                             (and (number? value) (zero? value)) false
                             (and (number? value) (== value 1)) true
                             :else value)]
                 (when-not (instance? Boolean value)
                   (invalid! "Blackout OSC value must be boolean, 0 or 1" {:path path :value value}))
                 {:op op :value value})
               (invalid! "Unsupported OSC command mapping" {:path path :op op}))))))
