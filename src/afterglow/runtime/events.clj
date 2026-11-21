(ns afterglow.runtime.events
  "Frame-local immutable staging for domain events. Successful reducers thread
  this entry through the same candidate model as their updates. Discarding a
  candidate therefore discards its events. Remove the entry before publication.")

(defn begin [model] (assoc model ::pending []))

(defn collect [model category emitter events]
  (if (and (contains? model ::pending) (seq events))
    (update model ::pending into
            (map (fn [event] {:category category :emitter emitter :event event}))
            events)
    model))

(defn pending [model] (::pending model []))

(defn finish [model] (dissoc model ::pending))
