(ns afterglow.render.gpu.lifecycle
  "Native owner teardown shared by the expression and moving-head workers.")

(defn finish! [done cleanup!]
  ;; ThreadPoolExecutor calls terminated under its own lock, sometimes on the
  ;; close! caller. Relinquish that lock before a driver can block destruction.
  (let [run (fn [] (deliver done (try (cleanup!) nil (catch Throwable error error))))]
    (doto (Thread. ^Runnable run "afterglow-gpu-cleanup")
      (.setDaemon true)
      (.start))))
