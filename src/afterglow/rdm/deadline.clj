(ns afterglow.rdm.deadline
  (:import [java.net SocketTimeoutException]))

(defn remaining-ms [deadline]
  (let [remaining (- deadline (System/nanoTime))]
    (when-not (pos? remaining) (throw (SocketTimeoutException. "RDM job deadline exceeded")))
    (long (max 1 (Math/ceil (/ remaining 1.0e6))))))
