(ns afterglow.rdm.transport
  "Owned, cancellable RDM job connections and shared E1.20 command handling."
  (:require [afterglow.rdm.artnet :as artnet]
            [afterglow.rdm.codec :as codec]
            [afterglow.rdm.deadline :as deadline]
            [afterglow.rdm.ola :as ola])
  (:import [java.net SocketTimeoutException]))

(def remaining-ms deadline/remaining-ms)

(defn open!
  "Open the configured RDM transport for one job. OLA is the default."
  [{:keys [transport] :as config} deadline register!]
  (case transport
    (nil :ola) (ola/open! config deadline register!)
    :art-net (artnet/open! config deadline register!)
    (codec/fail! "Unknown RDM transport" {:transport transport})))

(def nack-reasons
  {0 :unknown-pid 1 :format-error 2 :hardware-fault 3 :proxy-reject 4 :write-protect
   5 :unsupported-command-class 6 :data-out-of-range 7 :buffer-full 8 :packet-size-unsupported
   9 :sub-device-out-of-range 10 :proxy-buffer-full 11 :action-not-supported})

(defn- matches? [command response]
  (and (= (:pid command) (:pid response))
       (= (:sub-device command) (:sub-device response))
       (= (if (= :set (:command command)) 1 0) (:command-class response))))

(defn- reply-word [response]
  (when-not (= 2 (count (:data response)))
    (codec/fail! "RDM timer or NACK must contain a 16-bit value" {}))
  (codec/u16 (:data response) 0))

(defn- wait-timer! [response check-current!]
  (let [delay-ms (* 100 (reply-word response))
        until (+ (System/nanoTime) (* delay-ms 1000000))]
    (when (>= delay-ms (check-current!))
      (throw (SocketTimeoutException. "RDM ACK_TIMER exceeds job deadline")))
    ;; The transport socket may already have closed on cancellation. Check the
    ;; session while waiting, too, so the IO worker is promptly released.
    (loop []
      (check-current!)
      (let [remaining (- until (System/nanoTime))]
        (when (pos? remaining)
          (.sleep java.util.concurrent.TimeUnit/NANOSECONDS (min remaining 20000000))
          (recur))))))

(defn command!
  "Resolve ACK_TIMER by bounded QUEUED_MESSAGE polling. The selected transport owns
  ACK_OVERFLOW assembly and transaction validation. Never re-send a delayed SET."
  [request! request deadline current?]
  (let [request (codec/validate-command request)
        query (assoc request :pid 0x20 :command :get :data [1] :sub-device 0)
        check-current! (fn []
                         (when-not (current?)
                           (throw (ex-info "RDM job cancelled or session changed" {:rdm/error :cancelled})))
                         (remaining-ms deadline))]
    (loop [attempt 0]
      (check-current!)
      (when (>= attempt 32)
        (throw (ex-info "RDM queued reply limit exceeded" {:rdm/error :queue-limit})))
      (let [queued? (pos? attempt)
            response (request! "RDMCommand" (if queued? query request))
            type (:response-type response)
            original? (matches? request response)
            queue-command? (and queued? (matches? query response))]
        (check-current!)
        (cond
          (not= 0 (:response-code response)) (assoc response :status :transport-error)
          (not (#{0 1 2} type)) (codec/fail! "Unknown RDM response type" {:response response})
          (and (not queued?) (not original?))
          (codec/fail! "RDM response does not match the command" {:response response})

          (and original? (zero? type)) (assoc response :status :ack)
          (and (= type 2) (or original? queue-command?))
          (let [code (reply-word response)]
            (assoc response :status (if original? :nack :queue-nack)
                   :nack-code code :reason (get nack-reasons code :unknown)))

          :else
          (do (when (and (= type 1) (or original? queue-command?))
                (wait-timer! response check-current!))
              (recur (inc attempt))))))))
