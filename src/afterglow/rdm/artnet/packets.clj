(ns afterglow.rdm.artnet.packets
  "Art-Net 4 table-of-devices and E1.20 message encoding. Octets are unsigned."
  (:require [afterglow.rdm.codec :as rdm]
            [clojure.string :as str]))

(def ^:private id [65 114 116 45 78 101 116 0])

(def tod-request 0x8000)

(def tod-data 0x8100)

(def tod-control 0x8200)

(def art-rdm 0x8300)

(defn- route [universe]
  (when-not (and (integer? universe) (<= 1 universe 32768))
    (rdm/fail! "Art-Net universes range from 1 to 32768" {:universe universe}))
  (rdm/uint16-bytes (dec universe)))

(defn- header [opcode universe version]
  (let [[net _] (route universe)]
    (into id [(bit-and opcode 255) (bit-shift-right opcode 8) 0 14
              version 0 0 0 0 0 0 0 0 net])))

(defn- received? [packet opcode universe]
  (let [[net address] (route universe)]
    (and (<= 24 (count packet))
         (= id (subvec packet 0 8))
         (= opcode (+ (packet 8) (bit-shift-left (packet 9) 8)))
         (<= 14 (rdm/u16 packet 10))
         (= 1 (packet 12))
         (= net (packet 21))
         (= address (packet 23)))))

(defn discovery-packet [universe full?]
  (let [[_ address] (route universe)]
    (if full?
      (into (header tod-control universe 0) [1 address])
      ;; The Address[32] field has one used entry and 31 unused slots.
      (into (header tod-request universe 0) (concat [0 1 address] (repeat 31 0))))))

(defn individual-uid [value]
  (let [uid (rdm/uid value)]
    (when (or (= uid "0000:00000000") (str/ends-with? uid ":ffffffff") (str/starts-with? uid "ffff:"))
      (rdm/fail! "RDM requires an individual device UID" {:uid uid}))
    uid))

(defn- uid-bytes [value]
  (->> (str/replace (individual-uid value) ":" "")
       (re-seq #"..")
       (mapv #(Integer/parseInt % 16))))

(defn- read-uid [packet offset]
  (let [manufacturer (rdm/u16 packet offset)
        serial (reduce #(+ (bit-shift-left %1 8) %2) 0 (subvec packet (+ 2 offset) (+ 6 offset)))]
    (format "%04x:%08x" manufacturer serial)))

(defn read-tod [packet universe bind-index physical-port]
  (when (and (received? packet tod-data universe)
             (= physical-port (packet 13)) (= bind-index (packet 20)))
    (when (< (count packet) 28) (rdm/fail! "Truncated ArtTodData header" {}))
    (case (packet 22)
      255 :incomplete
      0 (let [total (rdm/u16 packet 24) block (packet 26) cnt (packet 27)]
          (when-not (and (<= cnt 200) (<= cnt total 512) (= (count packet) (+ 28 (* cnt 6)))
                         (if (zero? total) (zero? block) (pos? cnt)))
            (rdm/fail! "Invalid ArtTodData block size" {:block block :total total :count cnt}))
          {:total total :block block
           :uids (mapv #(individual-uid (read-uid packet %)) (range 28 (count packet) 6))})
      (rdm/fail! "Unknown ArtTodData response" {:response (packet 22)}))))

(defn add-block [{:keys [blocks total]} {:keys [block uids] :as packet}]
  (when (or (and total (not= total (:total packet)))
            (and (contains? blocks block) (not= (get blocks block) uids)))
    (rdm/fail! "Conflicting ArtTodData blocks" {:block block}))
  (let [blocks (assoc blocks block uids)
        all (mapcat val (sort-by key blocks))
        n (count all)
        total (:total packet)]
    (when (or (> n total) (not= n (count (set all))))
      (rdm/fail! "ArtTodData contains overlapping UIDs" {:total total}))
    (when (and (= n total) (not= (set (keys blocks)) (set (range (count blocks)))))
      (rdm/fail! "ArtTodData block indices have gaps" {}))
    (cond-> {:total total :blocks blocks}
      (= n total) (assoc :uids (vec all)))))

(defn- checksum [message]
  ;; The ArtRdm payload omits the DMX start code, which still counts in E1.20.
  (bit-and 0xffff (reduce + 0xcc message)))

(defn command-packet [controller transaction request]
  (let [{:keys [uid pid sub-device command data universe]} (rdm/validate-command request)
        [_ address] (route universe)
        destination (uid-bytes uid)
        source (uid-bytes controller)]
    (when (= source destination) (rdm/fail! "Controller and responder must have distinct UIDs" {:uid uid}))
    (when-not (rdm/uint? 8 transaction) (rdm/fail! "Invalid RDM transaction number" {}))
    (let [message (vec (concat [1 (+ 24 (count data))] destination source [transaction 1 0]
                               (rdm/uint16-bytes sub-device) [(if (= command :get) 0x20 0x30)]
                               (rdm/uint16-bytes pid) [(count data)] data))]
      (into (header art-rdm universe 1) (concat [0 address] message (rdm/uint16-bytes (checksum message)))))))

(defn read-response [packet controller transaction {:keys [universe uid command sub-device pid]}]
  (when (and (received? packet art-rdm universe) (= 0 (packet 22)) (<= 47 (count packet))
             (= controller (read-uid packet 26)) (= uid (read-uid packet 32))
             (= transaction (packet 38))
             (#{0x21 0x31} (packet 43)))
    (let [pdl (packet 46)
          end (+ 47 pdl)
          actual-pid (rdm/u16 packet 44)
          actual-sub (rdm/u16 packet 41)
          class (if (= 0x21 (packet 43)) 0 1)
          queued? (and (= pid 0x20) (= command :get))]
      (when (or queued? (and (= pid actual-pid) (= sub-device actual-sub) (= class (if (= command :set) 1 0))))
        (when-not (and (= 1 (packet 24)) (= (+ 24 pdl) (packet 25)) (= (+ 2 end) (count packet))
                       (= (checksum (subvec packet 24 end)) (rdm/u16 packet end)) (<= (packet 39) 3))
          (rdm/fail! "Invalid E1.20 response framing, checksum or response type" {:transaction transaction}))
        {:response-code 0 :response-type (packet 39) :message-count (packet 40)
         :pid actual-pid :sub-device actual-sub :command-class class :source-uid uid
         :data (subvec packet 47 end)}))))
