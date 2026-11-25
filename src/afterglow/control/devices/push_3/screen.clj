(ns afterglow.control.devices.push-3.screen
  "Tethered Push 3 display format and descriptor checks. Pure functions do no USB IO."
  (:import [java.awt AlphaComposite]
           [java.awt.image BufferedImage DataBufferInt]
           [java.nio ByteBuffer ByteOrder]))

(def ^:const width 960)

(def ^:const height 160)

(def ^:const stride 2048)

(def ^:const payload-length (* height stride))

(def vendor 0x2982)

(def product 0x1969)

(def interface-number 0)

(def endpoint 0x01)

(def display-name "Ableton Push 3 Display")

(defn header []
  (byte-array (map unchecked-byte [0xff 0xcc 0xaa 0x88 0 0 0 0 0 0 0 0 0 0 0 0])))

(defn buffers []
  (let [wire (byte-array payload-length)
        buffer (doto (ByteBuffer/wrap wire) (.order ByteOrder/LITTLE_ENDIAN))
        raster (BufferedImage. width height BufferedImage/TYPE_INT_RGB)
        pixels (.getData ^DataBufferInt (.getDataBuffer (.getRaster raster)))]
    ;; 64 invisible BGR565 pixels per row, black before signal shaping.
    (dotimes [i (quot payload-length 4)]
      (.putInt buffer (int (* i 4)) (unchecked-int 0xffe7f3e7)))
    {:raster raster :pixels pixels :wire wire :buffer buffer}))

(defn encode!
  "Fill the caller's reusable payload from an opaque, native-size browser raster."
  [{:keys [raster pixels wire buffer]} ^BufferedImage image]
  (when-not (and (instance? BufferedImage image) (= width (.getWidth image)) (= height (.getHeight image)))
    (throw (ex-info "Push 3 display requires a 960×160 BufferedImage" {})))
  (let [^ints pixels pixels ^ByteBuffer buffer buffer]
    ;; ImageIO commonly produces TYPE_3BYTE_BGR. Java2D's native blit converts
    ;; the whole raster in one pass, avoiding per-pixel getRGB colour conversion.
    (let [graphics (.createGraphics ^BufferedImage raster)]
      (try
        (.setComposite graphics AlphaComposite/Src)
        (.drawImage graphics image 0 0 nil)
        (finally (.dispose graphics))))
    (dotimes [y height]
      (let [src (* y width) dst (* y stride)]
        (dotimes [x width]
          (let [rgb (aget pixels (+ src x))
                value (bit-or (bit-shift-left (bit-and rgb 0xf8) 8)
                              (bit-and (unsigned-bit-shift-right rgb 5) 0x07e0)
                              (bit-and (unsigned-bit-shift-right rgb 19) 31))
                offset (+ dst (* 2 x))]
            (.putShort buffer (int offset)
                       (unchecked-short (bit-xor value (if (zero? (bit-and x 1)) 0xf3e7 0xffe7))))))))
    wire))

(defn- u8 [^bytes bytes i] (bit-and 0xff (aget bytes i)))

(defn- u16 [^bytes bytes i] (+ (u8 bytes i) (* 256 (u8 bytes (inc i)))))

(defn configuration
  "Parse standard USB configuration bytes, skipping class-specific descriptors.
  Invalid lengths fail before any interface can be selected."
  [^bytes b]
  (let [size (alength b) invalid #(throw (ex-info "Malformed USB configuration descriptor" {}))]
    (when-not (and (<= 9 size 4096) (= 9 (u8 b 0)) (= 2 (u8 b 1)) (= size (u16 b 2))) (invalid))
    (loop [i 9 interfaces []]
      (if (= i size)
        {:configuration (u8 b 5) :interfaces interfaces}
        (let [_ (when (> (+ i 2) size) (invalid))
              n (u8 b i) kind (u8 b (inc i))
              _ (when (or (< n 2) (> (+ i n) size)) (invalid))
              next-interfaces
              (case kind
                4 (do (when (< n 9) (invalid))
                      (conj interfaces {:interface (u8 b (+ i 2)) :alternate (u8 b (+ i 3))
                                        :endpoints-count (u8 b (+ i 4))
                                        :class (mapv #(u8 b (+ i %)) [5 6 7])
                                        :name-index (u8 b (+ i 8)) :endpoints []}))
                5 (do (when (or (< n 7) (empty? interfaces)) (invalid))
                      (update-in interfaces [(dec (count interfaces)) :endpoints] conj
                                 [(u8 b (+ i 2)) (bit-and 3 (u8 b (+ i 3))) (u16 b (+ i 4))]))
                interfaces)]
          (recur (+ i n) next-interfaces))))))

(defn candidate
  "Return only the independently observed display descriptor. Audio, MIDI, xPort,
  ambiguous alternates and other devices are never candidates."
  [{:keys [vendor-id product-id]} active configuration]
  (let [matches (filter #(zero? (:interface %)) (:interfaces configuration))
        {:keys [class endpoints endpoints-count alternate name-index] :as display} (first matches)]
    (when (and (= vendor vendor-id) (= product product-id)
               (= 1 active (:configuration configuration)) (= 1 (count matches))
               (= 0 alternate) (= [255 255 255] class) (pos? name-index)
               (= 2 endpoints-count (count endpoints)) (= #{[1 2 512] [129 2 512]} (set endpoints)))
      display)))
