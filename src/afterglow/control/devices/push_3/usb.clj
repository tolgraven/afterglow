(ns afterglow.control.devices.push-3.usb
  "Explicit, tethered display access through the platform's libusb 1.0.
  Enumeration reads cached USB device descriptors. Opening checks only the selected
  Push 3's active configuration and name, then claims only its display interface."
  (:require [afterglow.control.devices.push-3.screen :as screen]
            [clojure.java.io :as io])
  (:import [com.sun.jna Function Memory Native NativeLibrary Pointer]
           [com.sun.jna.ptr IntByReference PointerByReference]
           [java.nio.charset StandardCharsets]))

(defn- api [library]
  (let [library (or library (some #(when (.isFile (io/file %)) %)
                                  ["/opt/homebrew/lib/libusb-1.0.dylib" "/usr/local/lib/libusb-1.0.dylib"])
                    "usb-1.0")
        native (NativeLibrary/getInstance ^String library)]
    (into {} (map (fn [op] [op (.getFunction native (str "libusb_" (name op)))]))
          [:init :exit :get_device_list :free_device_list :get_device_descriptor
           :get_bus_number :get_device_address :open :close :get_configuration
           :control_transfer :get_string_descriptor_ascii :claim_interface :release_interface
           :bulk_transfer])))

(defn- int-call [usb op & args] (.invokeInt ^Function (usb op) (object-array args)))
(defn- void-call [usb op & args] (.invokeVoid ^Function (usb op) (object-array args)))
(defn- check [op result]
  (when (neg? result)
    (throw (ex-info (str "Push 3 USB " (name op) " failed (" result ")") {:operation op :libusb-code result})))
  result)

(defn- context [usb]
  (let [out (PointerByReference.)]
    (check :init (int-call usb :init out))
    (.getValue out)))

(defn- device-info [usb device ^Memory descriptor]
  (check :descriptor (int-call usb :get_device_descriptor device descriptor))
  (let [vendor (bit-and 0xffff (.getShort descriptor 8)) product (bit-and 0xffff (.getShort descriptor 10))]
    (when (and (= vendor screen/vendor) (= product screen/product))
      {:vendor-id vendor :product-id product :configurations (bit-and 255 (.getByte descriptor 17))
       :bus (bit-and 255 (int-call usb :get_bus_number device))
       :address (bit-and 255 (int-call usb :get_device_address device))})))

(defn- with-devices [usb ctx f]
  (let [out (PointerByReference.) fn-list ^Function (:get_device_list usb)
        args (object-array [ctx out])
        n (check :enumeration (if (= 8 Native/POINTER_SIZE) (.invokeLong fn-list args) (.invokeInt fn-list args)))
        ^Pointer devices (.getValue out)]
    (try
      (with-open [descriptor (Memory. 18)]
        (f (into [] (keep (fn [i]
                            (let [d (.getPointer devices (* i Native/POINTER_SIZE))]
                              (when-let [info (device-info usb d descriptor)] [info d]))))
                 (range n))))
      (finally (void-call usb :free_device_list devices (int 1))))))

(defn locations
  "Read locations of tethered Push 3 devices. No device or USB interface is claimed."
  ([] (locations {}))
  ([{:keys [library]}]
   (let [usb (api library) ctx (context usb)]
     (try (with-devices usb ctx #(mapv first %)) (finally (void-call usb :exit ctx))))))

(defn- config-bytes [usb handle]
  ;; Standard GET_DESCRIPTOR(CONFIGURATION, index 0). The known device has
  ;; exactly one configuration; we never set it or switch an alternate setting.
  (let [read! (fn [length]
                (let [b (byte-array length)
                      n (check :read-configuration
                               (int-call usb :control_transfer handle (unchecked-byte 0x80) (byte 6)
                                         (short 0x200) (short 0) b (short length) (int 400)))]
                  (when-not (= length n) (throw (ex-info "Incomplete USB configuration descriptor" {:read n})))
                  b))
        ^bytes header (read! 9)
        size (+ (bit-and 255 (aget header 2)) (* 256 (bit-and 255 (aget header 3))))]
    (when-not (<= 9 size 4096) (throw (ex-info "Unexpected Push 3 configuration length" {:bytes size})))
    (read! size)))

(defn- interface-name [usb handle index]
  (let [b (byte-array 256)
        n (check :read-name (int-call usb :get_string_descriptor_ascii handle (unchecked-byte index) b (int 256)))]
    (String. b 0 n StandardCharsets/US_ASCII)))

(defn- verify! [usb handle info]
  (let [active (IntByReference.)]
    (check :active-configuration (int-call usb :get_configuration handle active))
    (let [layout (screen/configuration (config-bytes usb handle))
          display (screen/candidate info (.getValue active) layout)]
      (when-not (and display (= screen/display-name (interface-name usb handle (:name-index display))))
        (throw (ex-info "Selected device does not match the tethered Push 3 display descriptor" info)))
      {:device info :configuration (:configuration layout) :interfaces (:interfaces layout)
       :display (assoc display :name screen/display-name)})))

(defn- open-device [usb ctx bus address]
  (with-devices usb ctx
    (fn [entries]
      (let [[info device] (first (filter (fn [[d _]] (= [bus address] [(:bus d) (:address d)])) entries))
            out (PointerByReference.)]
        (when-not (and device (= 1 (:configurations info)))
          (throw (ex-info "Selected tethered Push 3 is unavailable" {:bus bus :address address})))
        (check :open (int-call usb :open device out))
        [info (.getValue out)]))))

(defn- acquire [options claim?]
  (let [{:keys [bus address library]} options]
    (when-not (and (integer? bus) (<= 0 bus 255) (integer? address) (<= 1 address 127))
      (throw (ex-info "Choose a Push 3 bus and address from locations" {})))
    (let [usb (api library) ctx (context usb)]
      (try
        (let [[info handle] (open-device usb ctx bus address)]
          (try (let [descriptor (verify! usb handle info)]
                 (when claim? (check :claim (int-call usb :claim_interface handle (int screen/interface-number))))
                 {:usb usb :ctx ctx :device handle :descriptor descriptor :claimed? claim?})
               (catch Throwable e (void-call usb :close handle) (throw e))))
        (catch Throwable e (void-call usb :exit ctx) (throw e))))))

(defn close! [{:keys [usb ctx device claimed?]}]
  (try (when claimed? (check :release (int-call usb :release_interface device (int screen/interface-number))))
       (finally (try (void-call usb :close device) (finally (void-call usb :exit ctx))))))

(defn inspect
  "Read the selected unit's standard descriptors without claiming the display."
  [options]
  (let [handle (acquire options false)]
    (try (:descriptor handle) (finally (close! handle)))))

(defn open! [options] (acquire options true))

(defn write! [{:keys [usb device]} ^bytes data]
  (let [actual (IntByReference.) expected (alength data)]
    (check :bulk-out (int-call usb :bulk_transfer device (byte screen/endpoint) data
                               (int expected) actual (int 400)))
    (when-not (= expected (.getValue actual))
      (throw (ex-info "Incomplete Push 3 display transfer" {:expected expected :transferred (.getValue actual)})))))
