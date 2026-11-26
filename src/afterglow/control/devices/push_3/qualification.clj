(ns afterglow.control.devices.push-3.qualification
  "Explicit CLI for the tethered Push 3. list, inspect and timing never claim an
  interface. show-chart prints its refresh receipt as EDN after closing."
  (:require [afterglow.control.devices.push-3.usb :as usb]
            [afterglow.control.devices.push-3.display :as display])
  (:import [java.awt Color Font]
           [java.awt.image BufferedImage]))

(defn chart []
  (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        graphics (.createGraphics image)
        swatches [["RED" Color/RED Color/WHITE] ["GREEN" Color/GREEN Color/BLACK]
                  ["BLUE" Color/BLUE Color/WHITE] ["WHITE" Color/WHITE Color/BLACK]]]
    (try
      (.setFont graphics (Font. Font/MONOSPACED Font/BOLD 21))
      (doseq [[index [label color ink]] (map-indexed vector swatches)]
        (let [x (* 240 index)]
          (.setColor graphics color)
          (.fillRect graphics x 0 240 160)
          (.setColor graphics ink)
          (.drawString graphics ^String label (int (+ x 12)) (int 36))))
      (.setColor graphics Color/BLACK)
      (.drawRect graphics 0 0 959 159)
      (.drawString graphics "BOTTOM RIGHT" (int 785) (int 147))
      image
      (finally (.dispose graphics)))))

(defn- millis [start-ns] (/ (- (System/nanoTime) start-ns) 1e6))

(defn observe!
  "Claim the display, show the chart for seconds and return the refresh receipt."
  [options seconds]
  (when-not (and (integer? seconds) (<= 1 seconds 30))
    (throw (ex-info "Use a whole duration from 1 to 30 seconds" {})))
  (let [sink (display/sink options)
        handle ((:open! sink))]
    (try
      ((:render! sink) handle (chart))
      (Thread/sleep (* 1000 seconds))
      (when-let [failure (:failure @(:state handle))] (throw failure))
      (finally ((:close! sink) handle)))
    (display/refresh-receipt handle)))

(defn timing
  "Measure the shared libusb context and repeated read-only access in one process:
  the first scan, then list and inspect twice. Nothing is claimed or sent."
  [options]
  (let [context (usb/prepare! options)
        step (fn [f] (let [start (System/nanoTime) result (f)] [result (millis start)]))
        [found list-ms] (step #(usb/locations options))
        [_ inspect-ms] (step #(usb/inspect options))
        [_ again-ms] (step #(usb/inspect options))]
    {:context context :locations found :list-ms list-ms :inspect-ms [inspect-ms again-ms]}))

(defn -main [& args]
  (let [[command bus address duration] args
        options {:bus (some-> bus parse-long) :address (some-> address parse-long)}]
    (case [command (count args)]
      ["list" 1] (prn (usb/locations))
      ["inspect" 3] (prn (usb/inspect options))
      ["timing" 3] (prn (timing options))
      ["show-chart" 4] (prn (observe! options (parse-long duration)))
      (throw (ex-info "Use list, inspect BUS ADDRESS, timing BUS ADDRESS or show-chart BUS ADDRESS SECONDS" {})))))
