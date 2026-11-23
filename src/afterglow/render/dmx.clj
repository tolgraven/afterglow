(ns afterglow.render.dmx
  "Quantization shared by continuous channels and profiles with physical coarse-byte ranges.")

(defn fine-word ^long [^double coarse-units coarse-range?]
  (if coarse-range?
    (let [coarse (long coarse-units)]
      (bit-or (bit-shift-left coarse 8) (Math/round (* 255.0 (- coarse-units coarse)))))
    (Math/round (* 257.0 coarse-units))))

(defn coarse-units
  "Decode unsigned high and low bytes into the same 0..255 units as the channel inversion pivot."
  ^double [^long high ^long low coarse-range?]
  (if coarse-range?
    (min 255.0 (+ high (/ low 255.0)))
    (/ (+ (bit-shift-left high 8) low) 257.0)))
