(ns afterglow.render.fog-law)

(defn optical-depth
  "Apply the same nonnegative factors to numeric samples and to material
  expressions. Extinction is per metre, density is relative, distance is metres."
  [nonnegative product extinction density distance]
  (product (nonnegative extinction) (nonnegative density) (nonnegative distance)))
