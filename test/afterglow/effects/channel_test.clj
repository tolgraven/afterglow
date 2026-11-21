(ns afterglow.effects.channel-test
  (:require [clojure.test :refer :all]
            [afterglow.effects :as fx]
            [afterglow.effects.channel :as channel]
            [afterglow.util :as util]))

(deftest channel-packing-preserves-universe-and-byte-order
  (let [buffers {1 (byte-array 512) 2 (byte-array 512)}]
    (channel/apply-channel-value buffers {:universe 1 :index 511} 255)
    (channel/apply-channel-value buffers {:universe 2 :index 0 :fine-index 1} 127.5)
    (is (= 255 (util/unsign (aget (get buffers 1) 511))))
    (is (= [127 128] (mapv util/unsign (take 2 (get buffers 2)))))
    (is (every? zero? (take 511 (get buffers 1))))
    (is (every? zero? (drop 2 (get buffers 2))))))

(deftest coarse-channel-rounding-and-inversion-remain-compatible
  (doseq [[value options expected] [[12.49 {} 12] [12.5 {} 13]
                                    [0 {:inverted-from 0} 255]
                                    [255 {:inverted-from 0} 0]
                                    [0 {:inverted-from 1} 0]
                                    [1 {:inverted-from 1} 255]
                                    [255 {:inverted-from 1} 1]]]
    (let [buffer (byte-array 512)]
      (channel/apply-channel-value {1 buffer} (merge {:universe 1 :index 0} options) value)
      (is (= expected (util/unsign (aget buffer 0)))))))

(deftest channel-assignment-resolution-clamps-output
  (let [target {:universe 1 :address 1 :index 0}
        buffer (byte-array 512)]
    (doseq [[value expected] [[-20 0] [420 255]]]
      (fx/resolve-assignment (fx/->Assignment :channel [1 1] target value) {} {} {1 buffer})
      (is (= expected (util/unsign (aget buffer 0))))))
  (is (nil? (channel/apply-channel-value {} {:universe 42 :index 0} 128))))

(deftest highest-and-latest-priority-have-distinct-blending-semantics
  (let [target {:universe 1 :address 1 :index 0}
        htp (channel/build-fixed-channel-effect "HTP" 80 [target] :htp? true)
        ltp (channel/build-fixed-channel-effect "LTP" 80 [target])]
    (is (= 100 (:value (fx/run-assigners {} {} (fx/generate htp {} {}) 100))))
    (is (= 80 (:value (fx/run-assigners {} {} (fx/generate htp {} {}) 20))))
    (is (= 80 (:value (fx/run-assigners {} {} (fx/generate ltp {} {}) 100))))
    (is (= 80 (:value (fx/run-assigners {} {} (fx/generate htp {} {}) nil))))))
