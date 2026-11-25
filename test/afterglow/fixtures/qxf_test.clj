(ns afterglow.fixtures.qxf-test
  (:require [afterglow.fixtures.qxf :as qxf]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is]])
  (:import [java.io PushbackReader StringReader]
           [java.nio.file Files]))

(def model-name "3D Head / 45")

(def channel-name "Lamp \"A\"")

(def control-label "Slow \\ bright")

(def fixture
  {:model model-name :manufacturer "Demo" :type "Head" :open-curly "{"
   :creator {:author "Writer \"A\"" :name "Fixture Creator" :version "1"}
   :modes [{:name "Standard" :channels [[1 channel-name]]}]
   :channels [{:name channel-name :group "Effect" :capabilities [{:min 0 :max 255 :label control-label}]}]})

(deftest translated-fixture-preserves-quoted-text-as-data
  (binding [*read-eval* false]
    (with-open [reader (PushbackReader. (StringReader. (qxf/translate-definition fixture)))]
      (let [ns-form (read reader)
            [_ name _ _ result] (read reader)
            channel (first (:channels result))]
        (is (= "afterglow.fixtures.demo" (str (second ns-form))))
        (is (.contains ^String (nth ns-form 2) "Writer \"A\""))
        (is (= 'fixture-3-d-head-45 name))
        (is (= model-name (:name result)))
        (is (= channel-name (:function-name (apply hash-map (drop 3 channel)))))
        (is (= control-label (:var-label (apply hash-map (drop 3 channel)))))
        (is (= :end (read {:eof :end} reader)))))))

(deftest conversion-creates-one-output-in-source-directory
  (let [dir (.toFile (Files/createTempDirectory "qxf-fixture" (make-array java.nio.file.attribute.FileAttribute 0)))
        input (io/file dir "source.qxf") output (io/file dir "fixture-3-d-head-45.clj")]
    (try
      (with-redefs [qxf/parse-qxf (constantly fixture)]
        (is (= 0 (first (qxf/convert-qxf input))))
        (is (.isFile output))
        (spit output "operator edit")
        (is (= 1 (first (qxf/convert-qxf input))))
        (is (= "operator edit" (slurp output))))
      (finally (doseq [f (reverse (file-seq dir))] (io/delete-file f))))))
