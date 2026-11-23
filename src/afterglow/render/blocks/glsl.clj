(ns afterglow.render.blocks.glsl
  "Read a portable GLSL numeric expression into the lighting IR."
  (:require [clojure.string :as str]))

(def ^:private token-pattern
  #"\G\s*(?:((?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?)|([A-Za-z_][A-Za-z_0-9]*(?:\.[xyz])?)|([()+*/,-]))")
(def ^:private operators {"+" [1 :add] "-" [1 :subtract] "*" [2 :multiply] "/" [2 :divide]})
(def ^:private functions
  #{"sin" "cos" "abs" "floor" "fract" "sqrt" "exp" "pow" "clamp" "mix" "min" "max" "vec2" "vec3" "vec4"})

(defn- invalid [message offset]
  (throw (ex-info message {:path [:glsl] :offset offset :message message})))

(defn- tokenize [source]
  (when-not (and (string? source) (<= (count source) 4096))
    (invalid "Expected a GLSL expression of up to 4096 characters" 0))
  (let [s (str/trim source) matcher (re-matcher token-pattern s)]
    (loop [tokens [] offset 0]
      (cond (= offset (count s)) tokens
            (>= (count tokens) 512) (invalid "GLSL expression exceeds 512 tokens" offset)
            (.find matcher) (let [number (.group matcher 1)]
                              (recur (conj tokens [(if number (Double/parseDouble number)
                                                     (or (.group matcher 2) (.group matcher 3)))
                                                   (.start matcher)]) (.end matcher)))
            :else (invalid "Unsupported GLSL syntax" offset)))))

(defn expression
  "Accept arithmetic, supported numeric GLSL functions, prefab input names,
  mapped position.xyz, physical world.xyz and independent uv.xy components. The CPU and both GPU backends share the AST."
  [source]
  (let [tokens (tokenize source) cursor (volatile! 0)
        peek-token #(first (get tokens @cursor))
        location #(or (second (get tokens @cursor)) (count source))
        pop-token #(let [t (peek-token)] (vswap! cursor inc) t)
        require-token (fn [token]
                        (when-not (= token (peek-token)) (invalid (str "Expected " token) (location)))
                        (pop-token))]
    (letfn [(args [depth]
              (require-token "(")
              (loop [result [(binary 1 depth)]]
                (case (peek-token)
                  ")" (do (pop-token) result)
                  "," (do (pop-token) (recur (conj result (binary 1 depth))))
                  (invalid "Expected a comma or closing parenthesis" (location)))))
            (atom-node [depth]
              (when (> depth 64) (invalid "GLSL expression exceeds 64 levels" (location)))
              (let [offset (location) t (pop-token)]
                (cond (number? t) {:op :const :value t}
                      (= "(" t) (let [node (binary 1 (inc depth))] (require-token ")") node)
                      (= "-" t) {:op :subtract :args [(atom-node (inc depth))]}
                      (= "+" t) (atom-node (inc depth))
                      (functions t) {:op (keyword t) :args (args (inc depth))}
                      (and t (re-matches #"position\.[xyz]" t))
                      {:op :coordinate :axis (keyword (subs t 9))}
                      (and t (re-matches #"world\.[xyz]" t))
                      {:op :position :axis (keyword (subs t 6))}
                      (and t (re-matches #"uv\.[xy]" t))
                      {:op :surface-uv :axis (if (= "uv.x" t) :u :v)}
                      (and t (re-matches #"[A-Za-z_]\w*" t)) {:op :input :key (keyword t)}
                      :else (invalid "Expected a number, input, function or coordinate" offset))))
            (binary [precedence depth]
              (loop [lhs (atom-node depth)]
                (if-let [[rank opcode] (operators (peek-token))]
                  (if (< rank precedence) lhs
                    (do (pop-token)
                        (recur {:op opcode :args [lhs (binary (inc rank) depth)]})))
                  lhs)))]
      (let [tree (binary 1 0)]
        (when (peek-token) (invalid "Unexpected trailing GLSL input" (location)))
        tree))))
