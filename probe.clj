(require 'afterglow.render.verified)
(let [rng (var-get (ns-resolve 'afterglow.render.verified 'random-source))
      sample (ns-resolve 'afterglow.render.verified 'indices)
      check (fn [label expected got]
              (println (str label "    " (if (= expected got) "PASS" "FAIL")))
              (assert (= expected got)))]
  (check "Fresh process / entropy source deferred" false (realized? rng))
  (check "Four-row job / every row verified" [0 1 2 3] (vec (sample 4)))
  (check "Four-row job / no random state allocated" false (realized? rng))
  (let [rows (sample 8192)]
    (check "8,192-row job / distinct witnesses" 4 (count (set rows)))
    (check "8,192-row job / all witnesses in bounds" true (every? #(<= 0 % 8191) rows)))
  (check "Large job / process entropy initialized" true (realized? rng)))
