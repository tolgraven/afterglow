(ns afterglow.control.bounded
  "Bounded, oldest-first orders such as command receipt history.

  Dropping the head of a persistent vector copies the rest of it, so trimming
  a 1,024-entry order once per accepted command copied 1,024 IDs per command.
  Here a trimmed order is a view over the vector it came from, and the view is
  copied only once its backing vector has grown to twice its length plus 32.
  That is at most one copy per `limit` appends, the order is always exactly
  the newest `limit` entries, and it stays an ordinary Clojure vector for
  readers (equality, `rseq`, `peek`, printing and serialization).")

(defn drop-oldest
  "`order`, a vector, without its first `n` entries."
  [order n]
  (if (pos? n)
    (let [view (subvec order n)]
      (if (and (instance? clojure.lang.APersistentVector$SubVector view)
               (> (count (.v ^clojure.lang.APersistentVector$SubVector view)) (+ 32 (* 2 (count view)))))
        (into [] view)
        view))
    order))

(defn append
  "Append `x` to the vector `order` and drop its oldest entries beyond `limit`.
  Returns [order dropped], `dropped` being the removed entries, oldest first."
  [order x limit]
  (let [order (conj order x)
        excess (- (count order) limit)]
    (if (pos? excess)
      [(drop-oldest order excess) (subvec order 0 excess)]
      [order []])))
