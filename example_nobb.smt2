(declare-const x Int)
(declare-const y Int)
(declare-const obj Real)

(assert (= obj (+ x y)))

(assert (>= (- (* 2 y) (* 2 x)) 1))
(assert (<= (- (* 10 y) (* 8 x)) 13))

(assert (>= x -1000))
(assert (<= x 1000))

(assert (>= y -1000))
(assert (<= y 1000))
