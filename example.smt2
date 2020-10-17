(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun obj () Real)

(assert (= obj (+ x y)))

(assert (>= (- (* 2.0 y) (* 2.0 x)) 1.0))
(assert (<= (- (* 10.0 y) (* 8.0 x)) 13.0))

(assert (>= x -1000.0))
(assert (<= x 1000.0))

(assert (>= y -1000.0))
(assert (<= y 1000.0))
