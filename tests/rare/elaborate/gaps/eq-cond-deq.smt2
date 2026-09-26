(set-logic QF_LIA)
(declare-const x Int)
(assert (not (= (= (= x 1) (= x 2)) (and (not (= x 1)) (not (= x 2))))))
(check-sat)
