(set-logic QF_LIA)
(declare-const x6 Int)
(assert (not (= (= (not (not (>= x6 -2))) (>= x6 -2)) true)))
(check-sat)
