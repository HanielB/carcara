#[test]
fn la_rw_eq() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (= a b) (and (<= a b) (<= b a)))) :rule la_rw_eq)": true,
            "(step t1 (cl (= (= x y) (and (<= x y) (<= y x)))) :rule la_rw_eq)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (= (= b a) (and (<= a b) (<= b a)))) :rule la_rw_eq)": false,
            "(step t1 (cl (= (= x y) (and (<= x y) (<= x y)))) :rule la_rw_eq)": false,
        }
    }
}

#[test]
fn la_generic() {
    test_cases! {
        definitions = "
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun c () Real)
            (declare-fun m () Int)
            (declare-fun n () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (> a 0.0) (<= a 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (<= 0.0 0.0)) :rule la_generic :args (1.0))": true,

            "(step t1 (cl (< (+ a b) 1.0) (> (+ a b) 0.0))
                :rule la_generic :args (1.0 (- 1.0)))": true,

            "(step t1 (cl (<= (+ a (- b a)) b)) :rule la_generic :args (1.0))": true,

            "(step t1 (cl (not (<= (- a b) (- c 1.0))) (<= (+ 1.0 (- a c)) b))
                :rule la_generic :args (1.0 1.0))": true,
        }
        "Empty clause" {
            "(step t1 (cl) :rule la_generic)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0 1.0))": false,
        }
        "Invalid argument term" {
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 b))": false,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (ite (= a b) false true)) :rule la_generic :args (1.0))": false,
            "(step t1 (cl (= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0))": false,
        }
        "Negation of disequalities is satisfiable" {
            "(step t1 (cl (< 0.0 0.0)) :rule la_generic :args (1.0))": false,

            "(step t1 (cl (< (+ a b) 1.0) (> (+ a b c) 0.0))
                :rule la_generic :args (1.0 (- 1.0)))": false,
        }
        "Edge case where the strengthening rules need to be stronger" {
            "(step t1 (cl
                (not (<= (- 1) n))
                (not (<= (- 1) (+ n m)))
                (<= (- 2) (* 2 n))
                (not (<= m 1))
            ) :rule la_generic :args (1 1 1 1))": true,
        }
    }
}

#[test]
fn la_disequality() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (= a b) (not (<= a b)) (not (<= b a))))
                :rule la_disequality)": true,
            "(step t1 (cl (or (= x y) (not (<= x y)) (not (<= y x))))
                :rule la_disequality)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (or (= b a) (not (<= a b)) (not (<= b a))))
                :rule la_disequality)": false,
            "(step t1 (cl (or (= x y) (not (<= y x)) (not (<= y x))))
                :rule la_disequality)": false,
        }
    }
}

#[test]
fn la_totality() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (<= a b) (<= b a))) :rule la_totality)": true,
            "(step t1 (cl (or (<= x y) (<= y x))) :rule la_totality)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (or (<= a b) (<= a b))) :rule la_totality)": false,
            "(step t1 (cl (<= x y) (<= x y)) :rule la_totality)": false,
            "(step t1 (cl (<= 0 1) (<= 0.0 1.0)) :rule la_totality)": false,
        }
    }
}

#[test]
fn la_tautology() {
    test_cases! {
        definitions = "
            (declare-fun n () Int)
            (declare-fun x () Real)
        ",
        "First form" {
            "(step t1 (cl (<= n (+ 1 n))) :rule la_tautology)": true,
            "(step t1 (cl (< (- n 1) n)) :rule la_tautology)": true,
            "(step t1 (cl (not (<= n (- n 1)))) :rule la_tautology)": true,
            "(step t1 (cl (< 0 (- (+ 1 n) n))) :rule la_tautology)": true,
            "(step t1 (cl (not (<= (+ 1 n) (- (+ 1 n) 1)))) :rule la_tautology)": true,
        }
        "Second form" {
            "(step t1 (cl (or (not (<= x 5.0)) (<= x 6.0))) :rule la_tautology)": true,

            "(step t1 (cl (or (<= x 6.0) (not (<= x 6.0)))) :rule la_tautology)": true,
            "(step t1 (cl (or (<= x 6.1) (not (<= x 6.0)))) :rule la_tautology)": false,

            "(step t1 (cl (or (not (>= x 6.0)) (>= x 5.0))) :rule la_tautology)": true,

            "(step t1 (cl (or (>= x 5.0) (not (>= x 5.0)))) :rule la_tautology)": true,
            "(step t1 (cl (or (>= x 5.0) (not (>= x 5.1)))) :rule la_tautology)": false,

            "(step t1 (cl (or (not (<= x 4.0)) (not (>= x 5.0)))) :rule la_tautology)": true,
            "(step t1 (cl (or (not (<= x 5.0)) (not (>= x 5.0)))) :rule la_tautology)": false,
        }
    }
}

/// The strengthening rules of `la_generic` are integer reasoning, and are available only for rows
/// whose value is an integer under every valuation: every atom integer-sorted, every coefficient an
/// integer. Deciding it from the constant alone accepts `(cl (not (>= x 0.5)) (>= x 1.0))` for a
/// real `x`, which is false at `x = 0.7`.
#[test]
fn la_generic_strengthening_is_integer_only() {
    test_cases! {
        definitions = "
            (declare-fun n () Int)
            (declare-fun m () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Rounding a bound is valid over the integers" {
            "(step t1 (cl (not (>= (to_real n) (/ (- 3.0) 2.0))) (>= n (- 1))) :rule la_generic :args (1 1))": true,
            "(step t1 (cl (not (>= n (- 1))) (>= (to_real n) (/ (- 3.0) 2.0))) :rule la_generic :args (1 1))": true,
            "(step t1 (cl (not (>= (to_real (+ n m)) (/ (- 19.0) 4.0))) (>= (+ n m) (- 4))) :rule la_generic :args (1 1))": true,
            // An integer cannot sit strictly between two consecutive integers
            "(step t1 (cl (not (<= (to_real n) (/ (- 3.0) 2.0))) (not (<= (/ (- 3.0) 2.0) (to_real n)))) :rule la_generic :args (1 1))": true,
        }
        "and is not valid over the reals" {
            "(step t1 (cl (not (>= x 0.5)) (>= x 1.0)) :rule la_generic :args (1 1))": false,
            "(step t1 (cl (not (>= x 0.0)) (>= x 1.0)) :rule la_generic :args (1 1))": false,
            "(step t1 (cl (not (<= x 0.5)) (<= x 0.0)) :rule la_generic :args (1 1))": false,
            "(step t1 (cl (not (<= x 0.5)) (not (<= 0.5 x))) :rule la_generic :args (1 1))": false,
        }
        "nor for an integer atom with a rational coefficient" {
            // `n/2 > 1` gives `n >= 3`, i.e. `n/2 >= 3/2`, not `n/2 >= 2`
            "(step t1 (cl (not (> (* 0.5 (to_real n)) 1.0)) (>= (* 0.5 (to_real n)) 2.0)) :rule la_generic :args (1 1))": false,
        }
        "A strict bound stays strict when rows are added" {
            "(step t1 (cl (> x 0.0) (<= x 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (> (+ x y) 0.0) (<= x 0.0) (<= y 0.0)) :rule la_generic :args (1.0 1.0 1.0))": true,
            "(step t1 (cl (>= x 0.0) (<= x 0.0)) :rule la_generic :args (1.0 1.0))": true,
            // Not a tautology over the reals: both disjuncts fail at `x = 0`
            "(step t1 (cl (> x 0.0) (< x 0.0)) :rule la_generic :args (1.0 1.0))": false,
        }
    }
}


#[test]
fn to_int_lower() {
    test_cases! {
        definitions = "
            (declare-fun x () Real)
            (declare-fun n () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (<= (to_real (to_int x)) x)) :rule to_int_lower)": true,
            "(step t1 (cl (<= (to_real (to_int (/ (- 3.0) 2.0))) (/ (- 3.0) 2.0))) :rule to_int_lower)": true,
            "(step t1 (cl (<= (to_real (to_int (+ x 1.0))) (+ x 1.0))) :rule to_int_lower)": true,
        }
        "The two sides must be the same term" {
            "(step t1 (cl (<= (to_real (to_int x)) (to_real n))) :rule to_int_lower)": false,
            "(step t1 (cl (<= x (to_real (to_int x)))) :rule to_int_lower)": false,
        }
        "Wrong shape" {
            "(step t1 (cl (< (to_real (to_int x)) x)) :rule to_int_lower)": false,
            "(step t1 (cl (<= (to_int x) x)) :rule to_int_lower)": false,
            "(step t1 (cl (<= (to_real (to_int x)) x) (<= (to_real (to_int x)) x)) :rule to_int_lower)": false,
        }
    }
}

#[test]
fn to_int_upper() {
    test_cases! {
        definitions = "
            (declare-fun x () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (< x (+ (to_real (to_int x)) 1.0))) :rule to_int_upper)": true,
            "(step t1 (cl (< (/ (- 3.0) 2.0) (+ (to_real (to_int (/ (- 3.0) 2.0))) 1.0))) :rule to_int_upper)": true,
        }
        "The offset must be 1" {
            "(step t1 (cl (< x (+ (to_real (to_int x)) 2.0))) :rule to_int_upper)": false,
            "(step t1 (cl (< x (+ (to_real (to_int x)) 0.0))) :rule to_int_upper)": false,
        }
        "Wrong shape" {
            "(step t1 (cl (<= x (+ (to_real (to_int x)) 1.0))) :rule to_int_upper)": false,
            "(step t1 (cl (< (to_real (to_int x)) (+ (to_real (to_int x)) 1.0))) :rule to_int_upper)": false,
        }
    }
}

/// The two floor axioms determine `to_int` on a constant: they bound it to a half-open unit
/// interval, and `la_generic`'s integer strengthening turns each bound into a bound on the value.
#[test]
fn to_int_axioms_determine_the_value() {
    test_cases! {
        definitions = "(declare-fun z () Int)",
        "Tightening each bound to the floor" {
            "(step t1 (cl (not (<= (to_real (to_int (/ (- 3.0) 2.0))) (/ (- 3.0) 2.0))) (<= (to_int (/ (- 3.0) 2.0)) (- 2))) :rule la_generic :args (1 1))": true,
            "(step t1 (cl (not (< (/ (- 3.0) 2.0) (+ (to_real (to_int (/ (- 3.0) 2.0))) 1.0))) (<= (- 2) (to_int (/ (- 3.0) 2.0)))) :rule la_generic :args (1 1))": true,
        }
    }
}
