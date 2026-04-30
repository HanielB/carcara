#[test]
fn reordering() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl p q r s) :rule hole)
            (step t2 (cl r q p s) :rule reordering :premises (t1))": true,

            "(step t1 (cl p q q p r s) :rule hole)
            (step t2 (cl r q p p s q) :rule reordering :premises (t1))": true,

            "(step t1 (cl) :rule hole)
            (step t2 (cl) :rule reordering :premises (t1))": true,
        }
    }
}

#[test]
fn shuffle() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (+ x y z) (+ z x y))) :rule shuffle)": true,

            "(step t1 (cl (= (and p q q r p) (and q q p p r))) :rule shuffle)": true,
        }
        "Invalid examples" {
            "(step t1 (cl (= (- x y z) (- x y z))) :rule shuffle)": false,
            "(step t1 (cl (= (or p q r) (and p q r))) :rule shuffle)": false,
            "(step t1 (cl (= (or p q r) true)) :rule shuffle)": false,
            "(step t1 (cl (= (* x x y) (* x y y))) :rule shuffle)": false,
            "(step t1 (cl (= (* x x y) (+ x y))) :rule shuffle)": false,
        }
    }
}

#[test]
fn symm() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(assume h1 (= a b))
            (step t1 (cl (= b a)) :rule symm :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (not (= a b)))
            (step t1 (cl (not (= b a))) :rule symm :premises (h1))": false,
        }
    }
}

#[test]
fn not_symm() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(assume h1 (not (= a b)))
            (step t1 (cl (not (= b a))) :rule not_symm :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (= a b))
            (step t1 (cl (= b a)) :rule not_symm :premises (h1))": false,
        }
    }
}

#[test]
fn eq_symmetric() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (= b a) (= a b))) :rule eq_symmetric)": true,
            "(step t1 (cl (= (= a a) (= a a))) :rule eq_symmetric)": true,
        }
        "Failing examples" {
            "(step t1 (cl (= (= a b) (= a b))) :rule eq_symmetric)": false,
            "(step t1 (cl (= (not (= a b)) (not (= b a)))) :rule eq_symmetric)": false,
        }
    }
}

#[test]
fn weakening() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl a b c) :rule weakening :premises (t1))": true,

            "(step t1 (cl) :rule hole)
            (step t2 (cl a b) :rule weakening :premises (t1))": true,
        }
        "Failing examples" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl a c b) :rule weakening :premises (t1))": false,

            "(step t1 (cl a b c) :rule hole)
            (step t2 (cl a b) :rule weakening :premises (t1))": false,
        }
    }
}

#[test]
fn bind_let() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": true,
        }
        "Premise is of the wrong form" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (< (+ x y) 0)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": false,
        }
        "Premise doesn't justify inner terms' equality" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) a) (let ((a 0)) 0))) :rule bind_let)": false,

            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) y) (let ((a 0)) x))) :rule bind_let)": false,
        }
        "Bindings can't be renamed" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((b 0)) y))) :rule bind_let)": false,
        }
        "Polyequality in variable values" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= (= 0 1) (= 1 0))) :rule hole)
            (step t1.t2 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a (= 0 1))) x) (let ((a (= 1 0))) y)))
                :rule bind_let :premises (t1.t1))": true,
        }
    }
}

#[test]
fn la_mult_pos() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (and (> 2 0) (> a b)) (> (* 2 a) (* 2 b))))
                :rule la_mult_pos)": true,
            "(step t1 (cl (=>
                (and (> (/ 10.0 13.0) 0.0) (= x y))
                (= (* (/ 10.0 13.0) x) (* (/ 10.0 13.0) y)))
            ) :rule la_mult_pos)": true,
        }
    }
}

#[test]
fn la_mult_neg() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (and (< (- 2) 0) (>= a b)) (<= (* (- 2) a) (* (- 2) b))))
                :rule la_mult_neg)": true,
            "(step t1 (cl (=>
                (and (< (/ (- 1.0) 13.0) 0.0) (= x y))
                (= (* (/ (- 1.0) 13.0) x) (* (/ (- 1.0) 13.0) y)))
            ) :rule la_mult_neg)": true,
        }
    }
}

#[test]
fn la_mult_sign() {
    test_cases! {
        definitions = "
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
            (declare-fun a () Real)
            (declare-fun b () Real)
        ",
        "Single variable, positive" {
            "(step t1 (cl (=> (> x 0) (> x 0))) :rule la_mult_sign)": true,
        }
        "Single variable, negative" {
            "(step t1 (cl (=> (< x 0) (< x 0))) :rule la_mult_sign)": true,
        }
        "Product of two distinct vars, both positive (positive monomial)" {
            "(step t1 (cl (=> (and (> x 0) (> y 0)) (> (* x y) 0)))
                :rule la_mult_sign)": true,
        }
        "Product of two distinct vars, one negative (negative monomial)" {
            "(step t1 (cl (=> (and (< x 0) (> y 0)) (< (* x y) 0)))
                :rule la_mult_sign)": true,
            "(step t1 (cl (=> (and (> x 0) (< y 0)) (< (* x y) 0)))
                :rule la_mult_sign)": true,
        }
        "Product of two distinct vars, both negative (positive monomial)" {
            "(step t1 (cl (=> (and (< x 0) (< y 0)) (> (* x y) 0)))
                :rule la_mult_sign)": true,
        }
        "Even exponent uses disequality with zero" {
            "(step t1 (cl (=> (not (= x 0)) (> (* x x) 0))) :rule la_mult_sign)": true,
            "(step t1 (cl (=> (and (not (= x 0)) (> y 0)) (> (* x x y) 0)))
                :rule la_mult_sign)": true,
            "(step t1 (cl (=> (and (not (= x 0)) (< y 0)) (< (* x x y) 0)))
                :rule la_mult_sign)": true,
        }
        "Three distinct variables with mixed signs" {
            "(step t1 (cl (=> (and (< x 0) (< y 0) (< z 0)) (< (* x y z) 0)))
                :rule la_mult_sign)": true,
            "(step t1 (cl (=> (and (> x 0) (< y 0) (< z 0)) (> (* x y z) 0)))
                :rule la_mult_sign)": true,
        }
        "Real variables work too" {
            "(step t1 (cl (=> (and (> a 0.0) (< b 0.0)) (< (* a b) 0.0)))
                :rule la_mult_sign)": true,
        }
        "Wrong sign in conclusion" {
            "(step t1 (cl (=> (and (> x 0) (> y 0)) (< (* x y) 0)))
                :rule la_mult_sign)": false,
            "(step t1 (cl (=> (and (< x 0) (> y 0)) (> (* x y) 0)))
                :rule la_mult_sign)": false,
        }
        "Premise variable doesn't match monomial variable" {
            "(step t1 (cl (=> (and (> y 0) (> x 0)) (> (* x y) 0)))
                :rule la_mult_sign)": false,
        }
        "Number of premises doesn't match unique vars" {
            "(step t1 (cl (=> (> x 0) (> (* x y) 0))) :rule la_mult_sign)": false,
            "(step t1 (cl (=> (and (> x 0) (> y 0)) (> x 0))) :rule la_mult_sign)": false,
        }
        "Even-exponent variable with sign premise instead of disequality" {
            "(step t1 (cl (=> (> x 0) (> (* x x) 0))) :rule la_mult_sign)": false,
        }
        "Right-hand side of comparison must be zero" {
            "(step t1 (cl (=> (> x 1) (> x 0))) :rule la_mult_sign)": false,
            "(step t1 (cl (=> (> x 0) (> x 1))) :rule la_mult_sign)": false,
        }
        "Conclusion operator must be < or >" {
            "(step t1 (cl (=> (> x 0) (>= x 0))) :rule la_mult_sign)": false,
            "(step t1 (cl (=> (> x 0) (= x 0))) :rule la_mult_sign)": false,
        }
    }
}

#[test]
fn la_mult_abs_comparison() {
    test_cases! {
        definitions = "
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
            (declare-fun w () Int)
        ",
        "Equality conclusion: single premise" {
            "(step t1 (cl (= (abs x) (abs y))) :rule hole)
            (step t2 (cl (= (abs x) (abs y))) :rule la_mult_abs_comparison :premises (t1))": true,
        }
        "Equality conclusion: product of two" {
            "(step t1 (cl (= (abs x) (abs z))) :rule hole)
            (step t2 (cl (= (abs y) (abs w))) :rule hole)
            (step t3 (cl (= (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": true,
        }
        "Equality conclusion: product of three" {
            "(step t1 (cl (= (abs x) (abs y))) :rule hole)
            (step t2 (cl (= (abs y) (abs z))) :rule hole)
            (step t3 (cl (= (abs z) (abs w))) :rule hole)
            (step t4 (cl (= (abs (* x y z)) (abs (* y z w))))
                :rule la_mult_abs_comparison :premises (t1 t2 t3))": true,
        }
        "Greater-than conclusion: all premises strict" {
            "(step t1 (cl (> (abs x) (abs z))) :rule hole)
            (step t2 (cl (> (abs y) (abs w))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": true,
        }
        "Greater-than conclusion: equality premise needs zero guard" {
            "(step t1 (cl (> (abs x) (abs z))) :rule hole)
            (step t2 (cl (and (= (abs y) (abs w)) (not (= y 0)))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": true,
        }
        "Greater-than conclusion: first premise must be strict" {
            "(step t1 (cl (and (= (abs x) (abs z)) (not (= x 0)))) :rule hole)
            (step t2 (cl (> (abs y) (abs w))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
        "Greater-than conclusion: equality premise without zero guard fails" {
            "(step t1 (cl (> (abs x) (abs z))) :rule hole)
            (step t2 (cl (= (abs y) (abs w))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
        "Greater-than conclusion: zero guard for wrong term fails" {
            "(step t1 (cl (> (abs x) (abs z))) :rule hole)
            (step t2 (cl (and (= (abs y) (abs w)) (not (= w 0)))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
        "Equality conclusion: greater-than premise fails" {
            "(step t1 (cl (> (abs x) (abs y))) :rule hole)
            (step t2 (cl (= (abs x) (abs y))) :rule la_mult_abs_comparison :premises (t1))": false,
        }
        "Premise factors must match conclusion factors" {
            "(step t1 (cl (= (abs x) (abs z))) :rule hole)
            (step t2 (cl (= (abs y) (abs w))) :rule hole)
            (step t3 (cl (= (abs (* y x)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
        "Number of premises must match number of factors" {
            "(step t1 (cl (= (abs x) (abs y))) :rule hole)
            (step t2 (cl (= (abs (* x x)) (abs (* y y))))
                :rule la_mult_abs_comparison :premises (t1))": false,
        }
        "Wrong operator in conclusion" {
            "(step t1 (cl (= (abs x) (abs y))) :rule hole)
            (step t2 (cl (>= (abs x) (abs y))) :rule la_mult_abs_comparison :premises (t1))": false,
            "(step t1 (cl (= (abs x) (abs y))) :rule hole)
            (step t2 (cl (< (abs x) (abs y))) :rule la_mult_abs_comparison :premises (t1))": false,
        }
        "Repeated factors using same premise" {
            "(step t1 (cl (= (abs x) (abs y))) :rule hole)
            (step t2 (cl (= (abs (* x x)) (abs (* y y))))
                :rule la_mult_abs_comparison :premises (t1 t1))": true,
        }
        "Equality conclusion: AND-form premise rejected" {
            "(step t1 (cl (and (= (abs x) (abs y)) (not (= x 0)))) :rule hole)
            (step t2 (cl (= (abs x) (abs y))) :rule la_mult_abs_comparison :premises (t1))": false,
            "(step t1 (cl (= (abs x) (abs z))) :rule hole)
            (step t2 (cl (and (= (abs y) (abs w)) (not (= y 0)))) :rule hole)
            (step t3 (cl (= (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
        "Greater-than conclusion: first premise can't be in AND form" {
            "(step t1 (cl (and (> (abs x) (abs z)) (not (= x 0)))) :rule hole)
            (step t2 (cl (> (abs y) (abs w))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
        "Greater-than conclusion: AND-wrapped '>' is rejected" {
            "(step t1 (cl (> (abs x) (abs z))) :rule hole)
            (step t2 (cl (and (> (abs y) (abs w)) (not (= y 0)))) :rule hole)
            (step t3 (cl (> (abs (* x y)) (abs (* z w))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
    }
}

#[test]
fn mod_simplify() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (= (mod 2 2) 0)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod 42 8) 2)) :rule mod_simplify)": true,
        }
        "Negative numbers" {
            "(step t1 (cl (= (mod (- 8) 3) 1)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod 8 (- 3)) 2)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod (- 8) (- 3)) 1)) :rule mod_simplify)": true,

            "(step t1 (cl (= (mod (- 8) 3) (- 2))) :rule mod_simplify)": false,
            "(step t1 (cl (= (mod 8 (- 3)) (- 1))) :rule mod_simplify)": false,
            "(step t1 (cl (= (mod (- 8) (- 3)) (- 2))) :rule mod_simplify)": false,
        }
        "Modulo by zero" {
            "(step t1 (cl (= (mod 3 0) 1)) :rule mod_simplify)": false,
        }
    }
}

#[test]
fn evaluate() {
    test_cases! {
        definitions = "
            (declare-const x Int)
            (declare-fun f (Int Int) Int)
        ",
        "Booleans" {
            "(step t1 (cl (=
                (=> (and true true) (or true false) (ite false false true))
                true
            )) :rule evaluate)": true,

            "(step t1 (cl (= (or (= 0 0 1) (distinct 1 2 3 1)) false)) :rule evaluate)": true,
        }
        "Arithmetic" {
            "(step t1 (cl (= (+ 1 2 (* 3 (- 1))) 0)) :rule evaluate)": true,
            "(step t1 (cl (= (+ (div 3 (abs 2)) (mod (- 7) (- 3))) 0)) :rule evaluate)": true,
            "(step t1 (cl (= (/ 1.0 (to_real 7)) 1/7)) :rule evaluate)": true,
        }
        "Bitvectors" {
            "(step t1 (cl (=
                (bvnot (bvudiv #b100 (@bbterm false true false)))
                #b101
            )) :rule evaluate)": true,

            "(step t1 (cl (=
                (bvashr ((_ rotate_left 3) #b0101100) #b0000001)
                #b1110001
            )) :rule evaluate)": true,
        }
        "Partial evaluation" {
            "(step t1 (cl (= (+ x (+ 1 1)) (+ x 2))) :rule evaluate)": true,
            "(step t1 (cl (= (f x (+ 1 1)) (f x 2))) :rule evaluate)": false,
        }
        "Invalid examples" {
            "(step t1 (cl (= 2 (+ 1 1))) :rule evaluate)": false,
            "(step t1 (cl (= (forall ((x Int)) true) true)) :rule evaluate)": false,
        }
    }
}
