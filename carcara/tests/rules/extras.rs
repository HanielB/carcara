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
fn sko_ex_rename() {
    test_cases! {
        definitions = "
            (declare-fun p (Int) Bool)
            (declare-fun q (Int) Bool)
            (declare-fun y () Int)
        ",
        "Renamed binder" {
            "(anchor :step t1 :args ((:= (y Int) (choice ((x Int)) (p x)))))
            (step t1.t1 (cl (= (p y) (p (choice ((x Int)) (p x))))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (p x)) (p (choice ((x Int)) (p x)))))
                :rule sko_ex_rename)": true,
        }
        "Mismatched body still rejected" {
            "(anchor :step t1 :args ((:= (z Int) (choice ((x Int)) (p x)))))
            (step t1.t1 (cl (= (q z) (q (choice ((x Int)) (p x))))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (p x)) (q (choice ((x Int)) (p x)))))
                :rule sko_ex_rename)": false,
        }
        // The rename target is the free variable `y`, which already appears in the body. The
        // implicit substitution `x -> y` would alias the existing `y` (capture), which makes the
        // resulting equality unsound.
        "Variable capture rejected" {
            "(anchor :step t1 :args ((:= (y Int) (choice ((x Int)) (and (p x) (p y))))))
            (step t1.t1 (cl (= (and (p y) (p y))
                               (and (p (choice ((x Int)) (and (p x) (p y)))) (p y)))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (and (p x) (p y)))
                            (and (p (choice ((x Int)) (and (p x) (p y)))) (p y))))
                :rule sko_ex_rename)": false,
        }
    }
}

#[test]
fn sko_forall_rename() {
    test_cases! {
        definitions = "
            (declare-fun p (Int) Bool)
            (declare-fun q (Int) Bool)
            (declare-fun y () Int)
        ",
        "Renamed binder" {
            "(anchor :step t1 :args ((:= (z Int) (choice ((x Int)) (not (p x))))))
            (step t1.t1 (cl (= (p z) (p (choice ((x Int)) (not (p x)))))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (p x)) (p (choice ((x Int)) (not (p x))))))
                :rule sko_forall_rename)": true,
        }
        "Variable capture rejected" {
            "(anchor :step t1 :args ((:= (y Int) (choice ((x Int)) (not (and (p x) (p y)))))))
            (step t1.t1 (cl (= (and (p y) (p y))
                               (and (p (choice ((x Int)) (not (and (p x) (p y))))) (p y)))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (and (p x) (p y)))
                            (and (p (choice ((x Int)) (not (and (p x) (p y))))) (p y))))
                :rule sko_forall_rename)": false,
        }
    }
}
