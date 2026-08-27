use carcara::{ast, checker, elaborator, parser};

/// Runs the `core` elaboration pass on a proof, checks the result in elaborated granularity, and
/// returns the rules of the steps of the resulting proof.
fn run_core_pass(problem: &str, proof: &str) -> Vec<String> {
    run_pass(problem, proof, elaborator::ElaborationPass::Core)
}

/// Runs one elaboration pass, checks the result in elaborated granularity, and returns the rules
/// of the steps of the resulting proof.
fn run_pass(problem: &str, proof: &str, pass: elaborator::ElaborationPass) -> Vec<String> {
    let elaborated = elaborate_pass(problem, proof, pass);

    fn collect(commands: &[ast::ProofCommand], rules: &mut Vec<String>) {
        for c in commands {
            match c {
                ast::ProofCommand::Step(s) => rules.push(s.rule.clone()),
                ast::ProofCommand::Subproof(s) => collect(&s.commands, rules),
                ast::ProofCommand::Assume { .. } => (),
            }
        }
    }
    let mut rules = Vec::new();
    collect(&elaborated.commands, &mut rules);
    rules
}

/// Runs the `core` elaboration pass on a proof, checks the result in elaborated granularity, and
/// returns it.
fn elaborate_core_pass(problem: &str, proof: &str) -> ast::Proof {
    elaborate_pass(problem, proof, elaborator::ElaborationPass::Core)
}

fn elaborate_pass(problem: &str, proof: &str, pass: elaborator::ElaborationPass) -> ast::Proof {
    let (mut problem, proof, rare_rules, mut pool) = parser::parse_instance(
        problem,
        proof,
        None,
        parser::Config {
            allow_int_real_subtyping: true,
            ..Default::default()
        },
    )
    .unwrap();

    // The cases use `assume` commands to introduce premises, so the assumed terms are retroactively
    // added as the problem's premises, as the rule tests do
    problem.premises = proof
        .commands
        .iter()
        .filter_map(|c| match c {
            ast::ProofCommand::Assume { term, .. } => Some(term.clone()),
            _ => None,
        })
        .collect();

    let config = checker::Config::new();
    checker::ProofChecker::new(&mut pool, &rare_rules, config.clone())
        .check(&problem, &proof)
        .expect("original proof does not check");

    let elab_config = elaborator::Config {
        lia_solver: None,
        hole_solver: None,
        uncrowd_rotation: true,
        ..Default::default()
    };
    let node = ast::ProofNodeForest::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
        .elaborate(node, vec![pass])
        .expect("elaboration failed");
    let elaborated = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: elaborated_node.into_commands(),
    };

    checker::ProofChecker::new(&mut pool, &rare_rules, config.elaborated(true))
        .check(&problem, &elaborated)
        .expect("elaborated proof does not check");

    elaborated
}

/// Every arithmetic instance of `poly_simp_rel` reduces: one `la_generic` per direction for the
/// inequalities, and the `la_disequality` template for the equalities.
#[test]
fn poly_simp_rel() {
    let definitions = "
        (declare-const x Int)
        (declare-const y Int)
        (declare-const a Real)
        (declare-const b Real)
    ";
    let cases = [
        // The five relations, with the coefficients `1` and `1`
        "(step t1 (cl (= (* 1 (- (+ x y) 1)) (* 1 (- x (+ 1 (* -1 y)))))) :rule poly_simp)
         (step t2 (cl (= (< (+ x y) 1) (< x (+ 1 (* -1 y))))) :rule poly_simp_rel :premises (t1))",
        "(step t1 (cl (= (* 1 (- (+ x y) 1)) (* 1 (- x (+ 1 (* -1 y)))))) :rule poly_simp)
         (step t2 (cl (= (<= (+ x y) 1) (<= x (+ 1 (* -1 y))))) :rule poly_simp_rel :premises (t1))",
        "(step t1 (cl (= (* 1 (- (+ x y) 1)) (* 1 (- x (+ 1 (* -1 y)))))) :rule poly_simp)
         (step t2 (cl (= (= (+ x y) 1) (= x (+ 1 (* -1 y))))) :rule poly_simp_rel :premises (t1))",
        "(step t1 (cl (= (* 1 (- (+ x y) 1)) (* 1 (- x (+ 1 (* -1 y)))))) :rule poly_simp)
         (step t2 (cl (= (>= (+ x y) 1) (>= x (+ 1 (* -1 y))))) :rule poly_simp_rel :premises (t1))",
        "(step t1 (cl (= (* 1 (- (+ x y) 1)) (* 1 (- x (+ 1 (* -1 y)))))) :rule poly_simp)
         (step t2 (cl (= (> (+ x y) 1) (> x (+ 1 (* -1 y))))) :rule poly_simp_rel :premises (t1))",
        // Coefficients of the same sign, both negative, and scaling
        "(step t1 (cl (= (* -2 (- x 1)) (* -1 (- (* 2 x) 2)))) :rule poly_simp)
         (step t2 (cl (= (< x 1) (< (* 2 x) 2))) :rule poly_simp_rel :premises (t1))",
        "(step t1 (cl (= (* 1/2 (- x 1)) (* 2.0 (- (* 1/4 x) 1/4)))) :rule poly_simp)
         (step t2 (cl (= (>= x 1) (>= (* 1/4 x) 1/4))) :rule poly_simp_rel :premises (t1))",
        // Coefficients of different signs, which only the equality case allows
        "(step t1 (cl (= (* 1 (- x 1)) (* -1 (- 1 x)))) :rule poly_simp)
         (step t2 (cl (= (= x 1) (= 1 x))) :rule poly_simp_rel :premises (t1))",
        "(step t1 (cl (= (* -1.0 (- x 1)) (* 2.0 (- (* 1/2 1) (* 1/2 x))))) :rule poly_simp)
         (step t2 (cl (= (= x 1) (= (* 1/2 1) (* 1/2 x)))) :rule poly_simp_rel :premises (t1))",
        // Over the reals
        "(step t1 (cl (= (* 1.0 (- (+ a b) 1.0)) (* 1.0 (- a (- 1.0 b))))) :rule poly_simp)
         (step t2 (cl (= (<= (+ a b) 1.0) (<= a (- 1.0 b)))) :rule poly_simp_rel :premises (t1))",
        // With `to_real` wrappers, both around the premise's differences and inside the
        // conclusion's terms
        "(step t1 (cl (= (* 1.0 (to_real (- (+ x y) 1))) (* 1.0 (- (to_real (+ x y)) (to_real 1))))) :rule poly_simp)
         (step t2 (cl (= (<= (+ x y) 1) (<= (to_real (+ x y)) (to_real 1)))) :rule poly_simp_rel :premises (t1))",
        // A degenerate instance, where the two sides of the consequent are the same term
        "(step t1 (cl (= (* 1 (- x x)) (* 1 (- y y)))) :rule poly_simp)
         (step t2 (cl (= (= x x) (= y y))) :rule poly_simp_rel :premises (t1))",
        // The rule does not require its premise to be a polynomial identity, only to hold. Then
        // the certificate has to use the premise, and the recipe falls back on doing so
        "(assume h (= (* 1 (- x 0)) (* 1 (- y 0))))
         (step t2 (cl (= (< x 0) (< y 0))) :rule poly_simp_rel :premises (h))",
        "(assume h (= (* 2 (- x 1)) (* 3 (- y 1))))
         (step t2 (cl (= (>= x 1) (>= y 1))) :rule poly_simp_rel :premises (h))",
        "(assume h (= (* 1 (- x 0)) (* -1 (- 0 y))))
         (step t2 (cl (= (= x 0) (= 0 y))) :rule poly_simp_rel :premises (h))",
    ];
    for case in cases {
        let proof = format!("{}\n(step end (cl) :rule hole)", case);
        let rules = run_core_pass(definitions, &proof);
        assert!(
            !rules.iter().any(|r| r == "poly_simp_rel"),
            "step was not reduced: {}",
            case
        );
        assert!(rules.iter().any(|r| r == "la_generic"));
    }
}

/// The bitvector case of `poly_simp_rel` has no core reduction, so the step is kept.
#[test]
fn poly_simp_rel_bitvector_is_kept() {
    let definitions = "
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
    ";
    let proof = "
        (step t1 (cl (= (bvmul #b0011 (bvsub x y)) (bvmul #b0011 (bvsub x y)))) :rule refl)
        (step t2 (cl (= (= x y) (= x y))) :rule poly_simp_rel :premises (t1))
        (step end (cl) :rule hole)
    ";
    let rules = run_core_pass(definitions, proof);
    assert!(rules.iter().any(|r| r == "poly_simp_rel"));
}

/// Two steps with the same conclusion, in different subproofs, share a single derivation, which is
/// emitted once at the top level.
#[test]
fn sharing_across_subproofs() {
    let definitions = "
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
    ";
    // The `poly_simp_rel` step cannot be the last step before the one that closes the subproof,
    // since that one refers to it by its position; the `contraction` step stands in between
    let subproof = |i: usize| {
        format!(
            "(anchor :step t{i})
             (assume t{i}.h1 p)
             (step t{i}.t1 (cl (= (* 1 (- (+ x y) 1)) (* 1 (- x (+ 1 (* -1 y)))))) :rule poly_simp)
             (step t{i}.t2 (cl (= (< (+ x y) 1) (< x (+ 1 (* -1 y))))) :rule poly_simp_rel \
              :premises (t{i}.t1))
             (step t{i}.t3 (cl (= (< (+ x y) 1) (< x (+ 1 (* -1 y))))) :rule contraction \
              :premises (t{i}.t2))
             (step t{i} (cl (not p) (= (< (+ x y) 1) (< x (+ 1 (* -1 y))))) :rule subproof \
              :discharge (t{i}.h1))"
        )
    };
    let proof = format!(
        "(assume a0 p)\n{}\n{}\n(step end (cl) :rule hole)",
        subproof(1),
        subproof(2)
    );

    let elaborated = elaborate_core_pass(definitions, &proof);

    // Each direction of the equivalence takes one `la_generic` step, so a shared derivation has two
    // of them and two unshared ones would have four
    fn count(commands: &[ast::ProofCommand], rule: &str) -> usize {
        commands
            .iter()
            .map(|c| match c {
                ast::ProofCommand::Step(s) => usize::from(s.rule == rule),
                ast::ProofCommand::Subproof(s) => count(&s.commands, rule),
                ast::ProofCommand::Assume { .. } => 0,
            })
            .sum()
    }
    assert_eq!(count(&elaborated.commands, "poly_simp_rel"), 0);
    assert_eq!(count(&elaborated.commands, "la_generic"), 2);

    // The shared derivation lives at the top level, where both subproofs can see it
    let top_level: usize = elaborated
        .commands
        .iter()
        .filter(|c| matches!(c, ast::ProofCommand::Step(s) if s.rule == "la_generic"))
        .count();
    assert_eq!(top_level, 2);
}

/// A degenerate `eq_transitive`, whose chain has a single link, is closed by restating that link
/// with a one-premise `trans`, and not by flipping it twice with `symm`.
#[test]
/// `eq_transitive` is *core* since 2026-08-25 — the clausal variant of `trans` — so the pass keeps
/// it, degenerate instances included.
fn degenerate_eq_transitive() {
    let definitions = "
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
    ";
    let proof = "
        (step t1 (cl (not (= a b)) (not (= c d)) (= a b)) :rule eq_transitive)
        (step end (cl) :rule hole)
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "eq_transitive").count(), 1);
    assert_eq!(rules.iter().filter(|r| *r == "subproof").count(), 0);
}

/// `local`'s `eq_transitive` canonicalization drops the hypotheses the chain does not need — but
/// the rule requires at least three literals, so a chain needing only one premise must keep two.
#[test]
fn eq_transitive_canonicalization_keeps_two_hypotheses() {
    let definitions = "
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
    ";
    // The chain closes on the first hypothesis alone; the second is spare
    let proof = "
        (step t1 (cl (not (= a b)) (not (= b c)) (= a b)) :rule eq_transitive)
        (step end (cl) :rule hole :premises (t1))
    ";
    // The pass itself rechecks the output in elaborated granularity, so reaching here is the
    // assertion: before the clamp, the canonicalization emitted a two-literal `eq_transitive`,
    // which its own checker rejects
    let rules = run_pass(definitions, proof, elaborator::ElaborationPass::Local);
    assert!(rules.iter().any(|r| r == "eq_transitive"));
}

/// The `core-expensive` pass takes `poly_simp` to the antisymmetry pattern: two Farkas bounds and
/// `la_disequality`, with no ring normalization left.
#[test]
fn poly_simp_to_farkas_bounds() {
    let definitions = "
        (declare-const x Int)
        (declare-const y Int)
    ";
    let proof = "
        (step t1 (cl (= (+ x (* 2 y)) (+ (* 2 y) x))) :rule poly_simp)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert_eq!(rules.iter().filter(|r| *r == "poly_simp").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "la_disequality").count(), 1);
    assert_eq!(rules.iter().filter(|r| *r == "la_generic").count(), 2);
}

/// A nonlinear identity has no core route, so the step is kept.
#[test]
fn nonlinear_poly_simp_is_kept() {
    let definitions = "
        (declare-const x Int)
        (declare-const y Int)
    ";
    let proof = "
        (step t1 (cl (= (* x y) (* y x))) :rule poly_simp)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert_eq!(rules.iter().filter(|r| *r == "poly_simp").count(), 1);
}

/// `aci_simp` over a semilattice connective becomes the two clausal directions of the
/// equivalence, so no ACI normalization is left.
#[test]
fn aci_simp_to_clausal_equivalence() {
    let definitions = "
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
    ";
    for (lhs, rhs) in [
        ("(and p (and q r))", "(and r q p)"),
        ("(or p (or q r))", "(or r q p)"),
        ("(and p q true)", "(and q p)"),
    ] {
        let proof = format!(
            "(step t1 (cl (= {lhs} {rhs})) :rule aci_simp)\n(step end (cl) :rule hole :premises (t1))"
        );
        let rules = run_pass(
            definitions,
            &proof,
            elaborator::ElaborationPass::CoreExpensive,
        );
        assert_eq!(
            rules.iter().filter(|r| *r == "aci_simp").count(),
            0,
            "aci_simp survived for {lhs} = {rhs}"
        );
        assert_eq!(rules.iter().filter(|r| *r == "subproof").count(), 2);
    }
}

/// Scaling a comparison rests on `mult_pos`/`mult_neg` and the distributivity axiom, with no
/// `poly_simp` in the derivation.
#[test]
fn la_mult_uses_the_distributivity_axiom() {
    let definitions = "
        (declare-const x Int)
        (declare-const y Int)
        (declare-const m Int)
    ";
    for (rule, proof) in [
        (
            "la_mult_pos",
            "(step t1 (cl (=> (and (> m 0) (> x y)) (> (* m x) (* m y)))) :rule la_mult_pos)",
        ),
        (
            "la_mult_neg",
            "(step t1 (cl (=> (and (< m 0) (> x y)) (< (* m x) (* m y)))) :rule la_mult_neg)",
        ),
    ] {
        let proof = format!("{proof}\n(step end (cl) :rule hole :premises (t1))");
        let rules = run_core_pass(definitions, &proof);
        assert_eq!(rules.iter().filter(|r| *r == rule).count(), 0);
        assert_eq!(rules.iter().filter(|r| *r == "poly_simp").count(), 0);
        assert_eq!(rules.iter().filter(|r| *r == "mult_distrib").count(), 1);
        let axiom = if rule == "la_mult_pos" {
            "mult_pos"
        } else {
            "mult_neg"
        };
        assert_eq!(rules.iter().filter(|r| *r == axiom).count(), 1);
    }
}

/// `bind` reduces to the ∀-ε-clause plus a replay of its body at the witnesses, so the elaborated
/// proof carries no binder congruence — only `sko_forall`, `forall_inst` and clausal glue.
#[test]
fn bind_to_skolemization() {
    let definitions = "
        (declare-sort S 0)
        (declare-fun P (S) Bool)
    ";
    let proof = "
        (assume h1 (forall ((x S)) (P x)))
        (anchor :step t1 :args ((y S) (:= (x S) y)))
        (step t1.t1 (cl (= x y)) :rule refl)
        (step t1.t2 (cl (= (P x) (P y))) :rule cong :premises (t1.t1))
        (step t1 (cl (= (forall ((x S)) (P x)) (forall ((y S)) (P y)))) :rule bind)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert_eq!(rules.iter().filter(|r| *r == "bind").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "sko_forall").count(), 2);
    assert_eq!(rules.iter().filter(|r| *r == "forall_inst").count(), 2);
}

/// The generalized (∀-closure) form needs one direction only: the closure literal is Skolemized
/// and the body replayed there, with the other literals passing through.
#[test]
fn generalized_bind_to_skolemization() {
    let definitions = "
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun q () Bool)
    ";
    let proof = "
        (assume h1 q)
        (anchor :step t1 :args ((x S)))
        (step t1.t1 (cl (P x) (not q)) :rule hole)
        (step t1 (cl (forall ((x S)) (P x)) (not q)) :rule bind)
        (step t2 (cl (forall ((x S)) (P x))) :rule resolution :premises (t1 h1) :args (q false))
        (step end (cl) :rule hole :premises (t2))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert_eq!(rules.iter().filter(|r| *r == "bind").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "sko_forall").count(), 1);
}

/// A `bind` under an enclosing anchor is kept: the cumulative substitution would also reach the
/// terms the reduction builds.
#[test]
fn nested_bind_is_kept() {
    let definitions = "
        (declare-sort S 0)
        (declare-fun P (S S) Bool)
    ";
    let proof = "
        (anchor :step t1 :args ((v S) (:= (u S) v)))
        (anchor :step t1.t1 :args ((y S) (:= (x S) y)))
        (step t1.t1.t1 (cl (= (P x u) (P y v))) :rule hole)
        (step t1.t1 (cl (= (forall ((x S)) (P x u)) (forall ((y S)) (P y v)))) :rule bind)
        (step t1 (cl (= (forall ((u S)) (forall ((x S)) (P x u)))
                        (forall ((v S)) (forall ((y S)) (P y v))))) :rule bind)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert!(rules.iter().any(|r| r == "bind"));
}
