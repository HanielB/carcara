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
        parser::Source::from(problem),
        parser::Source::from(proof),
        None,
        parser::Config::new().allow_int_real_subtyping(true),
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

    let elab_config = elaborator::Config::new().uncrowd_rotation(true);
    let node = ast::ProofNodeForest::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
        .elaborate(node, std::path::Path::new("<test>"), vec![pass])
        .expect("elaboration failed");
    let elaborated = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        filename: proof.filename.clone(),
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
    // The α-renaming case: both sides Skolemize at the same witnesses, so four steps close it and
    // the body is not even looked at — no `forall_inst`, no replay
    assert_eq!(rules.iter().filter(|r| *r == "bind").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "sko_forall").count(), 2);
    assert_eq!(rules.iter().filter(|r| *r == "forall_inst").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "trans").count(), 1);
}

/// When the body genuinely rewrites, the two sides no longer Skolemize to the same term, so the
/// reduction falls back on instantiating the premise at the target's witnesses and replaying.
#[test]
fn rewriting_bind_replays_the_body() {
    let definitions = "
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun Q (S) Bool)
    ";
    let proof = "
        (anchor :step t1 :args ((y S) (:= (x S) y)))
        (step t1.t1 (cl (= (P x) (Q y))) :rule hole)
        (step t1 (cl (= (forall ((x S)) (P x)) (forall ((y S)) (Q y)))) :rule bind)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert_eq!(rules.iter().filter(|r| *r == "bind").count(), 0);
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

/// The inner α-renaming `bind` reduces even under the enclosing anchor (the judgment is
/// contextual, and the four-step route never inspects the body). The outer one is kept for now:
/// its two sides differ in a *nested* bound name, which the syntactic-renaming check does not
/// reach, and its replay route is blocked by the enclosing-anchor guard being vacuous here but
/// the body having become a `sko_forall` chain whose α-difference persists.
#[test]
fn nested_bind_inner_reduces() {
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
    // The inner `bind` is gone; the outer, α-differing in a nested bound name, is kept
    assert!(rules.iter().filter(|r| *r == "bind").count() <= 1);
    assert!(rules.iter().filter(|r| *r == "sko_forall").count() >= 2);
}

/// A *rewriting* `bind` under an enclosing anchor reduces too: its replay composes the enclosing
/// substitution with the witness one, transporting each of the body's terms through the context
/// before substituting the witnesses.
#[test]
fn nested_rewriting_bind_is_reduced() {
    let definitions = "
        (declare-sort S 0)
        (declare-fun P (S S) Bool)
        (declare-fun Q (S S) Bool)
    ";
    let proof = "
        (anchor :step t1 :args ((v S) (:= (u S) v)))
        (anchor :step t1.t1 :args ((y S) (:= (x S) y)))
        (step t1.t1.t1 (cl (= (P x u) (Q y v))) :rule hole)
        (step t1.t1 (cl (= (forall ((x S)) (P x u)) (forall ((y S)) (Q y v)))) :rule bind)
        (step t1 (cl (= (forall ((u S)) (forall ((x S)) (P x u)))
                        (forall ((v S)) (forall ((y S)) (Q y v))))) :rule bind)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_pass(
        definitions,
        proof,
        elaborator::ElaborationPass::CoreExpensive,
    );
    assert_eq!(rules.iter().filter(|r| *r == "bind").count(), 0);
    assert!(rules.iter().any(|r| r == "forall_inst"));
}

/// `bfun_elim`'s second step, on its own: the premise has no Boolean bindings, and the conclusion
/// only replaces the applications of a non-constant Boolean argument by their `ite` expansion.
/// The branches are subproof-free — `eq_congruent` and `eq_transitive` take the conditional
/// hypothesis as a literal, where `cong`/`trans` would want a unit premise and a discharge.
#[test]
fn bfun_elim_second_step() {
    let definitions = "
        (declare-fun f (Bool) Bool)
        (declare-fun a () Bool)
    ";
    let proof = "
        (assume h1 (f a))
        (step t1 (cl (ite a (f true) (f false))) :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    assert!(rules.iter().any(|r| r == "ite_then_intro"));
    assert!(rules.iter().any(|r| r == "ite_else_intro"));
    assert!(rules.iter().any(|r| r == "eq_congruent"));
    assert!(rules.iter().any(|r| r == "eq_transitive"));
    // No discharge subproof: the reduction never assumes the condition
    assert_eq!(rules.iter().filter(|r| *r == "subproof").count(), 0);
}

/// An application with several Boolean arguments expands into a *tree* of `ite`s, one level per
/// argument, and the reduction recurses with it: each level's branches chain through the level
/// below by `eq_transitive`.
#[test]
fn bfun_elim_nested_expansion() {
    let definitions = "
        (declare-fun g (Bool Bool Bool) Bool)
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (declare-fun c () Bool)
    ";
    let proof = "
        (assume h1 (g a b c))
        (step t1 (cl (ite a
            (ite b
                (ite c (g true true true) (g true true false))
                (ite c (g true false true) (g true false false)))
            (ite b
                (ite c (g false true true) (g false true false))
                (ite c (g false false true) (g false false false)))
        )) :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    // One `refl` per untouched argument of each `eq_congruent`, which needs a literal for each
    assert!(rules.iter().any(|r| r == "refl"));
    assert_eq!(rules.iter().filter(|r| *r == "subproof").count(), 0);
}

/// Both steps at once: the Boolean bindings expand into the conjunction of the instances, and the
/// applications in the instances then expand into `ite`s. The implication of the first step and
/// the equivalence of the second are crossed by `equiv_pos2`.
#[test]
fn bfun_elim_both_steps() {
    let definitions = "
        (declare-fun g (Bool Bool Bool) Bool)
        (declare-fun a () Bool)
    ";
    let proof = "
        (assume h1 (forall ((x Bool) (y Bool)) (g x a y)))
        (step t1 (cl (and
            (ite a (g false true false) (g false false false))
            (ite a (g true true false) (g true false false))
            (ite a (g false true true) (g false false true))
            (ite a (g true true true) (g true false true))
        )) :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "forall_inst").count(), 4);
    assert!(rules.iter().any(|r| r == "and_neg"));
    assert!(rules.iter().any(|r| r == "equiv_pos2"));
    assert!(rules.iter().any(|r| r == "ite_then_intro"));
}

/// An expansion under a quantifier: the argument mentions the bound variable, so the equality
/// cannot be derived outside, and the congruence crosses the binder with a `bind` subproof.
#[test]
fn bfun_elim_expansion_under_a_quantifier() {
    let definitions = "
        (declare-fun f (Bool) Bool)
        (declare-fun p (Int) Bool)
    ";
    let proof = "
        (assume h1 (forall ((x Int)) (f (p x))))
        (step t1 (cl (forall ((x Int)) (ite (p x) (f true) (f false))))
            :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "bind").count(), 1);
}

/// A Boolean quantifier *below a connective*: the first step is not at the top of the premise, so
/// it is derived as an equivalence and carried to its position by `cong`.
#[test]
fn bfun_elim_below_a_connective() {
    let definitions = "
        (declare-fun p (Int Bool) Bool)
        (declare-fun q () Bool)
    ";
    let proof = "
        (assume h1 (or q (forall ((x Bool)) (p 1 x))))
        (step t1 (cl (or q (and (p 1 false) (p 1 true)))) :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    // The equivalence: the → direction instantiates, the ← direction case splits and closes
    assert_eq!(rules.iter().filter(|r| *r == "forall_inst").count(), 2);
    assert!(rules.iter().any(|r| r == "and_pos"));
    assert!(rules.iter().any(|r| r == "bind"));
}

/// A Boolean quantifier nested under a non-Boolean one: the expansion happens under the outer
/// binder, so the equivalence is carried through it by `bind`.
#[test]
fn bfun_elim_nested_quantifier() {
    let definitions = "
        (declare-fun p (Int Bool) Bool)
    ";
    let proof = "
        (assume h1 (forall ((y Int)) (forall ((x Bool)) (p y x))))
        (step t1 (cl (forall ((y Int)) (and (p y false) (p y true))))
            :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    assert!(rules.iter().filter(|r| *r == "bind").count() >= 2);
}

/// An `exists` premise expands through the quantifier duality: the instances are packed as
/// `(not (or …))` on the `forall` side, which is what turns back into a disjunction with no De
/// Morgan step in between.
#[test]
fn bfun_elim_exists_premise() {
    let definitions = "
        (declare-fun f (Bool) Bool)
    ";
    let proof = "
        (assume h1 (exists ((x Bool)) (f x)))
        (step t1 (cl (or (f false) (f true))) :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    assert!(rules.iter().any(|r| r == "connective_def"));
    assert!(rules.iter().any(|r| r == "or_pos"));
    assert!(rules.iter().any(|r| r == "or_neg"));
}

/// The same, with a non-Boolean variable left behind: the disjunction stays under an `exists`, so
/// both dualities are real quantifier ones.
#[test]
fn bfun_elim_exists_with_a_remaining_variable() {
    let definitions = "
        (declare-fun r (Int Bool) Bool)
    ";
    let proof = "
        (assume h1 (exists ((y Int) (x Bool)) (r y x)))
        (step t1 (cl (exists ((y Int)) (or (r y false) (r y true))))
            :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    assert_eq!(rules.iter().filter(|r| *r == "connective_def").count(), 2);
}

/// A Boolean quantifier below the top whose variable occurs *under a binder* of its body. The
/// case split's hypotheses are assumed, so the rewriting is a unit congruence, and the vanilla
/// `bind` carries it through the inner quantifier.
#[test]
fn bfun_elim_case_split_under_a_binder() {
    let definitions = "
        (declare-fun p (Int Bool) Bool)
        (declare-fun q () Bool)
    ";
    let proof = "
        (assume h1 (or q (forall ((x Bool)) (forall ((z Int)) (p z x)))))
        (step t1 (cl (or q (and (forall ((z Int)) (p z false)) (forall ((z Int)) (p z true)))))
            :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    // The ← direction's case split is a discharge subproof now, one per branch
    assert_eq!(rules.iter().filter(|r| *r == "subproof").count(), 2);
    assert!(rules.iter().any(|r| r == "not_not"));
}

/// The same, with the inner quantifier itself Boolean: the crossing is followed by a nested first
/// step on what the expansion produced.
#[test]
fn bfun_elim_case_split_under_a_boolean_binder() {
    let definitions = "
        (declare-fun p (Bool Bool) Bool)
        (declare-fun q () Bool)
    ";
    let proof = "
        (assume h1 (or q (forall ((x Bool)) (forall ((y Bool)) (p x y)))))
        (step t1 (cl (or q (and (and (p false false) (p false true))
                                (and (p true false) (p true true)))))
            :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
}

/// A Boolean binding that does not occur in the body makes two assignments produce the *same*
/// instance. The conjunction the rule builds keeps both, but resolution reads a clause as a set,
/// so the repacking discharges each distinct instance once.
#[test]
fn bfun_elim_repeated_instances() {
    let definitions = "
        (declare-fun p (Int Bool) Bool)
    ";
    let proof = "
        (assume h1 (forall ((x Bool) (z Bool)) (p 1 x)))
        (step t1 (cl (and (p 1 false) (p 1 true) (p 1 false) (p 1 true)))
            :rule bfun_elim :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert_eq!(rules.iter().filter(|r| *r == "bfun_elim").count(), 0);
    // Two distinct instances, so two instantiations rather than four
    assert_eq!(rules.iter().filter(|r| *r == "forall_inst").count(), 2);
}

/// `ite_intro`'s selection tautologies come straight from the term-`ite` selection axioms: no
/// discharge subproof, and no `rare_rewrite` — so the output checks without a RARE file. veriT
/// writes the equalities with the `ite` on the right, which is the flipped orientation.
#[test]
fn ite_intro_on_the_selection_axioms() {
    let definitions = "
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Bool)
    ";
    let flipped = "
        (assume h1 (= (f (ite c a b)) 0))
        (step t1 (cl (= (= (f (ite c a b)) 0)
                        (and (= (f (ite c a b)) 0) (ite c (= a (ite c a b)) (= b (ite c a b))))))
            :rule ite_intro)
        (step end (cl) :rule hole :premises (t1))
    ";
    let direct = "
        (assume h1 (= (f (ite c a b)) 0))
        (step t1 (cl (= (= (f (ite c a b)) 0)
                        (and (= (f (ite c a b)) 0) (ite c (= (ite c a b) a) (= (ite c a b) b)))))
            :rule ite_intro)
        (step end (cl) :rule hole :premises (t1))
    ";
    for proof in [flipped, direct] {
        let rules = run_core_pass(definitions, proof);
        assert_eq!(rules.iter().filter(|r| *r == "ite_intro").count(), 0);
        assert_eq!(rules.iter().filter(|r| *r == "rare_rewrite").count(), 0);
        assert_eq!(rules.iter().filter(|r| *r == "subproof").count(), 0);
        assert!(rules.iter().any(|r| r == "ite_then_intro"));
        assert!(rules.iter().any(|r| r == "ite_else_intro"));
    }
}

/// The legacy AC names are relabeled to the structural rule of their operator: `aci_simp` and
/// `absorb` become `semilattice_simp`, `boolean_group_simp`, `assoc_simp` or `poly_simp`, and
/// none of the legacy names survives the core pass.
#[test]
fn legacy_ac_rules_become_structural() {
    let definitions = "
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
    ";
    let cases: &[(&str, &str, &str)] = &[
        // (legacy step, expected structural rule, legacy name)
        ("(step t1 (cl (= (and p (and q r)) (and r q p))) :rule aci_simp)", "semilattice_simp", "aci_simp"),
        ("(step t1 (cl (= (or p false q) (or q p))) :rule aci_simp)", "semilattice_simp", "aci_simp"),
        // (a legacy `aci_simp` can only reorder `bvxor`, never cancel a pair — the parity law is
        // `boolean_group_simp`'s own; so the legacy input is a reordering)
        ("(step t1 (cl (= (bvxor a (bvxor b a)) (bvxor b a a))) :rule aci_simp)", "boolean_group_simp", "aci_simp"),
        ("(step t1 (cl (= (bvxor a b) (bvxor b a))) :rule aci_simp)", "boolean_group_simp", "aci_simp"),
        ("(step t1 (cl (= (concat (concat a b) a) (concat a b a))) :rule aci_simp)", "assoc_simp", "aci_simp"),
        ("(step t1 (cl (= (+ x (+ y x)) (+ x x y))) :rule aci_simp)", "poly_simp", "aci_simp"),
        ("(step t1 (cl (= (* x y 1) (* y x))) :rule aci_simp)", "poly_simp", "aci_simp"),
        ("(step t1 (cl (= (and p false q) false)) :rule absorb)", "semilattice_simp", "absorb"),
        ("(step t1 (cl (= (or p true) true)) :rule absorb)", "semilattice_simp", "absorb"),
        ("(step t1 (cl (= (bvand a #b0000) #b0000)) :rule absorb)", "semilattice_simp", "absorb"),
    ];
    for (step, expected, legacy) in cases {
        let proof = format!("{step}\n(step end (cl) :rule hole :premises (t1))");
        let rules = run_core_pass(definitions, &proof);
        assert!(
            rules.iter().any(|r| r == expected),
            "{legacy} was not relabeled to {expected} for: {step} (got {rules:?})"
        );
        assert!(
            !rules.iter().any(|r| r == legacy),
            "{legacy} survived for: {step} (got {rules:?})"
        );
    }
}

/// veriT's premise-carrying `ac_simp`: the step checks by reading its premises as sub-rewrites,
/// and elaborates into the premise's congruence glued to the structural layers.
#[test]
fn ac_simp_with_premises() {
    let definitions = "
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
    ";
    let proof = "
        (assume h1 (= a b))
        (step t1 (cl (= (and (and a c) c) (and b c))) :rule ac_simp :premises (h1))
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert!(!rules.iter().any(|r| r == "ac_simp"), "ac_simp survived: {rules:?}");
    assert!(rules.iter().any(|r| r == "cong"), "expected the premise to be lifted: {rules:?}");
    assert!(
        rules.iter().any(|r| r == "semilattice_simp"),
        "expected the flattening layer: {rules:?}"
    );
}

/// An `ac_simp` whose conclusion veriT left under-flattened: it checks by the meet-in-the-middle
/// fallback, and elaborates into per-layer structural steps glued by `cong`/`trans`/`symm`, with
/// no `ac_simp` left for the consumer.
#[test]
fn ac_simp_under_flattened_conclusion() {
    let definitions = "
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
        (declare-const s Bool)
    ";
    // the nested `(and (and p q) r)` under the `=` is left alone on both sides
    let proof = "
        (step t1 (cl (= (or (= (and (and p q) r) s) (or p q))
                        (or (= (and (and p q) r) s) p q))) :rule ac_simp)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert!(!rules.iter().any(|r| r == "ac_simp"), "ac_simp survived: {rules:?}");
    assert!(
        rules.iter().any(|r| r == "semilattice_simp"),
        "expected the flattening layers: {rules:?}"
    );
}

/// A nested `ac_simp` is decomposed layer by layer, each layer a `semilattice_simp` step lifted by
/// `cong`, with no legacy AC name left.
#[test]
fn ac_simp_layers_are_semilattice_simp() {
    let definitions = "
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
        (declare-const s Bool)
    ";
    let proof = "
        (step t1 (cl (= (or (and (and p q) r) (or s s)) (or (and p q r) s))) :rule ac_simp)
        (step end (cl) :rule hole :premises (t1))
    ";
    let rules = run_core_pass(definitions, proof);
    assert!(!rules.iter().any(|r| r == "ac_simp"), "ac_simp survived: {rules:?}");
    assert!(!rules.iter().any(|r| r == "aci_simp"), "aci_simp emitted: {rules:?}");
    assert!(
        rules.iter().filter(|r| *r == "semilattice_simp").count() >= 2,
        "expected a semilattice_simp per changed layer: {rules:?}"
    );
}
