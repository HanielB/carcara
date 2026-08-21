//! Tests for the rewrite-vocabulary reductions of the `core` pass: the `core-taut` regime
//! (everything to the core plus the term-`ite` selection axioms) and the `core-simp-rare` regime
//! (`*_simplify` to chains of `rare_rewrite`/`evaluate` lemmas).

use carcara::{ast, checker, elaborator, parser};

/// The RARE rules the tests need: the extended `*_simplify` file shipped with the repository,
/// plus the handful of `rewrites.eo` rules the cases instantiate.
fn rare_rules_text() -> String {
    let extended = include_str!("../../rare-tests/rare/simplify-rules.eo");
    let from_rewrites_eo = r#"
(declare-rare-rule eq-refl ((@T0 Type) (t1 @T0))
  :args (t1)
  :conclusion (= (= t1 t1) true)
)
(declare-rare-rule eq-symm ((@T0 Type) (@T1 Type) (t1 @T0) (s1 @T1))
  :args (t1 s1)
  :conclusion (= (= t1 s1) (= s1 t1))
)
(declare-rare-rule bool-double-not-elim ((t1 Bool))
  :args (t1)
  :conclusion (= (not (not t1)) t1)
)
(declare-rare-rule bool-eq-true ((t1 Bool))
  :args (t1)
  :conclusion (= (= t1 true) t1)
)
(declare-rare-rule bool-eq-false ((t1 Bool))
  :args (t1)
  :conclusion (= (= t1 false) (not t1))
)
(declare-rare-rule bool-eq-nrefl ((x1 Bool))
  :args (x1)
  :conclusion (= (= x1 (not x1)) false)
)
(declare-rare-rule bool-and-conf ((xs1 Bool :list) (w1 Bool) (ys1 Bool :list) (zs1 Bool :list))
  :args (xs1 w1 ys1 zs1)
  :conclusion (= (and xs1 w1 ys1 (not w1) zs1) false)
)
(declare-rare-rule bool-or-taut ((xs1 Bool :list) (w1 Bool) (ys1 Bool :list) (zs1 Bool :list))
  :args (xs1 w1 ys1 zs1)
  :conclusion (= (or xs1 w1 ys1 (not w1) zs1) true)
)
(declare-rare-rule bool-impl-elim ((t1 Bool) (s1 Bool))
  :args (t1 s1)
  :conclusion (= (=> t1 s1) (or (not t1) s1))
)
(declare-rare-rule bool-implies-de-morgan ((x1 Bool) (y1 Bool))
  :args (x1 y1)
  :conclusion (= (not (=> x1 y1)) (and x1 (not y1)))
)
(declare-rare-rule ite-true-cond ((@T0 Type) (@T1 Type) (x1 @T0) (y1 @T1))
  :args (x1 y1)
  :conclusion (= (ite true x1 y1) x1)
)
(declare-rare-rule ite-false-cond ((@T0 Type) (@T1 Type) (x1 @T0) (y1 @T1))
  :args (x1 y1)
  :conclusion (= (ite false x1 y1) y1)
)
(declare-rare-rule ite-not-cond ((@T0 Type) (@T1 Type) (c1 Bool) (x1 @T0) (y1 @T1))
  :args (c1 x1 y1)
  :conclusion (= (ite (not c1) x1 y1) (ite c1 y1 x1))
)
(declare-rare-rule ite-eq-branch ((@T0 Type) (c1 Bool) (x1 @T0))
  :args (c1 x1)
  :conclusion (= (ite c1 x1 x1) x1)
)
(declare-rare-rule arith-elim-lt ((@T0 Type) (@T1 Type) (t1 @T0) (s1 @T1))
  :args (t1 s1)
  :conclusion (= (< t1 s1) (not (>= t1 s1)))
)
(declare-rare-rule arith-leq-norm ((t1 Int) (s1 Int))
  :args (t1 s1)
  :conclusion (= (<= t1 s1) (not (>= t1 (+ s1 1))))
)
(declare-rare-rule arith-geq-tighten ((t1 Int) (s1 Int))
  :args (t1 s1)
  :conclusion (= (not (>= t1 s1)) (>= s1 (+ t1 1)))
)
(declare-rare-rule arith-eq-elim-int ((t1 Int) (s1 Int))
  :args (t1 s1)
  :conclusion (= (= t1 s1) (and (>= t1 s1) (<= t1 s1)))
)
(declare-rare-rule or-not-refl ((T0 Type) (t @T0) (xs Bool :list))
   :args (t xs)
   :conclusion (= (or (not (= t t)) xs) (or xs))
)
(declare-rare-rule distinct-false ((@T0 Type) (t @T0) (xs @T0 :list) (ys @T0 :list) (zs @T0 :list))
   :args (t xs ys zs)
   :conclusion (= (distinct xs t ys t zs) false)
)
(declare-rare-rule ite-eq ((@T0 Type) (C Bool) (t1 @T0) (t2 @T1))
  :args (C t1 t2)
  :conclusion (= (ite C (= (ite C t1 t2) t1) (= (ite C t1 t2) t2)) true)
)
(declare-rare-rule ite-then-true ((c1 Bool) (x1 Bool))
  :args (c1 x1)
  :conclusion (= (ite c1 true x1) (or c1 x1))
)
(declare-rare-rule ite-then-lookahead ((@T0 Type) (@T1 Type) (@T2 Type) (c1 Bool) (x1 @T0) (y1 @T1) (z1 @T2))
  :args (c1 x1 y1 z1)
  :conclusion (= (ite c1 (ite c1 x1 y1) z1) (ite c1 x1 z1))
)
(declare-rare-rule ite-else-lookahead ((@T0 Type) (@T1 Type) (@T2 Type) (c1 Bool) (x1 @T0) (y1 @T1) (z1 @T2))
  :args (c1 x1 y1 z1)
  :conclusion (= (ite c1 x1 (ite c1 y1 z1)) (ite c1 x1 z1))
)
"#;
    format!("{extended}\n{from_rewrites_eo}")
}

/// Elaborates a proof with the given pass, re-checks the result at elaborated granularity, and
/// returns the rules used in it.
fn run_pass(pass: elaborator::ElaborationPass, definitions: &str, proof: &str) -> Vec<String> {
    let rules_text = rare_rules_text();
    let (mut problem, proof, rare_rules, mut pool) = parser::parse_instance(
        definitions,
        proof,
        Some(&rules_text),
        parser::Config {
            allow_int_real_subtyping: true,
            ..Default::default()
        },
    )
    .unwrap();
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
        rare_rules: Some(rare_rules.clone()),
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

const DEFINITIONS: &str = "
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const r Bool)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const a Int)
    (declare-const b Int)
";

fn simplify_cases() -> Vec<&'static str> {
    vec![
        // ite_simplify
        "(step t1 (cl (= (ite p true false) p)) :rule ite_simplify)",
        "(step t1 (cl (= (ite (not p) a b) (ite p b a))) :rule ite_simplify)",
        "(step t1 (cl (= (ite p a a) a)) :rule ite_simplify)",
        "(step t1 (cl (= (ite p true q) (or p q))) :rule ite_simplify)",
        "(step t1 (cl (= (ite true a b) a)) :rule ite_simplify)",
        "(step t1 (cl (= (ite p (ite p a b) b) (ite p a b))) :rule ite_simplify)",
        // eq_simplify
        "(step t1 (cl (= (= x x) true)) :rule eq_simplify)",
        "(step t1 (cl (= (= 1 2) false)) :rule eq_simplify)",
        "(step t1 (cl (= (not (= 1 1)) false)) :rule eq_simplify)",
        // not_simplify
        "(step t1 (cl (= (not (not p)) p)) :rule not_simplify)",
        "(step t1 (cl (= (not false) true)) :rule not_simplify)",
        "(step t1 (cl (= (not (not (not p))) (not p))) :rule not_simplify)",
        // implies_simplify
        "(step t1 (cl (= (=> (not p) (not q)) (=> q p))) :rule implies_simplify)",
        "(step t1 (cl (= (=> p p) true)) :rule implies_simplify)",
        "(step t1 (cl (= (=> false p) true)) :rule implies_simplify)",
        "(step t1 (cl (= (=> p false) (not p))) :rule implies_simplify)",
        "(step t1 (cl (= (=> (not p) p) p)) :rule implies_simplify)",
        // equiv_simplify
        "(step t1 (cl (= (= p p) true)) :rule equiv_simplify)",
        "(step t1 (cl (= (= p (not p)) false)) :rule equiv_simplify)",
        "(step t1 (cl (= (= (not p) p) false)) :rule equiv_simplify)",
        "(step t1 (cl (= (= p true) p)) :rule equiv_simplify)",
        "(step t1 (cl (= (= false p) (not p))) :rule equiv_simplify)",
        "(step t1 (cl (= (= (not p) (not q)) (= p q))) :rule equiv_simplify)",
        // bool_simplify
        "(step t1 (cl (= (not (=> p q)) (and p (not q)))) :rule bool_simplify)",
        "(step t1 (cl (= (not (or p q)) (and (not p) (not q)))) :rule bool_simplify)",
        "(step t1 (cl (= (=> p (=> q r)) (=> (and p q) r))) :rule bool_simplify)",
        "(step t1 (cl (= (=> p (=> p r)) (=> (and p p) r))) :rule bool_simplify)",
        "(step t1 (cl (= (and p (=> p q)) (and p q))) :rule bool_simplify)",
        // comp_simplify
        "(step t1 (cl (= (< x y) (not (<= y x)))) :rule comp_simplify)",
        "(step t1 (cl (= (>= x y) (<= y x))) :rule comp_simplify)",
        "(step t1 (cl (= (> x y) (not (<= x y)))) :rule comp_simplify)",
        "(step t1 (cl (= (<= x x) true)) :rule comp_simplify)",
        "(step t1 (cl (= (< 1 2) true)) :rule comp_simplify)",
        // and_simplify
        "(step t1 (cl (= (and p true q) (and p q))) :rule and_simplify)",
        "(step t1 (cl (= (and p (not p)) false)) :rule and_simplify)",
        "(step t1 (cl (= (and (not p) q p) false)) :rule and_simplify)",
        "(step t1 (cl (= (and p p) p)) :rule and_simplify)",
        "(step t1 (cl (= (and p false q) false)) :rule and_simplify)",
        "(step t1 (cl (= (and true p) p)) :rule and_simplify)",
        "(step t1 (cl (= (and (and p q r)) (and p q r))) :rule and_simplify)",
        // or_simplify
        "(step t1 (cl (= (or p false q) (or p q))) :rule or_simplify)",
        "(step t1 (cl (= (or p (not p)) true)) :rule or_simplify)",
        "(step t1 (cl (= (or p true q) true)) :rule or_simplify)",
        "(step t1 (cl (= (or p p q) (or p q))) :rule or_simplify)",
        "(step t1 (cl (= (or false p) p)) :rule or_simplify)",
        // the arithmetic bundles rename to poly_simp
        "(step t1 (cl (= (* 1 (* 2 x)) (* 2 x))) :rule prod_simplify)",
        "(step t1 (cl (= (+ x 0 y) (+ x y))) :rule sum_simplify)",
        "(step t1 (cl (= (- x x) 0)) :rule minus_simplify)",
    ]
}

fn taut_only_cases() -> Vec<&'static str> {
    vec![
        // evaluate
        "(step t1 (cl (= (+ 1 2) 3)) :rule evaluate)",
        "(step t1 (cl (= (< 1 2) true)) :rule evaluate)",
        "(step t1 (cl (= (>= 1 2) false)) :rule evaluate)",
        "(step t1 (cl (= (= 1 1) true)) :rule evaluate)",
        "(step t1 (cl (= (= 1 2) false)) :rule evaluate)",
        "(step t1 (cl (= (not (= 1 1)) false)) :rule evaluate)",
        "(step t1 (cl (= (and true (< 0 1)) true)) :rule evaluate)",
        "(step t1 (cl (= (or false (< 1 0)) false)) :rule evaluate)",
        "(step t1 (cl (= (=> true (< 1 0)) false)) :rule evaluate)",
        "(step t1 (cl (= (ite (< 0 1) 5 7) 5)) :rule evaluate)",
        "(step t1 (cl (= (* 3 (- 2 5)) -9)) :rule evaluate)",
        // rare_rewrite over the corpus rules
        "(step t1 (cl (= (< x y) (not (>= x y)))) :rule rare_rewrite :args (\"arith-elim-lt\" x y))",
        "(step t1 (cl (= (<= x y) (not (>= x (+ y 1))))) :rule rare_rewrite :args (\"arith-leq-norm\" x y))",
        "(step t1 (cl (= (not (>= x y)) (>= y (+ x 1)))) :rule rare_rewrite :args (\"arith-geq-tighten\" x y))",
        "(step t1 (cl (= (= x y) (and (>= x y) (<= x y)))) :rule rare_rewrite :args (\"arith-eq-elim-int\" x y))",
        "(step t1 (cl (= (= x y) (= y x))) :rule rare_rewrite :args (\"eq-symm\" x y))",
        "(step t1 (cl (= (= x x) true)) :rule rare_rewrite :args (\"eq-refl\" x))",
        "(step t1 (cl (= (not (not p)) p)) :rule rare_rewrite :args (\"bool-double-not-elim\" p))",
        "(step t1 (cl (= (= p true) p)) :rule rare_rewrite :args (\"bool-eq-true\" p))",
        "(step t1 (cl (= (= p false) (not p))) :rule rare_rewrite :args (\"bool-eq-false\" p))",
        "(step t1 (cl (= (=> p q) (or (not p) q))) :rule rare_rewrite :args (\"bool-impl-elim\" p q))",
        "(step t1 (cl (= (not (=> p q)) (and p (not q)))) :rule rare_rewrite
            :args (\"bool-implies-de-morgan\" p q))",
        "(step t1 (cl (= (ite true a b) a)) :rule rare_rewrite :args (\"ite-true-cond\" a b))",
        "(step t1 (cl (= (ite false a b) b)) :rule rare_rewrite :args (\"ite-false-cond\" a b))",
        "(step t1 (cl (= (ite (not p) a b) (ite p b a))) :rule rare_rewrite
            :args (\"ite-not-cond\" p a b))",
        "(step t1 (cl (= (ite p a a) a)) :rule rare_rewrite :args (\"ite-eq-branch\" p a))",
        "(step t1 (cl (= (ite p (= (ite p a b) a) (= (ite p a b) b)) true)) :rule rare_rewrite
            :args (\"ite-eq\" p a b))",
        "(step t1 (cl (= (ite p true q) (or p q))) :rule rare_rewrite
            :args (\"ite-then-true\" p q))",
        "(step t1 (cl (= (or (not (= x x)) p q) (or p q))) :rule rare_rewrite
            :args (\"or-not-refl\" x (rare-list p q)))",
        "(step t1 (cl (= (distinct x y x) false)) :rule rare_rewrite
            :args (\"distinct-false\" x rare-list (rare-list y) rare-list))",
    ]
}

#[test]
fn core_taut_reduces_the_rewrite_vocabulary() {
    let forbidden = [
        "ite_simplify",
        "eq_simplify",
        "not_simplify",
        "implies_simplify",
        "equiv_simplify",
        "bool_simplify",
        "comp_simplify",
        "and_simplify",
        "or_simplify",
        "prod_simplify",
        "sum_simplify",
        "minus_simplify",
        "evaluate",
        "rare_rewrite",
    ];
    for case in simplify_cases().into_iter().chain(taut_only_cases()) {
        let case = &format!("{case}\n(step end (cl) :rule hole)");
        let rules = run_pass(elaborator::ElaborationPass::CoreTaut, DEFINITIONS, case);
        for rule in &rules {
            assert!(
                !forbidden.contains(&rule.as_str()),
                "'{rule}' left in the output of: {case}"
            );
        }
    }
}

#[test]
fn core_simp_rare_reduces_the_simplify_rules() {
    let forbidden = [
        "ite_simplify",
        "eq_simplify",
        "not_simplify",
        "implies_simplify",
        "equiv_simplify",
        "bool_simplify",
        "comp_simplify",
        "and_simplify",
        "or_simplify",
        "prod_simplify",
        "sum_simplify",
        "minus_simplify",
    ];
    for case in simplify_cases() {
        let case = &format!("{case}\n(step end (cl) :rule hole)");
        let rules = run_pass(elaborator::ElaborationPass::CoreSimpRare, DEFINITIONS, case);
        for rule in &rules {
            assert!(
                !forbidden.contains(&rule.as_str()),
                "'{rule}' left in the output of: {case}"
            );
        }
    }
}
