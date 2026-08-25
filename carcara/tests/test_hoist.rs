use carcara::{ast, checker, elaborator, parser};

/// Parses a problem and a proof, checks the proof, and returns everything the tests need.
fn parse(
    problem: &str,
    proof: &str,
) -> (
    ast::Problem,
    ast::Proof,
    ast::rare_rules::Rules,
    ast::PrimitivePool,
) {
    let (mut problem, proof, rare_rules, pool) = parser::parse_instance(
        problem,
        proof,
        None,
        parser::Config {
            allow_int_real_subtyping: true,
            ..Default::default()
        },
    )
    .unwrap();

    // The cases use `assume` commands to introduce premises, so the assumed terms are
    // retroactively added as the problem's premises, as the rule tests do
    problem.premises = proof
        .commands
        .iter()
        .filter_map(|c| match c {
            ast::ProofCommand::Assume { term, .. } => Some(term.clone()),
            _ => None,
        })
        .collect();
    (problem, proof, rare_rules, pool)
}

/// Runs the `deep-hoist` pass, which additionally collapses lemma scopes.
fn run_deep_hoist_pass(problem: &str, proof: &str, config: checker::Config) -> ast::Proof {
    run_pass(problem, proof, config, elaborator::ElaborationPass::DeepHoist)
}

/// Runs the `hoist` pass on a proof and returns the result. The input is checked before the pass and
/// the output after it, both with the given configuration.
fn run_hoist_pass(problem: &str, proof: &str, config: checker::Config) -> ast::Proof {
    run_pass(problem, proof, config, elaborator::ElaborationPass::Hoist)
}

fn run_pass(
    problem: &str,
    proof: &str,
    config: checker::Config,
    pass: elaborator::ElaborationPass,
) -> ast::Proof {
    let (problem, proof, rare_rules, mut pool) = parse(problem, proof);

    let holey = checker::ProofChecker::new(&mut pool, &rare_rules, config.clone())
        .check(&problem, &proof)
        .expect("original proof does not check");

    let elab_config = elaborator::Config {
        allowed_rules: config.allowed_rules.clone(),
        ..Default::default()
    };
    let node = ast::ProofNodeForest::from_commands(proof.commands.clone());
    let hoisted_node = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
        .elaborate(node, vec![pass])
        .expect("hoisting failed");
    let hoisted = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: hoisted_node.into_commands(),
    };

    let holey_after = checker::ProofChecker::new(&mut pool, &rare_rules, config)
        .check(&problem, &hoisted)
        .expect("hoisted proof does not check");
    assert_eq!(
        holey, holey_after,
        "hoisting changed whether the proof is holey"
    );

    hoisted
}

/// The ids of the steps of a proof, in order, with the ids of a subproof's steps nested under it.
fn step_ids(commands: &[ast::ProofCommand]) -> Vec<String> {
    let mut result = Vec::new();
    for c in commands {
        match c {
            ast::ProofCommand::Step(s) => result.push(s.id.clone()),
            ast::ProofCommand::Subproof(s) => result.extend(step_ids(&s.commands)),
            ast::ProofCommand::Assume { .. } => (),
        }
    }
    result
}

/// The ids of the top-level steps of a proof that use the given rule.
fn top_level_with_rule(proof: &ast::Proof, rule: &str) -> Vec<String> {
    proof
        .commands
        .iter()
        .filter_map(|c| match c {
            ast::ProofCommand::Step(s) if s.rule == rule => Some(s.id.clone()),
            _ => None,
        })
        .collect()
}

fn count_rule(commands: &[ast::ProofCommand], rule: &str) -> usize {
    commands
        .iter()
        .map(|c| match c {
            ast::ProofCommand::Step(s) => usize::from(s.rule == rule),
            ast::ProofCommand::Subproof(s) => count_rule(&s.commands, rule),
            ast::ProofCommand::Assume { .. } => 0,
        })
        .sum()
}

const DEFS: &str = "
    (declare-const x Int)
    (declare-const y Int)
    (declare-const p Bool)
    (declare-const q Bool)
";

/// A closed step that two subproofs both prove is derived once, at the top level, and both
/// subproofs use it from there.
#[test]
fn duplicate_in_two_subproofs_is_shared() {
    // The `evaluate` step cannot be the last step before the one that closes the subproof, since
    // that one refers to it by its position; the `contraction` step stands in between
    let subproof = |i: usize| {
        format!(
            "(anchor :step t{i})
             (assume t{i}.h1 p)
             (step t{i}.t1 (cl (= (+ 1 1) 2)) :rule evaluate)
             (step t{i}.t2 (cl (= (+ 1 1) 2)) :rule contraction :premises (t{i}.t1))
             (step t{i} (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t{i}.h1))"
        )
    };
    let proof = format!(
        "(assume a0 p)\n{}\n{}\n(step end (cl) :rule hole)",
        subproof(1),
        subproof(2)
    );

    let hoisted = run_hoist_pass(DEFS, &proof, checker::Config::new());

    // The two `evaluate` steps became one, at the top level
    assert_eq!(count_rule(&hoisted.commands, "evaluate"), 1);
    assert_eq!(top_level_with_rule(&hoisted, "evaluate").len(), 1);

    // Which is one step less than the proof had
    let before = step_ids(&parse(DEFS, &proof).1.commands).len();
    assert_eq!(step_ids(&hoisted.commands).len(), before - 1);
}

/// A step that depends on an assumption of its subproof is not closed, so it stays where it is even
/// if another subproof proves the same clause.
#[test]
fn duplicate_depending_on_an_assumption_is_not_shared() {
    let subproof = |i: usize| {
        format!(
            "(anchor :step t{i})
             (assume t{i}.h1 (= (+ 1 1) 2))
             (step t{i}.t1 (cl (= (+ 1 1) 2)) :rule contraction :premises (t{i}.h1))
             (step t{i}.t2 (cl (= (+ 1 1) 2)) :rule contraction :premises (t{i}.t1))
             (step t{i} (cl (not (= (+ 1 1) 2)) (= (+ 1 1) 2)) :rule subproof \
              :discharge (t{i}.h1))"
        )
    };
    let proof = format!(
        "{}\n{}\n(step end (cl) :rule hole)",
        subproof(1),
        subproof(2)
    );

    let hoisted = run_hoist_pass(DEFS, &proof, checker::Config::new());

    // Both copies are still there, and neither was lifted to the top level
    assert_eq!(count_rule(&hoisted.commands, "contraction"), 4);
    assert!(top_level_with_rule(&hoisted, "contraction").is_empty());
    assert_eq!(
        step_ids(&hoisted.commands),
        step_ids(&parse(DEFS, &proof).1.commands)
    );
}

/// A step of a context subproof whose conclusion mentions a variable the anchor binds is not
/// context-free: it must not be lifted, and must not be replaced by a step from outside the anchor
/// that happens to conclude the same term about a different `x`.
#[test]
fn context_dependent_duplicate_is_not_shared() {
    let definitions = "
        (declare-const x Int)
        (declare-fun f (Int) Bool)
    ";
    // The anchor declares a variable that shadows the constant `x`, so the `refl` step inside
    // proves something about the bound `x` and the one outside about the constant
    let proof = "
        (step t1 (cl (= x x)) :rule refl)
        (anchor :step t2 :args ((x Int)))
        (step t2.t1 (cl (= x x)) :rule refl)
        (step t2.t2 (cl (= (f x) (f x))) :rule cong :premises (t2.t1))
        (step t2 (cl (= (forall ((x Int)) (f x)) (forall ((x Int)) (f x)))) :rule bind)
        (step end (cl) :rule hole)
    ";

    let hoisted = run_hoist_pass(definitions, proof, checker::Config::new());

    assert_eq!(count_rule(&hoisted.commands, "refl"), 2);
    assert_eq!(top_level_with_rule(&hoisted, "refl").len(), 1);
    assert_eq!(
        step_ids(&hoisted.commands),
        step_ids(&parse(definitions, proof).1.commands)
    );
}

/// A derivation that goes through a hole is never used in place of a real one, and a real one is
/// never replaced by it: the proof is exactly as holey after the pass as it was before.
#[test]
fn hole_rooted_duplicate_never_replaces_a_derivation() {
    // Both subproofs prove `(= (+ 1 1) 2)`: the first one really, the second one with a
    // `hole`. Whichever order the pass visits them in, neither may take the other's place
    let proof = "
        (assume a0 p)
        (anchor :step t1)
        (assume t1.h1 p)
        (step t1.t1 (cl (= (+ 1 1) 2)) :rule evaluate)
        (step t1.t2 (cl (= (+ 1 1) 2)) :rule contraction :premises (t1.t1))
        (step t1 (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t1.h1))
        (anchor :step t2)
        (assume t2.h1 p)
        (step t2.t1 (cl (= (+ 1 1) 2)) :rule hole)
        (step t2.t2 (cl (= (+ 1 1) 2)) :rule contraction :premises (t2.t1))
        (step t2 (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t2.h1))
        (step end (cl) :rule hole)
    ";

    let hoisted = run_hoist_pass(DEFS, proof, checker::Config::new());

    // The `hole` step is still there, and so is the real derivation: no step was replaced by the
    // other subproof's, in either direction
    assert_eq!(count_rule(&hoisted.commands, "hole"), 2);
    assert_eq!(count_rule(&hoisted.commands, "evaluate"), 1);
    assert_eq!(count_rule(&hoisted.commands, "contraction"), 2);
}

/// A rule that the checker was told to accept as a hole is treated like `hole` itself.
#[test]
fn allowed_rule_duplicate_never_replaces_a_derivation() {
    let proof = "
        (assume a0 p)
        (anchor :step t1)
        (assume t1.h1 p)
        (step t1.t1 (cl (= (+ 1 1) 2)) :rule evaluate)
        (step t1.t2 (cl (= (+ 1 1) 2)) :rule contraction :premises (t1.t1))
        (step t1 (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t1.h1))
        (anchor :step t2)
        (assume t2.h1 p)
        (step t2.t1 (cl (= (+ 1 1) 2)) :rule trust_me)
        (step t2.t2 (cl (= (+ 1 1) 2)) :rule contraction :premises (t2.t1))
        (step t2 (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t2.h1))
        (step end (cl) :rule hole)
    ";
    let config = checker::Config {
        allowed_rules: ["trust_me".to_owned()].into_iter().collect(),
        ..Default::default()
    };

    let hoisted = run_hoist_pass(DEFS, proof, config);

    assert_eq!(count_rule(&hoisted.commands, "trust_me"), 1);
    assert_eq!(count_rule(&hoisted.commands, "evaluate"), 1);
    assert_eq!(count_rule(&hoisted.commands, "contraction"), 2);
}

/// Running the pass a second time changes nothing.
#[test]
fn running_the_pass_twice_is_a_no_op() {
    let subproof = |i: usize| {
        format!(
            "(anchor :step t{i})
             (assume t{i}.h1 p)
             (step t{i}.t1 (cl (= (+ 1 1) 2)) :rule evaluate)
             (step t{i}.t2 (cl (= (< x y) (< x y))) :rule refl)
             (step t{i}.t3 (cl (= (+ 1 1) 2)) :rule contraction :premises (t{i}.t1))
             (step t{i} (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t{i}.h1))"
        )
    };
    let proof = format!(
        "(assume a0 p)\n{}\n{}\n{}\n(step end (cl) :rule hole)",
        subproof(1),
        subproof(2),
        subproof(3)
    );

    let (problem, parsed, _, mut pool) = parse(DEFS, &proof);
    let config = elaborator::Config::default();
    let forest = ast::ProofNodeForest::from_commands(parsed.commands.clone());
    let once = elaborator::Elaborator::new(&mut pool, &problem, config.clone())
        .elaborate(forest, vec![elaborator::ElaborationPass::Hoist])
        .unwrap();
    let once_commands = once.into_commands();

    let twice = elaborator::Elaborator::new(&mut pool, &problem, config)
        .elaborate(
            ast::ProofNodeForest::from_commands(once_commands.clone()),
            vec![elaborator::ElaborationPass::Hoist],
        )
        .unwrap();
    let twice_commands = twice.into_commands();

    // The first run did do something, and the second one did not
    assert!(step_ids(&once_commands).len() < step_ids(&parsed.commands).len());
    assert_eq!(step_ids(&once_commands), step_ids(&twice_commands));
    assert_eq!(
        format!("{:?}", once_commands),
        format!("{:?}", twice_commands)
    );
}

/// The step that closes a subproof, and the one it refers to by its position, stay in the subproof
/// even when an identical derivation is available at the top level.
#[test]
fn positional_steps_are_never_lifted() {
    let proof = "
        (assume a0 p)
        (step t0 (cl (= (+ 1 1) 2)) :rule evaluate)
        (anchor :step t1)
        (assume t1.h1 p)
        (step t1.t1 (cl (= (+ 1 1) 2)) :rule evaluate)
        (step t1 (cl (not p) (= (+ 1 1) 2)) :rule subproof :discharge (t1.h1))
        (step end (cl) :rule hole)
    ";

    let hoisted = run_hoist_pass(DEFS, proof, checker::Config::new());

    // `t1.t1` is the implicit premise of `t1`, so it cannot be replaced by `t0`
    assert_eq!(count_rule(&hoisted.commands, "evaluate"), 2);
    assert_eq!(
        step_ids(&hoisted.commands),
        step_ids(&parse(DEFS, proof).1.commands)
    );
}

/// A lemma scope whose discharged clause a premise-free rule proves outright is replaced by that
/// one step. This is the shape cvc5 emits for every congruence-closure lemma.
#[test]
fn transitivity_scope_collapses_to_eq_transitive() {
    let definitions = "
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
    ";
    let proof = "
        (anchor :step t1)
        (assume t1.a0 (= a b))
        (assume t1.a1 (= b c))
        (step t1.t0 (cl (= a c)) :rule trans :premises (t1.a0 t1.a1))
        (step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof
            :discharge (t1.a0 t1.a1))
        (step t2 (cl) :rule hole :premises (t1))
    ";
    let config = checker::Config::new().ignore_unknown_rules(true);

    // `hoist` leaves the scope alone
    let hoisted = run_hoist_pass(definitions, proof, config.clone());
    assert_eq!(count_rule(&hoisted.commands, "subproof"), 1);
    assert_eq!(count_rule(&hoisted.commands, "eq_transitive"), 0);

    // `deep-hoist` replaces the whole four-command scope with one clausal step
    let collapsed = run_deep_hoist_pass(definitions, proof, config);
    assert_eq!(count_rule(&collapsed.commands, "subproof"), 0);
    assert_eq!(count_rule(&collapsed.commands, "trans"), 0);
    assert_eq!(count_rule(&collapsed.commands, "eq_transitive"), 1);
    assert!(
        !collapsed
            .commands
            .iter()
            .any(|c| matches!(c, ast::ProofCommand::Subproof(_))),
        "a subproof survived the collapse"
    );
}

/// A congruence lemma collapses the same way, onto `eq_congruent`.
#[test]
fn congruence_scope_collapses_to_eq_congruent() {
    let definitions = "
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
    ";
    let proof = "
        (anchor :step t1)
        (assume t1.a0 (= a b))
        (step t1.t0 (cl (= (f a) (f b))) :rule cong :premises (t1.a0))
        (step t1 (cl (not (= a b)) (= (f a) (f b))) :rule subproof :discharge (t1.a0))
        (step t2 (cl) :rule hole :premises (t1))
    ";
    let collapsed = run_deep_hoist_pass(
        definitions,
        proof,
        checker::Config::new().ignore_unknown_rules(true),
    );
    assert_eq!(count_rule(&collapsed.commands, "subproof"), 0);
    assert_eq!(count_rule(&collapsed.commands, "eq_congruent"), 1);
}

/// A scope whose conclusion no premise-free rule proves is left exactly as it was.
#[test]
fn a_scope_with_no_clausal_counterpart_is_kept() {
    let definitions = "
        (declare-const p Bool)
        (declare-const q Bool)
    ";
    let proof = "
        (anchor :step t1)
        (assume t1.a0 p)
        (step t1.t0 (cl q) :rule hole :premises (t1.a0))
        (step t1 (cl (not p) q) :rule subproof :discharge (t1.a0))
        (step t2 (cl) :rule hole :premises (t1))
    ";
    let collapsed = run_deep_hoist_pass(
        definitions,
        proof,
        checker::Config::new().ignore_unknown_rules(true),
    );
    assert_eq!(count_rule(&collapsed.commands, "subproof"), 1);
}

/// A rule the checker was told to treat as a hole must never become the justification of a scope
/// that had a real derivation, for the same reason `hoist` will not share a holey derivation.
#[test]
fn an_allowed_rule_is_not_used_to_collapse_a_scope() {
    let definitions = "
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
    ";
    let proof = "
        (anchor :step t1)
        (assume t1.a0 (= a b))
        (assume t1.a1 (= b c))
        (step t1.t0 (cl (= a c)) :rule trans :premises (t1.a0 t1.a1))
        (step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof
            :discharge (t1.a0 t1.a1))
        (step t2 (cl) :rule hole :premises (t1))
    ";
    let config = checker::Config::new()
        .ignore_unknown_rules(true)
        .allowed_rules(["eq_transitive"]);
    let collapsed = run_deep_hoist_pass(definitions, proof, config);
    assert_eq!(count_rule(&collapsed.commands, "eq_transitive"), 0);
    assert_eq!(count_rule(&collapsed.commands, "subproof"), 1);
}

/// A scope whose body uses `cong` with the implicit-premise convention — identical argument pairs
/// skipped — has fewer equality literals than a whole-clause `eq_congruent` demands, so the
/// battery cannot touch it. The clausal replay translates the body instead: `eq_congruent` over
/// every argument pair, with `eq_reflexive` supplying the identical ones.
#[test]
fn implicit_premise_congruence_scope_is_replayed()  {
    let definitions = "
        (declare-fun f (Int Int Int Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
    ";
    let proof = "
        (anchor :step t2)
        (assume t2.a0 (= a b))
        (assume t2.a1 (= c d))
        (step t2.t0 (cl (= (f a a c b) (f b a d b))) :rule cong :premises (t2.a0 t2.a1))
        (step t2 (cl (not (= a b)) (not (= c d)) (= (f a a c b) (f b a d b))) :rule subproof
            :discharge (t2.a0 t2.a1))
        (step t3 (cl) :rule hole :premises (t2))
    ";
    let collapsed = run_deep_hoist_pass(
        definitions,
        proof,
        checker::Config::new().ignore_unknown_rules(true),
    );
    assert_eq!(count_rule(&collapsed.commands, "subproof"), 0);
    assert_eq!(count_rule(&collapsed.commands, "cong"), 0);
    assert_eq!(count_rule(&collapsed.commands, "eq_congruent"), 1);
    assert_eq!(count_rule(&collapsed.commands, "refl"), 2);
}

/// A body mixing `trans` and `symm` from the assumptions replays through `eq_transitive`.
#[test]
fn transitivity_and_symmetry_scope_is_replayed() {
    let definitions = "
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
    ";
    let proof = "
        (anchor :step t1)
        (assume t1.a0 (= b a))
        (assume t1.a1 (= b c))
        (step t1.t0 (cl (= a b)) :rule symm :premises (t1.a0))
        (step t1.t1 (cl (= a c)) :rule trans :premises (t1.t0 t1.a1))
        (step t1 (cl (not (= b a)) (not (= b c)) (= a c)) :rule subproof
            :discharge (t1.a0 t1.a1))
        (step t2 (cl) :rule hole :premises (t1))
    ";
    let collapsed = run_deep_hoist_pass(
        definitions,
        proof,
        checker::Config::new().ignore_unknown_rules(true),
    );
    assert_eq!(count_rule(&collapsed.commands, "subproof"), 0);
    assert!(count_rule(&collapsed.commands, "eq_transitive") >= 1);
}
