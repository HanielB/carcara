use carcara::*;
use std::io::Cursor;

fn run_elaboration_test(problem: &str, proof: &str) {
    let (problem, proof, mut pool) = parser::parse_instance(
        Cursor::new(problem),
        Cursor::new(proof),
        parser::Config::new(),
    )
    .expect("parsing failed");

    let checker_config = checker::Config {
        elaborated: false,
        ignore_unknown_rules: true,
        allowed_rules: Default::default(),
    };

    // First, the original proof checks
    checker::ProofChecker::new(&mut pool, checker_config.clone())
        .check(&problem, &proof)
        .expect("original proof failed to check");

    // Then we elaborate it
    let elab_config = elaborator::Config {
        lia_options: None,
        hole_options: None,
        uncrowd_rotation: false,
    };
    let node = ast::ProofNode::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
        .elaborate(&node, vec![elaborator::ElaborationStep::SkoRename]);
    let elaborated = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: elaborated_node.into_commands(),
    };

    // The elaborated proof must check too
    checker::ProofChecker::new(&mut pool, checker_config)
        .check(&problem, &elaborated)
        .expect("elaborated proof failed to check");

    // Make sure the elaboration actually got rid of all `sko_*_rename` rules
    fn assert_no_rename(commands: &[ast::ProofCommand]) {
        for c in commands {
            match c {
                ast::ProofCommand::Step(s) => {
                    assert!(
                        s.rule != "sko_ex_rename" && s.rule != "sko_forall_rename",
                        "elaborated proof still contains '{}'",
                        s.rule
                    );
                }
                ast::ProofCommand::Subproof(sp) => assert_no_rename(&sp.commands),
                ast::ProofCommand::Assume { .. } => {}
            }
        }
    }
    assert_no_rename(&elaborated.commands);
}

#[test]
fn sko_ex_rename_elaboration() {
    let problem = "
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (declare-fun q (Int) Bool)
        (assert (and (forall (($v0 Int)) (or (not (p $v0)) (q $v0)))
                     (exists (($v0 Int)) (and (p $v0) (not (q $v0))))))
        (check-sat)
    ";

    let proof = "
        (assume input_0 (and (forall (($v0 Int)) (or (not (p $v0)) (q $v0)))
                             (exists (($v0 Int)) (and (p $v0) (not (q $v0))))))
        (define-fun all_2_0 () Int (choice ((all_2_0 Int)) (and (p all_2_0) (not (q all_2_0)))))
        (anchor :step t3 :args ((:= (all_2_0_choice Int) all_2_0)))
        (step t4 (cl (= (and (p all_2_0_choice) (not (q all_2_0_choice)))
                        (and (p all_2_0) (not (q all_2_0))))) :rule refl)
        (step t3 (cl (= (exists (($v0 Int)) (and (p $v0) (not (q $v0))))
                        (and (p all_2_0) (not (q all_2_0))))) :rule sko_ex_rename)
        (step t5 (cl) :rule hole :premises (t3))
    ";

    run_elaboration_test(problem, proof);
}

#[test]
fn sko_forall_rename_elaboration() {
    let problem = "
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (assert (forall (($v0 Int)) (p $v0)))
        (check-sat)
    ";

    let proof = "
        (assume input_0 (forall (($v0 Int)) (p $v0)))
        (define-fun c () Int (choice ((c Int)) (not (p c))))
        (anchor :step t2 :args ((:= (renamed Int) c)))
        (step t2.1 (cl (= (p renamed) (p c))) :rule refl)
        (step t2 (cl (= (forall (($v0 Int)) (p $v0)) (p c))) :rule sko_forall_rename)
        (step t3 (cl) :rule hole :premises (t2))
    ";

    run_elaboration_test(problem, proof);
}
