use super::*;
use crate::{checker::error::LiaGenericError, parser, LiaGenericOptions};
use indexmap::IndexMap;
use std::{
    io::{BufRead, Write},
    process::{Command, Stdio},
};

fn get_problem_string(conclusion: &[Rc<Term>], prelude: &ProblemPrelude) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    write!(&mut problem, "(set-option :produce-proofs true)").unwrap();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_lia_smt_instance(&mut bytes, conclusion, true).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();

    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

pub fn lia_generic_single_thread(
    pool: &mut PrimitivePool,
    conclusion: &[Rc<Term>],
    prelude: &ProblemPrelude,
    elaborator: Option<&mut Elaborator>,
    root_id: &str,
    options: &LiaGenericOptions,
) -> bool {
    let problem = get_problem_string(conclusion, prelude);
    let commands = match get_solver_proof(pool, problem, options) {
        Ok(c) => c,
        Err(e) => {
            log::warn!("failed to check `lia_generic` step: {}", e);
            if let Some(elaborator) = elaborator {
                elaborator.unchanged(conclusion);
            }
            return true;
        }
    };

    if let Some(elaborator) = elaborator {
        insert_solver_proof(pool, elaborator, commands, conclusion, root_id);
    }
    false
}

pub fn lia_generic_multi_thread(
    conclusion: &[Rc<Term>],
    prelude: &ProblemPrelude,
    options: &LiaGenericOptions,
) -> bool {
    let mut pool = PrimitivePool::new();
    let problem = get_problem_string(conclusion, prelude);
    if let Err(e) = get_solver_proof(&mut pool, problem, options) {
        log::warn!("failed to check `lia_generic` step using: {}", e);
        true
    } else {
        false
    }
}

fn get_solver_proof(
    pool: &mut PrimitivePool,
    problem: String,
    options: &LiaGenericOptions,
) -> Result<Vec<ProofCommand>, LiaGenericError> {
    let mut process = Command::new(options.solver.as_ref())
        .args(options.arguments.iter().map(AsRef::as_ref))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(problem.as_bytes())
        .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(LiaGenericError::SolverTimeout);
            }
        }
        return Err(LiaGenericError::NonZeroExitCode(output.status.code()));
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| LiaGenericError::SolverGaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(LiaGenericError::OutputNotUnsat);
    }

    parse_and_check_solver_proof(pool, problem.as_bytes(), proof)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))
}

fn parse_and_check_solver_proof(
    pool: &mut PrimitivePool,
    problem: &[u8],
    proof: &[u8],
) -> CarcaraResult<Vec<ProofCommand>> {
    let mut parser = parser::Parser::new(pool, parser::Config::new(), problem)?;
    let (prelude, premises) = parser.parse_problem()?;
    parser.reset(proof)?;
    let commands = parser.parse_proof()?;
    let proof = Proof { premises, commands };

    ProofChecker::new(pool, Config::new(), &prelude).check(&proof)?;
    Ok(proof.commands)
}

fn update_premises(commands: &mut [ProofCommand], delta: usize, root_id: &str) {
    for c in commands {
        match c {
            ProofCommand::Assume { id, .. } => {
                *id = format!("{}.{}", root_id, id);
            }
            ProofCommand::Step(s) => {
                s.id = format!("{}.{}", root_id, s.id);
                for p in s.premises.iter_mut().chain(s.discharge.iter_mut()) {
                    if p.0 == 0 {
                        p.1 += delta;
                    }
                    p.0 += 1;
                }
            }
            ProofCommand::Subproof(s) => {
                update_premises(&mut s.commands, delta, root_id);
            }
        }
    }
}

fn insert_missing_assumes(
    pool: &mut PrimitivePool,
    elaborator: &mut Elaborator,
    conclusion: &[Rc<Term>],
    proof: &[ProofCommand],
    root_id: &str,
) -> (Vec<Rc<Term>>, usize) {
    let mut count_map: IndexMap<&Rc<Term>, usize> = IndexMap::new();
    for c in conclusion {
        *count_map.entry(c).or_default() += 1;
    }

    let proof_premises: Vec<_> = proof
        .iter()
        .filter_map(|c| {
            if let ProofCommand::Assume { term, .. } = c {
                Some(term.remove_negation().unwrap().clone())
            } else {
                None
            }
        })
        .collect();
    for p in &proof_premises {
        *count_map.get_mut(p).unwrap() -= 1;
    }

    let mut all = Vec::new();
    for (t, mut count) in count_map {
        while count > 0 {
            let id = elaborator.get_new_id(root_id);
            all.push(t.clone());
            let term = build_term!(pool, (not {t.clone()}));
            elaborator.add_new_command(ProofCommand::Assume { id, term }, true);
            count -= 1;
        }
    }
    let num_added = all.len();
    all.extend(proof_premises);
    (all, num_added)
}

fn insert_solver_proof(
    pool: &mut PrimitivePool,
    elaborator: &mut Elaborator,
    mut commands: Vec<ProofCommand>,
    conclusion: &[Rc<Term>],
    root_id: &str,
) {
    let subproof_id = elaborator.get_new_id(root_id);
    elaborator.open_accumulator_subproof();

    let (all_premises, num_added) = insert_missing_assumes(
        pool,
        elaborator,
        conclusion,
        &commands,
        // This is a bit ugly, but we have to add the ".added" to avoid colliding with the first few
        // steps in the solver proof
        &format!("{}.added", root_id),
    );

    let (mut clause, discharge): (Vec<_>, Vec<_>) = all_premises
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let term = build_term!(pool, (not (not {t.clone()})));
            (term, (1usize, i))
        })
        .unzip();
    clause.push(pool.bool_false());

    update_premises(&mut commands, num_added, &subproof_id);
    for c in commands {
        elaborator.add_new_command(c, true);
    }

    let subproof = elaborator.close_accumulator_subproof(
        Vec::new(),
        Vec::new(),
        ProofStep {
            id: subproof_id,
            clause: clause.clone(),
            rule: "subproof".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge,
        },
        root_id,
    );

    let not_not_steps: Vec<_> = clause[..clause.len() - 1]
        .iter()
        .map(|term| {
            let clause = vec![
                build_term!(pool, (not {term.clone()})),
                term.remove_negation()
                    .unwrap()
                    .remove_negation()
                    .unwrap()
                    .clone(),
            ];
            let id = elaborator.get_new_id(root_id);
            elaborator.add_new_step(ProofStep {
                id,
                clause,
                rule: "not_not".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
                discharge: Vec::new(),
            })
        })
        .collect();
    let id = elaborator.get_new_id(root_id);
    let false_step = elaborator.add_new_step(ProofStep {
        id,
        clause: vec![build_term!(pool, (not {pool.bool_false()}))],
        rule: "false".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
    });

    let mut premises = vec![subproof];
    premises.extend(not_not_steps);
    premises.push(false_step);

    let id = elaborator.get_new_id(root_id);
    elaborator.push_elaborated_step(ProofStep {
        id,
        clause: conclusion.to_vec(),
        rule: "resolution".to_owned(),
        premises,
        args: Vec::new(),
        discharge: Vec::new(),
    });
}

pub fn sat_external_prove_lemmas(RuleArgs { pool, args, .. }: RuleArgs) -> RuleResult {
    let Sort::String = pool.sort(&args[0]).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let Sort::String = pool.sort(&args[1]).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let Sort::Bool = pool.sort(&args[2]).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    // transform each AND arg, if any, into a string and build a
    // string "(and ... )" so that each lemma has its own names
    let term_str = if let Some(and_args) = match_term!((and ...) = args[2]) {
        let mut j = 0;
        let mut term_str2 = String::new();
        use std::fmt::Write;
        write!(&mut term_str2, "(and").unwrap();
        while j < and_args.len() {
            if j < and_args.len() - 1 {
                write!(&mut term_str2, " {}", and_args[j]).unwrap();
            }
            else {
                write!(&mut term_str2, "{}", and_args[j]).unwrap();
            }
            j += 1;
        }
        write!(&mut term_str2, ")").unwrap();
        term_str2
    } else {
        format!("{}", args[2])
    };

    let string = format!("(\n{}\n{}\n{}\n)",
                         args[0], args[1], term_str);

    // this will make it expect this script from where you are running Carcara
    let mut process = Command::new("./sat-lemmas-prove.sh")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(string.as_bytes())
        .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(CheckerError::Unspecified);
            }
        }
        return Err(CheckerError::Unspecified);
    }
    let res = output.stdout.as_slice();

    if res == b"true\n" {
        return Ok(());
    }
    return Err(CheckerError::Unspecified);
}
