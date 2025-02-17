use super::*;
use crate::checker::error::LiaGenericError;
use crate::external::*;
use std::collections::HashMap;
use std::process;
use std::{
    fs::File,
    io::Write,
    process::{Command, Stdio},
};

fn sat_refutation_external_check(
    cnf_path: String,
    prelude: &ProblemPrelude,
    checker_path: String,
    lemmas: &Vec<Rc<Term>>,
) -> RuleResult {
    let prelude_path = format!("prelude_{}.smt2", process::id());
    write!(File::create(prelude_path.clone()).unwrap(), "{}", prelude).unwrap();

    // transform each AND arg, if any, into a string and build a
    // string "(and ... )" so that each lemma has its own names
    let lemmas_as_str = if lemmas.len() == 1 {
        let lemma_or = if let Some((Operator::RareList, lemma_lits)) = lemmas[0].as_op() {
            Term::Op(Operator::Or, lemma_lits.to_vec())
        } else {
            unreachable!();
        };
        format!("{}", lemma_or)
    } else {
        let mut str_aux = String::new();
        use std::fmt::Write;
        write!(&mut str_aux, "(and").unwrap();
        lemmas.iter().for_each(|lemma| {
            let lemma_or = if let Some((Operator::RareList, lemma_lits)) = lemma.as_op() {
                Term::Op(Operator::Or, lemma_lits.to_vec())
            } else {
                unreachable!();
            };
            write!(&mut str_aux, " {}", lemma_or).unwrap();
        });
        write!(&mut str_aux, ")").unwrap();
        str_aux
    };

    let string = format!("(\n{}\n{}\n{}\n)", cnf_path, prelude_path, lemmas_as_str);
    // this will make it expect this script from where you are running Carcara
    let mut process = Command::new(checker_path.clone())
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
    return Err(CheckerError::Explanation(format!(
        "External checker {} did not validate step",
        checker_path
    )));
}

pub fn sat_refutation(
    RuleArgs { pool, .. }: RuleArgs,
    premise_steps: Vec<&ProofCommand>,
    prelude: &ProblemPrelude,
    checker_path: Option<String>,
) -> RuleResult {
    // Create the DIMACS file from the premises and the lemmas.
    //
    // Lemmas (i.e., conclusions of "hole") are non-unit clauses if
    // they are OR terms, and unit otherwise. Literals are going to be
    // generated by doing the "remove_all_negations()" method of
    // terms.
    //
    // For the remaining premises, we can have some of them which
    // occur as arguments in others, which as a safer thing we also
    // add them as unit clauses with a literal corresponding to the
    // whole clause.

    let mut lemmas: Vec<Rc<Term>> = Vec::new();
    let mut clause_id_to_lemma: HashMap<usize, Rc<Term>> = HashMap::new();
    let premise_clauses =
        collect_premise_clauses(pool, &premise_steps, &mut lemmas, &mut clause_id_to_lemma);

    let mut sat_clause_to_lemma: HashMap<Vec<i32>, Rc<Term>> = HashMap::new();
    match checker_path {
        Some(checker_path) => {
            let cnf_path = gen_dimacs(
                &premise_clauses,
                &clause_id_to_lemma,
                &mut sat_clause_to_lemma,
                true,
            );
            sat_refutation_external_check(cnf_path, prelude, checker_path, &lemmas)
        }
        None => {
            let cnf_path = gen_dimacs(
                &premise_clauses,
                &clause_id_to_lemma,
                &mut sat_clause_to_lemma,
                false,
            );

            match get_core_lemmas(cnf_path, &sat_clause_to_lemma) {
                Ok(core_lemmas) => {
                    let borrowed_term_pool = pool;
                    let primitive_pool: &mut PrimitivePool = match borrowed_term_pool
                        .as_any_mut()
                        .downcast_mut::<PrimitivePool>()
                    {
                        Some(b) => b,
                        None => panic!("&a isn't a B!"),
                    };
                    // for each core lemma, we will run cvc5, parse the proof in, and check it
                    for i in 0..core_lemmas.len() {
                        // println!("\tCheck lemma {:?}", lemma);
                        let problem = get_problem_string(primitive_pool, &prelude, &core_lemmas[i][..]);

                        if let Err(_) = get_solver_proof(primitive_pool, problem.clone()) {
                            println!("\t\tFailed: {:?}", core_lemmas[i]);
                            return Err(CheckerError::LiaGeneric(LiaGenericError::OutputNotUnsat));
                        }
                    }
                    return Ok(());
                },
                Err(e) => return Err(CheckerError::External(e))
            }
        }
    }
}

pub fn external_checker(RuleArgs { args, .. }: RuleArgs, checker_path: String) -> RuleResult {
    let args_str: Vec<String> = args.iter().map(|t| format!("{}", t)).collect();
    let string = format!("(\n{}\n)", args_str.join("\n"));
    // this will make it expect this script from where you are running Carcara
    let mut process = Command::new(checker_path.clone())
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
    return Err(CheckerError::Explanation(format!(
        "External checker {} did not validate step",
        checker_path
    )));
}
