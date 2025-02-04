use super::*;
use crate::checker::error::LiaGenericError;
use std::process;
use std::{
    fs::File,
    io::Write,
    process::{Command, Stdio},
};

pub fn sat_refutation(
    RuleArgs { pool, .. }: RuleArgs,
    premise_steps : Vec<&ProofCommand>,
    prelude: &ProblemPrelude
) -> RuleResult {
    // This should be done now for each premise that is a hole, given
    // that they show up in the trimmed input

    // let smt2_prelude = format!("prelude_{}.smt2", process::id());
    // let mut f = File::create(smt2_prelude.clone()).unwrap();
    // write!(f, "{}", prelude).unwrap();

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
    let mut premise_clauses : Vec<Vec<_>> = Vec::new();
    premise_steps
        .iter()
        .for_each(|p|
                  { match p
                    {
                        ProofCommand::Step(step) => {
                            // holes are assumed to be theory lemmas, where if they
                            // are OR nodes then they are non-unit, otherwise
                            // unities. If they are not singleton clauses, we add the
                            // whole clause as a clause
                            if step.rule == "hole" {
                                match &step.clause[..] {
                                    [term] => {
                                        match term.as_ref() {
                                            Term::Op(Operator::Or, or_args) => {
                                                premise_clauses.push(or_args.to_vec());
                                            }
                                            _ => {premise_clauses.push(vec![term.clone()]);}
                                        }
                                    }
                                    _ => {
                                        premise_clauses.push(step.clause.clone());
                                    }
                                }
                            }
                            else {
                                match &step.clause[..] {
                                    // singletons are always added as unities and as clauses, if OR nodes
                                    [term] => {
                                        match term.as_ref() {
                                            Term::Op(Operator::Or, or_args) => {
                                                premise_clauses.push(or_args.to_vec());
                                            }
                                            _ => {}
                                        }
                                        premise_clauses.push(vec![term.clone()]);
                                    }
                                    _ => {
                                        premise_clauses.push(step.clause.clone());
                                    }
                                }
                            }
                        }
                        ProofCommand::Subproof(_) => {}
                        ProofCommand::Assume { term, .. } => {
                            // if OR, collect as clause, but also always generate as
                            // literal
                            match term.as_ref() {
                                Term::Op(Operator::Or, or_args) => {
                                    premise_clauses.push(or_args.to_vec());
                                }
                                _ => {}
                            }
                            premise_clauses.push(vec![term.clone()]);
                        }
                    }
                  }
        );

    let mut max_var = 0;
    let mut lemma_id = 0;

    // TODO collect unit clauses from premises
    // TODO create the DIMACS string
    // TODO create the first line of the DIMACS and print to file

    // TODO add sanity check calling CaDiCaL? Nah


    // let string = format!("(\n{}\n{}\n{}\n)", smt2_prelude, term_str);

    // // this will make it expect this script from where you are running Carcara
    // let mut process = Command::new(checker_path.clone())
    //     .stdin(Stdio::piped())
    //     .stdout(Stdio::piped())
    //     .stderr(Stdio::piped())
    //     .spawn()
    //     .map_err(LiaGenericError::FailedSpawnSolver)?;

    // process
    //     .stdin
    //     .take()
    //     .expect("failed to open solver stdin")
    //     .write_all(string.as_bytes())
    //     .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    // let output = process
    //     .wait_with_output()
    //     .map_err(LiaGenericError::FailedWaitForSolver)?;

    // if !output.status.success() {
    //     if let Ok(s) = std::str::from_utf8(&output.stderr) {
    //         if s.contains("interrupted by timeout.") {
    //             return Err(CheckerError::Unspecified);
    //         }
    //     }
    //     return Err(CheckerError::Unspecified);
    // }
    // let res = output.stdout.as_slice();

    // if res == b"true\n" {
    //     return Ok(());
    // }
    // return Err(CheckerError::Explanation(format!(
    //     "External checker {} did not validate step",
    //     checker_path
    // )));

    return Ok(());
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
