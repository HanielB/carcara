use carcara::*;
use std::{
    fs, io,
    path::{Path, PathBuf},
};

fn run_parallel_checker_test(
    problem_path: &Path,
    proof_path: &Path,
    num_threads: usize,
) -> CarcaraResult<()> {
    use checker::Config;
    use std::sync::Arc;

    let (prelude, proof, pool) = parser::parse_instance(
        io::BufReader::new(fs::File::open(problem_path)?),
        io::BufReader::new(fs::File::open(proof_path)?),
        parser::Config::new(),
    )?;

    let (scheduler, schedule_context_usage) = checker::Scheduler::new(num_threads, &proof);
    let mut checker = checker::ParallelProofChecker::new(
        Arc::new(pool),
        Config::new(),
        &prelude,
        &schedule_context_usage,
        128 * 1024 * 1024,
    );
    checker.check(&proof, &scheduler)?;
    Ok(())
}

fn run_test(problem_path: &Path, proof_path: &Path) -> CarcaraResult<()> {
    use checker::Config;

    let (_, proof, mut pool) = parser::parse_instance(
        io::BufReader::new(fs::File::open(problem_path)?),
        io::BufReader::new(fs::File::open(proof_path)?),
        parser::Config::new(),
    )?;

    // First, we check the proof normally
    checker::ProofChecker::new(&mut pool, Config::new()).check(&proof)?;

    // Then we elaborate it
    let node = ast::ProofNode::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::elaborate(
        &mut pool,
        &proof.premises,
        &node,
        None,
        elaborator::ResolutionGranularity::Reordering,
    );
    let elaborated = ast::Proof {
        premises: proof.premises.clone(),
        commands: elaborated_node.into_commands(),
    };

    // After that, we check the elaborated proof to make sure it is valid
    checker::ProofChecker::new(&mut pool, Config::new()).check(&elaborated)?;

    // Finally, we elaborate the already elaborated proof, to make sure the elaboration step is
    // idempotent
    let elaborated_twice = elaborator::elaborate(
        &mut pool,
        &proof.premises,
        &elaborated_node,
        None,
        elaborator::ResolutionGranularity::Reordering,
    );
    assert!(
        elaborated.commands == elaborated_twice.into_commands(),
        "elaboration was not idempotent!"
    );

    // We also test the parallel checker, with different values for the number of threads
    run_parallel_checker_test(problem_path, proof_path, 1)?;
    run_parallel_checker_test(problem_path, proof_path, 4)?;
    run_parallel_checker_test(problem_path, proof_path, 16)?;

    Ok(())
}

fn test_file(proof_path: &str) {
    let proof_path = PathBuf::from(format!("../{}", proof_path));
    let problem_path = {
        let mut path = proof_path.clone();
        while path.extension().unwrap() != "smt_in" && path.extension().unwrap() != "smt2" {
            path.set_extension("");
        }
        path
    };
    if let Err(e) = run_test(&problem_path, &proof_path) {
        // Error messages are sometimes pretty big, so printing them fully can be very bad for
        // performance
        let short_message = match e {
            Error::Io(_) => "IO error".to_owned(),
            Error::Parser(_, (line, column)) => format!("parser error at {}:{}", line, column),
            Error::Checker { rule, step, .. } => format!("checker error at '{}' ({})", step, rule),
            Error::DoesNotReachEmptyClause => format!("{}", e), // This one is already pretty short
        };
        panic!(
            "\"{}\" returned error: {}",
            &proof_path.to_str().unwrap(),
            short_message
        )
    }
}

#[test_generator::from_dir("benchmarks/small")]
#[allow(dead_code)]
fn small(proof_path: &str) {
    test_file(proof_path)
}

#[test_generator::from_dir("benchmarks/full", ignore)]
#[allow(dead_code)]
fn full(proof_path: &str) {
    test_file(proof_path)
}
