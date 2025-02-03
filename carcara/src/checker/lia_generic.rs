use super::*;
use crate::checker::error::LiaGenericError;
use std::process;
use std::{
    fs::File,
    io::Write,
    process::{Command, Stdio},
};

pub fn sat_refutation(
    RuleArgs { pool, args, .. }: RuleArgs,
    prelude: &ProblemPrelude,
    checker_path: String,
) -> RuleResult {
    let Sort::String = pool.sort(&args[0]).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let Sort::Bool = pool.sort(&args[1]).as_sort().cloned().unwrap() else {
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
            write!(&mut term_str2, " {}", and_args[j]).unwrap();
            j += 1;
        }
        write!(&mut term_str2, ")").unwrap();
        term_str2
    } else {
        format!("{}", args[2])
    };

    let file_name = format!("prelude_{}.smt2", process::id());
    let mut f = File::create(file_name.clone()).unwrap();
    write!(f, "{}", prelude).unwrap();

    let string = format!("(\n{}\n{}\n{}\n)", args[0], file_name, term_str);

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
