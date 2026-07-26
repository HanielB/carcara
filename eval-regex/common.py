"""Shared helpers for the regex-eval pipeline (runlim invocation and log layout).

The log layout mirrors the IJCAR artifact (artifact/evaluation/run-evaluation.py):
each task gets a directory with `output.log` (stdout) and `run.out` (runlim
stats), so artifact/tools/cmpr-ethos.py can aggregate our results unchanged.
"""

import os
import re
import subprocess

RUNLIM = "runlim"

# cvc5 ProofRewriteRule names -> Carcara rule names (carcara/src/checker/mod.rs)
EVAL_RULES = {
    "str-in-re-eval": "str_in_re_eval",
    "str-replace-re-eval": "str_replace_re_eval",
    "str-replace-re-all-eval": "str_replace_re_all_eval",
    "str-indexof-re-eval": "str_indexof_re_eval",
    "re-loop-elim": "re_loop_elim",
    "re-eq-elim": "re_eq_elim",
}

BENCHMARKS_ROOT = os.path.expanduser("~/benchmarks/smtlib/non-incremental")
DATA_ROOT = os.path.expanduser("~/benchmarks/regex-eval")


def save_run_out(log_dir, stderr_text):
    """Parse runlim's stderr report into the artifact's run.out format."""
    def search(pattern, default):
        m = re.search(pattern, stderr_text)
        return m.group(1) if m else default

    cputime = search(r"\[runlim\] time:\s*(\d*\.?\d*)\s*seconds", 0)
    # runlim 1.10 reports no separate wall time; newer versions print "real:"
    walltime = search(r"\[runlim\] real:\s*(\d*\.?\d*)\s*seconds", cputime)
    returnvalue = search(r"\[runlim\] result:\s*(\d+)", 0)
    space_mb = search(r"\[runlim\] space:\s*(\d*\.?\d*)", 0)
    memory = int(float(space_mb) * 1024 * 1024)

    status = search(r"\[runlim\]\s*status:\s*([\w ]*)", "").strip()
    terminationreason = ""
    if status == "out of time":
        terminationreason = "terminationreason=time"
    elif status == "out of memory":
        terminationreason = "terminationreason=memory"

    with open(os.path.join(log_dir, "run.out"), "w") as f:
        f.write(
            f"returnvalue={returnvalue}\n"
            f"walltime={walltime}\n"
            f"cputime={cputime}\n"
            f"memory={memory}\n"
            f"{terminationreason}\n"
        )


def run_task(cmd, log_dir, time_limit=60, space_limit=8000):
    """Run `cmd` under runlim, writing output.log and run.out into log_dir."""
    os.makedirs(log_dir, exist_ok=True)
    full_cmd = [
        RUNLIM,
        f"--time-limit={time_limit}",
        f"--space-limit={space_limit}",
    ] + cmd
    proc = subprocess.run(full_cmd, capture_output=True)
    with open(os.path.join(log_dir, "output.log"), "wb") as f:
        f.write(proc.stdout)
    with open(os.path.join(log_dir, "output.err"), "wb") as f:
        f.write(proc.stderr)
    save_run_out(log_dir, proc.stderr.decode(errors="replace"))
