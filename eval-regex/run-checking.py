#!/usr/bin/env python3
"""Check proofs with Carcara under runlim, artifact-style.

Usage: run-checking.py {organic,synthetic} --configs CarcaraEval CarcaraLB
                       [-j N] [--time-limit S] [--out DIR] [--limit N]

Reads OUT/<set>_list and, for each entry and each config, runs
    runlim --time-limit=60 --space-limit=8000 carcara check <proof> <problem>
writing output.log + run.out under OUT/check-<set>/<config>/<rel>/ (the layout
artifact/tools/cmpr-ethos.py understands). Resumable like generate-proofs.py.

CarcaraEval checks proof-eval.alethe (regex-eval steps checked by the new
automaton rules); CarcaraLB checks proof.alethe (same steps as anonymous holes,
accepted for free) — the paper's LB analog.
"""

import argparse
import os
import sys
from multiprocessing import Pool

from common import DATA_ROOT, run_task

CARCARA = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "..", "target", "release", "carcara"
)

CONFIGS = {
    "CarcaraEval": "proof-eval.alethe",
    "CarcaraLB": "proof.alethe",
}

# Rules cvc5's Alethe printer emits at dsl-rewrite granularity that this branch
# does not implement; allowed as holes in BOTH configs so that the Eval-vs-LB
# difference is exactly the six regex-eval rules.
ALLOWED_RULES = ["rare_rewrite", "evaluate"]


def process(task):
    config, rel, proof_dir, log_dir, time_limit = task
    if os.path.exists(os.path.join(log_dir, "run.out")):
        return False
    proof = os.path.join(proof_dir, CONFIGS[config])
    problem = os.path.join(proof_dir, "problem.smt2")
    cmd = [CARCARA, "check", "--allowed-rules"] + ALLOWED_RULES + ["--", proof, problem]
    run_task(cmd, log_dir, time_limit=time_limit)
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("benchmark_set", choices=["organic", "synthetic"])
    ap.add_argument("--configs", nargs="+", choices=CONFIGS, required=True)
    ap.add_argument("-j", "--jobs", type=int, default=7)
    ap.add_argument("--time-limit", type=int, default=60)
    ap.add_argument("--out", default=DATA_ROOT)
    ap.add_argument("--limit", type=int, help="only the first N benchmarks")
    args = ap.parse_args()

    with open(os.path.join(args.out, f"{args.benchmark_set}_list")) as f:
        rels = [line.strip() for line in f if line.strip()]
    if args.limit:
        rels = rels[: args.limit]

    tasks = []
    for config in args.configs:
        for rel in rels:
            proof_dir = os.path.join(args.out, args.benchmark_set, rel)
            log_dir = os.path.join(args.out, f"check-{args.benchmark_set}", config, rel)
            tasks.append((config, rel, proof_dir, log_dir, args.time_limit))

    done = 0
    with Pool(args.jobs) as pool:
        for _ in pool.imap_unordered(process, tasks, chunksize=1):
            done += 1
            sys.stdout.write(f"\r{done}/{len(tasks)}")
            sys.stdout.flush()
    print()


if __name__ == "__main__":
    main()
