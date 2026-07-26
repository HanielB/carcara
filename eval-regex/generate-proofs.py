#!/usr/bin/env python3
"""Generate Alethe proofs with cvc5 for a list of SMT-LIB benchmarks.

Usage: generate-proofs.py BENCHMARK_LIST [-j N] [--time-limit S] [--out DIR]

BENCHMARK_LIST contains benchmark paths relative to ~/benchmarks/smtlib/non-incremental,
e.g. "QF_S/20230329-automatark-lu/instance08481.smt2", one per line.

For each benchmark, runs (under runlim, default 60s/8GB):
    cvc5 --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite
and stores output.log + run.out under OUT/cvc5/<relative-path>/.
Tasks whose run.out already exists are skipped, so the sweep is resumable.
"""

import argparse
import os
import sys
from multiprocessing import Pool

from common import BENCHMARKS_ROOT, DATA_ROOT, run_task

CVC5_CMD = [
    "cvc5",
    "--dump-proofs",
    "--proof-format-mode=alethe",
    "--proof-granularity=dsl-rewrite",
]


def process(task):
    rel, out_root, time_limit = task
    log_dir = os.path.join(out_root, "cvc5", rel)
    if os.path.exists(os.path.join(log_dir, "run.out")):
        return False
    benchmark = os.path.join(BENCHMARKS_ROOT, rel)
    run_task(CVC5_CMD + [benchmark], log_dir, time_limit=time_limit)
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("benchmark_list")
    ap.add_argument("-j", "--jobs", type=int, default=7)
    ap.add_argument("--time-limit", type=int, default=60)
    ap.add_argument("--out", default=DATA_ROOT)
    args = ap.parse_args()

    with open(args.benchmark_list) as f:
        rels = [line.strip() for line in f if line.strip()]
    tasks = [(rel, args.out, args.time_limit) for rel in rels]

    done = 0
    with Pool(args.jobs) as pool:
        for _ in pool.imap_unordered(process, tasks, chunksize=1):
            done += 1
            sys.stdout.write(f"\r{done}/{len(tasks)}")
            sys.stdout.flush()
    print()


if __name__ == "__main__":
    main()
