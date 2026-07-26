#!/usr/bin/env python3
"""Translate the artifact's synthetic traces into Alethe proofs.

Usage: translate-traces.py TRACES_DIR [--out DIR]

TRACES_DIR is an extracted artifact/evaluation/logs/cvc5/traces.tar.gz: files
<rel>/proof.eo made of lines
    (step @p :rule str-in-re-eval :args ((= (str.in_re "s" R) bool)))
The term syntax is plain SMT-LIB, so each line becomes one Alethe step whose
clause is the equality. We write, under OUT/synthetic/<rel>/:
    proof.alethe        steps with :rule hole            (lower bound)
    proof-eval.alethe   steps with :rule str_in_re_eval  (measured config)
    problem.smt2        trivial QF_S problem (proofs have no assumptions)
and OUT/synthetic_list with one <rel> per line.
"""

import argparse
import os
import re

from common import DATA_ROOT

LINE = re.compile(r"\(step @p\d* :rule str-in-re-eval :args \((\(.*\))\s*\)\)\s*$")

PROBLEM = "(set-logic QF_S)\n(check-sat)\n"


def translate(trace_path):
    holes, evals = [], []
    with open(trace_path, errors="replace") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            m = LINE.match(line)
            assert m, f"unrecognized trace line in {trace_path}: {line[:120]}"
            term = m.group(1)
            i = len(holes) + 1
            holes.append(f"(step t{i} (cl {term}) :rule hole)\n")
            evals.append(f"(step t{i} (cl {term}) :rule str_in_re_eval)\n")
    # Carcara requires proofs to conclude the empty clause; close with a hole
    # step (identical in both configs, so it does not affect the comparison).
    end = f"(step t{len(holes) + 1} (cl) :rule hole)\n"
    holes.append(end)
    evals.append(end)
    return holes, evals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("traces_dir")
    ap.add_argument("--out", default=DATA_ROOT)
    args = ap.parse_args()

    out_root = os.path.join(args.out, "synthetic")
    rels = []
    for dirpath, _, filenames in os.walk(args.traces_dir):
        for name in filenames:
            if name != "proof.eo":
                continue
            holes, evals = translate(os.path.join(dirpath, name))
            rel = os.path.relpath(dirpath, args.traces_dir)
            dest = os.path.join(out_root, rel)
            os.makedirs(dest, exist_ok=True)
            with open(os.path.join(dest, "proof.alethe"), "w") as f:
                f.writelines(holes)
            with open(os.path.join(dest, "proof-eval.alethe"), "w") as f:
                f.writelines(evals)
            with open(os.path.join(dest, "problem.smt2"), "w") as f:
                f.write(PROBLEM)
            rels.append(rel)

    rels.sort()
    with open(os.path.join(args.out, "synthetic_list"), "w") as f:
        f.writelines(rel + "\n" for rel in rels)
    print(f"translated {len(rels)} traces (list in {args.out}/synthetic_list)")


if __name__ == "__main__":
    main()
