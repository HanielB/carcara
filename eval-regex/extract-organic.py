#!/usr/bin/env python3
"""Extract the Organic proof set from cvc5 proof-generation logs.

Usage: extract-organic.py [--out DIR]

Walks OUT/cvc5/ looking for output.log files whose first line is "unsat". The
proof is the text after the "unsat" line, minus cvc5's outer "(" and ")" wrapper
lines (same convention as artifact/tools/extract_proofs.py). Proofs that apply
at least one of the six regex-eval rewrites (as dsl-rewrite holes) form the
Organic set:

  OUT/organic/<relative-path>/problem.smt2   (symlink to the SMT-LIB benchmark)
  OUT/organic/<relative-path>/proof.alethe   (untransformed: eval steps are holes)

and OUT/organic_list gets one <relative-path> per line.
"""

import argparse
import os

from common import BENCHMARKS_ROOT, DATA_ROOT, EVAL_RULES


def extract_proof(output_log):
    with open(output_log, errors="replace") as f:
        lines = f.read().splitlines()
    if not lines or lines[0] != "unsat":
        return None
    proof = lines[1:]
    # cvc5 wraps the Alethe proof in a single "(" ... ")" pair on its own lines
    if proof and proof[0] == "(" and proof[-1] == ")":
        proof = proof[1:-1]
    return "\n".join(proof) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=DATA_ROOT)
    args = ap.parse_args()

    cvc5_root = os.path.join(args.out, "cvc5")
    organic_root = os.path.join(args.out, "organic")
    kept = []

    for dirpath, _, filenames in os.walk(cvc5_root):
        if "output.log" not in filenames:
            continue
        proof = extract_proof(os.path.join(dirpath, "output.log"))
        if proof is None:
            continue
        if not any(f'"{name}"' in proof for name in EVAL_RULES):
            continue
        rel = os.path.relpath(dirpath, cvc5_root)
        dest = os.path.join(organic_root, rel)
        os.makedirs(dest, exist_ok=True)
        with open(os.path.join(dest, "proof.alethe"), "w") as f:
            f.write(proof)
        link = os.path.join(dest, "problem.smt2")
        if not os.path.lexists(link):
            os.symlink(os.path.join(BENCHMARKS_ROOT, rel), link)
        kept.append(rel)

    kept.sort()
    with open(os.path.join(args.out, "organic_list"), "w") as f:
        f.writelines(rel + "\n" for rel in kept)
    print(f"organic set: {len(kept)} proofs (list in {args.out}/organic_list)")


if __name__ == "__main__":
    main()
