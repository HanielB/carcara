#!/usr/bin/env python3
"""Turn cvc5's named regex-eval holes into checkable Carcara rules.

Usage: transform-holes.py [--out DIR]

For every OUT/organic/**/proof.alethe, writes proof-eval.alethe next to it with
    :rule hole :args ("str-in-re-eval")   ->   :rule str_in_re_eval
(and likewise for the other five rewrites). The untransformed proof.alethe is
kept: checking it is the lower-bound configuration (holes are accepted for
free), mirroring the paper's LB.
"""

import argparse
import os
import re

from common import DATA_ROOT, EVAL_RULES

PATTERN = re.compile(
    r':rule hole :args \("(' + "|".join(EVAL_RULES) + r')"\)'
)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=DATA_ROOT)
    args = ap.parse_args()

    n = 0
    for dirpath, _, filenames in os.walk(os.path.join(args.out, "organic")):
        if "proof.alethe" not in filenames:
            continue
        with open(os.path.join(dirpath, "proof.alethe")) as f:
            text = f.read()
        transformed, count = PATTERN.subn(
            lambda m: ":rule " + EVAL_RULES[m.group(1)], text
        )
        assert count > 0, f"no eval holes found in {dirpath}"
        with open(os.path.join(dirpath, "proof-eval.alethe"), "w") as f:
            f.write(transformed)
        n += 1
    print(f"transformed {n} proofs")


if __name__ == "__main__":
    main()
