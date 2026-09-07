#!/usr/bin/env python3
"""Builds the test set of the cpcCarcaraEval experiment: a fixed-seed random
sample of N benchmarks from each of the 26 sets of the unified AUFBVLIRA
corpus of pfcmp (16 cmp_* sets + 10 linear arr_* sets), written as a single
benchmark_set_cpcc_sample file next to this script."""

import os
import random
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
PFCMP_SETS = os.path.expanduser("~/exp/pfcmp/sets")
HERE = os.path.dirname(os.path.abspath(__file__))

CMP = [
    "cmp_LIA", "cmp_LRA", "cmp_QF_IDL", "cmp_QF_LIA", "cmp_QF_LRA", "cmp_QF_RDL",
    "cmp_QF_UF", "cmp_QF_UFIDL", "cmp_QF_UFLIA", "cmp_QF_UFLRA", "cmp_UF",
    "cmp_UFIDL", "cmp_UFLIA", "cmp_UFLRA", "cmp_QF_BV", "cmp_QF_UFBV",
]
ARR = [
    "arr_ABV", "arr_ALIA", "arr_AUFBV", "arr_AUFLIA", "arr_AUFLIRA",
    "arr_QF_ABV", "arr_QF_ALIA", "arr_QF_AUFBV", "arr_QF_AUFLIA", "arr_QF_AX",
]

rng = random.Random(20260907)
sample = []
for name in CMP + ARR:
    with open(os.path.join(PFCMP_SETS, "benchmark_set_" + name)) as f:
        lines = [l.strip() for l in f if l.strip()]
    chosen = lines if len(lines) <= N else rng.sample(lines, N)
    sample.extend(sorted(chosen))
    print(f"{name}: {len(chosen)} of {len(lines)}")

out = os.path.join(HERE, "sets", "benchmark_set_cpcc_sample")
os.makedirs(os.path.dirname(out), exist_ok=True)
with open(out, "w") as f:
    f.write("\n".join(sample) + "\n")
print(f"{len(sample)} benchmarks -> {out}")
