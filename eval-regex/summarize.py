#!/usr/bin/env python3
"""Summarize checking runs into a Table-3-style overview.

Usage: summarize.py {organic,synthetic} [--out DIR] [--common]

For each config under OUT/check-<set>/: #S (solved = returnvalue 0), the
valid/holey split (Carcara's stdout verdict), total CPU time, and peak-memory
sum. With --common, time/memory totals are restricted to the instances solved
by every config (the paper's "commonly checked" convention).
"""

import argparse
import os
from collections import defaultdict


def read_run(log_dir):
    stats = {}
    try:
        with open(os.path.join(log_dir, "run.out")) as f:
            for line in f:
                if "=" in line:
                    k, v = line.strip().split("=", 1)
                    stats[k] = v
    except FileNotFoundError:
        return None
    verdict = ""
    try:
        with open(os.path.join(log_dir, "output.log"), errors="replace") as f:
            out = f.read()
        for v in ("valid", "holey"):
            if v in out.splitlines():
                verdict = v
    except FileNotFoundError:
        pass
    stats["verdict"] = verdict
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("benchmark_set", choices=["organic", "synthetic"])
    ap.add_argument("--out", default=os.path.expanduser("~/benchmarks/regex-eval"))
    ap.add_argument("--common", action="store_true")
    args = ap.parse_args()

    root = os.path.join(args.out, f"check-{args.benchmark_set}")
    data = defaultdict(dict)  # config -> rel -> stats
    for config in sorted(os.listdir(root)):
        config_root = os.path.join(root, config)
        for dirpath, _, filenames in os.walk(config_root):
            if "run.out" in filenames:
                rel = os.path.relpath(dirpath, config_root)
                data[config][rel] = read_run(dirpath)

    # runlim 1.10 reports neither the child's exit code (result: is always 0)
    # nor propagates it, so "solved" is determined from Carcara's stdout verdict.
    solved = {
        config: {rel for rel, s in runs.items() if s and s["verdict"]}
        for config, runs in data.items()
    }
    common = set.intersection(*solved.values()) if args.common else None
    if common is not None:
        print(f"common instances: {len(common)}")

    header = (
        f"{'config':<14} {'#S':>6} {'valid':>6} {'holey':>6} "
        f"{'T (s)':>10} {'W (s)':>10} {'M (GB)':>8}"
    )
    print(header)
    print("-" * len(header))
    for config, runs in sorted(data.items()):
        counted = common if common is not None else solved[config]
        time = sum(float(runs[rel]["cputime"]) for rel in counted)
        wall = sum(float(runs[rel]["walltime"]) for rel in counted)
        mem = sum(int(runs[rel]["memory"]) for rel in counted) / 1024**3
        n_valid = sum(1 for rel in solved[config] if runs[rel]["verdict"] == "valid")
        n_holey = sum(1 for rel in solved[config] if runs[rel]["verdict"] == "holey")
        print(
            f"{config:<14} {len(solved[config]):>6} {n_valid:>6} {n_holey:>6} "
            f"{time:>10.1f} {wall:>10.1f} {mem:>8.1f}"
        )


if __name__ == "__main__":
    main()
