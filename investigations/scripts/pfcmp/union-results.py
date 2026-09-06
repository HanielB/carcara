#!/usr/bin/env python3
"""Build the union of several runs as one run directory: <out>/results.json.gz
holds the task records of every input run (the job record and `options`
of the first), optionally dropping the benchmarks of some logics. Used to
merge the arrays corpus into the main one (dropping the nonlinear array
logics AUFNIRA and QF_AUFNIA) so that logic-tables.py and the plot scripts
work on the unified evaluation. Build the pfchk cache on the output
afterwards (pfchk-cmpr.py).

Usage: union-results.py <out-dir> [--drop LOGIC,LOGIC,...] <run-dir>...
"""

import gzip
import json
import os
import shutil
import sys


def records(d):
    with gzip.open(os.path.join(d, 'results.json.gz'), 'rt') as f:
        for line in f:
            if line.strip():
                yield json.loads(line)


def main():
    args = sys.argv[1:]
    out = args.pop(0)
    drop = set()
    if args and args[0] == '--drop':
        args.pop(0)
        drop = set(args.pop(0).split(','))
    runs = args
    os.makedirs(out, exist_ok=True)
    seen = set()
    counts = {}
    with gzip.open(os.path.join(out, 'results.json.gz'), 'wt') as g:
        for i, d in enumerate(runs):
            n = 0
            for rec in records(d):
                if rec.get('type') != 'task':
                    if i == 0:
                        g.write(json.dumps(rec) + '\n')
                    continue
                bench = rec['job_args'].split()[-1]
                logic = bench.split('/non-incremental/')[1].split('/')[0]
                if logic in drop or bench in seen:
                    continue
                seen.add(bench)
                g.write(json.dumps(rec) + '\n')
                n += 1
            counts[d] = n
    shutil.copy(os.path.join(runs[0], 'options'), os.path.join(out, 'options'))
    for d, n in counts.items():
        print(f'{n:6d} tasks from {d}')
    print(f'{len(seen)} tasks in {out}' + (f' (dropped logics: {sorted(drop)})' if drop else ''))


if __name__ == '__main__':
    main()
