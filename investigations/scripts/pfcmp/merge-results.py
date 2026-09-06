#!/usr/bin/env python3
"""Merge a fix run into a base run: writes <out>/results.json.gz with the
base's task records, except that every benchmark present in the fix run
takes the fix run's record (as all-alethe-pivots2fix patched round 5, and
all-arr3-alethe-fix patches arrays round 3). The job record and the
`options` file are copied from the base. Build the pfchk cache on the
output afterwards (pfchk-cmpr.py) so the table and plot scripts can use it
like any run directory.

Usage: merge-results.py <base-dir> <fix-dir> <out-dir>
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
    base, fix, out = sys.argv[1:4]
    os.makedirs(out, exist_ok=True)
    patched = {}
    for rec in records(fix):
        if rec.get('type') == 'task':
            patched[rec['job_args'].split()[-1]] = rec
    n_base = n_patched = 0
    with gzip.open(os.path.join(out, 'results.json.gz'), 'wt') as g:
        for rec in records(base):
            if rec.get('type') == 'task':
                bench = rec['job_args'].split()[-1]
                if bench in patched:
                    rec = patched.pop(bench)
                    n_patched += 1
                n_base += 1
            g.write(json.dumps(rec) + '\n')
    shutil.copy(os.path.join(base, 'options'), os.path.join(out, 'options'))
    print(f'{n_base} tasks written, {n_patched} patched from the fix run; '
          f'{len(patched)} fix benchmarks not in the base (ignored)')


if __name__ == '__main__':
    main()
