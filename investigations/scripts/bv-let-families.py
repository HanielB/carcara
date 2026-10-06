#!/usr/bin/env python3
"""Per-family parse time, alethe-bv round 1 (all-bv) vs round 2 (all-bv2).

Usage: bv-let-families.py <all-bv/results.json.gz> <all-bv2/results.json.gz> [<QF_BV dir>]

A benchmark counts as let-pathological when round 1 parsed its proof below
200KB/s and took more than 1s. With the local QF_BV directory, also prints the
stp_samples parse speedup bucketed by let-nesting depth of the problem.
"""
import gzip, json, os, re, statistics as st, sys
from collections import defaultdict

UNITS = {'ns': 1e-9, 'µs': 1e-6, 'ms': 1e-3, 's': 1.0}


def load(path):
    out = {}
    for line in gzip.open(path, 'rt'):
        d = json.loads(line)
        if d.get('type') != 'task':
            continue
        log = d.get('output_log', '')
        parse = re.search(r'^parsing:\s+([\d.]+)(ns|µs|ms|s)\b', log, re.M)
        size = re.search(r'proof_bytes=(\d+)', log)
        out[d['job_args'].split()[-1]] = (
            float(parse.group(1)) * UNITS[parse.group(2)] if parse else None,
            int(size.group(1)) if size else None)
    return out


def let_depth(path):
    stack, cur, best = [], 0, 0
    for m in re.finditer(r'\(\s*let\b|\(|\)', open(path, errors='replace').read()):
        if m.group(0) == ')':
            if stack and stack.pop():
                cur -= 1
        else:
            is_let = m.group(0) != '('
            stack.append(is_let)
            if is_let:
                cur += 1
                best = max(best, cur)
    return best


r1, r2 = load(sys.argv[1]), load(sys.argv[2])
fams = defaultdict(list)
for p, (t1, b) in r1.items():
    t2 = r2.get(p, (None, None))[0]
    if t1 and t2 and b:
        rel = p.split('/non-incremental/')[1]
        fams['/'.join(rel.split('/')[:2])].append((rel, t1, t2, b))

print(f"{'family':40s} {'n':>6s} {'r1 s':>9s} {'r2 s':>8s} {'x':>6s} {'patho':>6s} {'patho r1':>9s} {'patho r2':>9s}")
for fam, rows in sorted(fams.items(), key=lambda kv: -sum(r[1] - r[2] for r in kv[1]))[:12]:
    patho = [r for r in rows if r[3] / r[1] < 200e3 and r[1] > 1]
    p1, p2 = sum(r[1] for r in rows), sum(r[2] for r in rows)
    print(f"{fam:40s} {len(rows):6d} {p1:9.0f} {p2:8.0f} {p1 / p2:6.1f} {len(patho):6d}"
          f" {sum(r[1] for r in patho):9.0f} {sum(r[2] for r in patho):9.0f}")

if len(sys.argv) > 3:
    buckets = defaultdict(list)
    for rel, t1, t2, b in fams['QF_BV/stp_samples']:
        local = os.path.join(sys.argv[3], rel.split('QF_BV/', 1)[1])
        if os.path.exists(local):
            d = let_depth(local)
            buckets[next(k for k in (50, 100, 150, 10**9) if d < k)].append((t1, t2))
    print('\nstp_samples by let depth: n, median r1 ms, median r2 ms, median ratio')
    for k in sorted(buckets):
        v = buckets[k]
        label = f'< {k}' if k < 10**9 else '>= 150'
        print(f"  depth {label:6s}: {len(v):4d} {st.median(a for a, _ in v) * 1e3:6.0f}"
              f" {st.median(b for _, b in v) * 1e3:6.0f} {st.median(a / b for a, b in v):5.1f}")
