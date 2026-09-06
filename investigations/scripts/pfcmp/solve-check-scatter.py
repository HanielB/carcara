#!/usr/bin/env python3
"""Scatter of cvc5 solving+printing time vs carcara time for pfcmp, with
the BV logics (any logic whose name contains BV) and the others in
different colors.

For every benchmark whose proof checked valid, plots cvc5 solving time
(x, the runner's measured wall time) against carcara's total time
(y, parsing + checking from the carcara --stats output), log-log, with the
y = x diagonal for reference.

Usage: solve-check-scatter.py [results-dir [out-dir]]
Writes solve-vs-carcara.pdf/.png.
"""

import gzip
import json
import os
import re
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

UNIT_S = {'ns': 1e-9, 'µs': 1e-6, 'us': 1e-6, 'ms': 1e-3, 's': 1.0}
PHASE_LINE = re.compile(r'^(parsing|checking):\s+([\d.]+)(ns|µs|us|ms|s) ')

C_OTH, C_BV = '#2a78d6', '#d9822b'  # non-BV blue, BV-logic orange


def parse(results_dir):
    pts = {True: ([], []), False: ([], [])}
    with gzip.open(os.path.join(results_dir, 'results.json.gz'), 'rt') as f:
        for line in f:
            try:
                d = json.loads(line)
            except Exception:
                continue
            if d.get('type') != 'task':
                continue
            out = d['output_log']
            if '[pfchk] ok=1' not in out:
                continue
            bv = re.search(r'/[A-Z_]*BV/', d.get('job_args', '')) is not None
            solve = float(out.split('solver_time=')[1].split('\n')[0])
            phases = {}
            for l in out.splitlines():
                m = PHASE_LINE.match(l)
                if m:
                    phases[m.group(1)] = float(m.group(2)) * UNIT_S[m.group(3)]
            if 'parsing' in phases and 'checking' in phases:
                pts[bv][0].append(solve)
                pts[bv][1].append(phases['parsing'] + phases['checking'])
    return pts


def main():
    args = sys.argv[1:]
    d_res = args[0] if len(args) > 0 else \
        os.path.expanduser('~/exp/results/pfcmp/all-alethe-share')
    out = args[1] if len(args) > 1 else os.path.expanduser('~/exp/pfcmp/plots-alethe5')
    os.makedirs(out, exist_ok=True)

    pts = parse(d_res)
    n = sum(len(p[0]) for p in pts.values())
    cheaper = sum(1 for bv in pts for x, y in zip(*pts[bv]) if y < x)
    print(f'{n} benchmarks; carcara cheaper than cvc5 on {cheaper} '
          f'({100 * cheaper / n:.1f}%)')

    lo, hi = 1e-3, 2e3
    fig, ax = plt.subplots(figsize=(6.5, 6))
    ax.plot([lo, hi], [lo, hi], linestyle='--', color='#999999',
            linewidth=1.0, zorder=1)
    ax.annotate('y = x', xy=(hi * 0.4, hi * 0.55), fontsize=8,
                color='#777777', rotation=45, ha='center', va='center')
    for bv, color, label in ((True, C_BV, 'BV logics'),
                             (False, C_OTH, 'other logics')):
        xs, ys = pts[bv]
        if xs:
            ax.scatter(xs, ys, s=7, color=color, alpha=0.22, linewidths=0,
                       zorder=2, rasterized=True, label=label)
    ax.legend(frameon=False, fontsize=8, loc='upper left', markerscale=2.5)
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_aspect('equal')
    ax.set_xlabel('cvc5 solving + proof printing (s)')
    ax.set_ylabel('carcara parsing + checking (s)')
    ax.set_title(f'per-benchmark solving vs. checking ({n} valid; '
                 f'checking cheaper on {100 * cheaper / n:.1f}%)', fontsize=10)
    ax.spines[['top', 'right']].set_visible(False)
    ax.grid(color='#dddddd', linewidth=0.6)
    ax.set_axisbelow(True)
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{out}/solve-vs-carcara.{ext}', dpi=200)
    plt.close(fig)
    print(f'wrote {out}/solve-vs-carcara.{{pdf,png}}')


if __name__ == '__main__':
    main()
