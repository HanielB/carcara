#!/usr/bin/env python3
"""Within-pipeline scatters for the pfcmp Alethe configurations:

  ablation-bytes.pdf     proof size, sharing off (x) vs on (y)
  ablation-pipeline.pdf  pipeline time (solve+print+check), off vs on
  pivots-check.pdf       carcara checking time, without (x) vs with (y) pivots

Each plot is over the benchmarks valid in both runs of the pair.

Usage: ablation-scatters.py [base-dir share-dir pivots-dir pivotsfix-dir [out-dir]]
"""

import os
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import polars as pl

COLOR = '#2a78d6'

C_OTH, C_BV = '#2a78d6', '#d9822b'  # non-BV blue, QF_(UF)BV orange


def bv_mask(df):
    import polars as pl
    return df['benchmark'].str.contains('/QF_BV/|/QF_UFBV/')



def load(d):
    return pl.read_parquet(os.path.join(d, 'pfchk_cache.v2.parquet')).filter(
        pl.col('check_result') == 'valid').select(
        ['benchmark', 'solver_time', 'check_time', 'proof_bytes'])


def scatter(path, xs, ys, bv, lo, hi, xlabel, ylabel, title):
    fig, ax = plt.subplots(figsize=(6.5, 6))
    ax.plot([lo, hi], [lo, hi], linestyle='--', color='#999999',
            linewidth=1.0, zorder=1)
    ax.annotate('y = x', xy=(hi * 0.4, hi * 0.55), fontsize=8,
                color='#777777', rotation=45, ha='center', va='center')
    for want, color, label in ((True, C_BV, 'QF_(UF)BV'),
                               (False, C_OTH, 'other logics')):
        pts = [(x, y) for x, y, b in zip(xs, ys, bv) if b == want]
        if pts:
            ax.scatter([p[0] for p in pts], [p[1] for p in pts], s=7,
                       color=color, alpha=0.22, linewidths=0, zorder=2,
                       rasterized=True, label=label)
    ax.legend(frameon=False, fontsize=8, loc='upper left', markerscale=2.5)
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_aspect('equal')
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.set_title(title, fontsize=10)
    ax.spines[['top', 'right']].set_visible(False)
    ax.grid(color='#dddddd', linewidth=0.6)
    ax.set_axisbelow(True)
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{path}.{ext}', dpi=200)
    plt.close(fig)


def main():
    args = sys.argv[1:]
    base = os.path.expanduser
    d_b = args[0] if len(args) > 0 else base('~/exp/results/pfcmp/all-alethe-base')
    d_s = args[1] if len(args) > 1 else base('~/exp/results/pfcmp/all-alethe-share')
    d_p = args[2] if len(args) > 2 else base('~/exp/results/pfcmp/all-alethe-pivots2')
    d_f = args[3] if len(args) > 3 else base('~/exp/results/pfcmp/all-alethe-pivots2fix')
    out = args[4] if len(args) > 4 else base('~/exp/pfcmp/plots-cmp5')
    os.makedirs(out, exist_ok=True)

    b = load(d_b)
    s = load(d_s)
    p = pl.concat([load(d_p), load(d_f)])

    j = b.join(s, on='benchmark', suffix='_s')
    n = len(j)
    smaller = (j['proof_bytes_s'] < j['proof_bytes']).sum()
    scatter(f'{out}/ablation-bytes',
            j['proof_bytes'].to_list(), j['proof_bytes_s'].to_list(),
            bv_mask(j).to_list(), 1e2, 1e10,
            'Alethe proof size without subproof sharing (bytes)',
            'Alethe proof size with subproof sharing (bytes)',
            f'proof size per benchmark ({n} valid in both;\n'
            f'strictly smaller with sharing on {100 * smaller / n:.0f}%, larger on none)')

    xs = (j['solver_time'] + j['check_time']).to_list()
    ys = (j['solver_time_s'] + j['check_time_s']).to_list()
    scatter(f'{out}/ablation-pipeline', xs, ys, bv_mask(j).to_list(),
            1e-2, 2e3,
            'pipeline time without subproof sharing (s)',
            'pipeline time with subproof sharing (s)',
            f'solve + print + check per benchmark ({n} valid in both)')

    j = s.join(p, on='benchmark', suffix='_p')
    n = len(j)
    slower = (j['check_time_p'] > j['check_time']).sum()
    scatter(f'{out}/pivots-check',
            j['check_time'].to_list(), j['check_time_p'].to_list(),
            bv_mask(j).to_list(), 1e-3, 2e3,
            'carcara checking time without pivots (s)',
            'carcara checking time with pivots (s)',
            f'carcara checking time per benchmark ({n} valid in both;\n'
            f'slower with pivots on {100 * slower / n:.0f}%)')

    print(f'wrote {out}/ablation-bytes, ablation-pipeline, pivots-check')


if __name__ == '__main__':
    main()
