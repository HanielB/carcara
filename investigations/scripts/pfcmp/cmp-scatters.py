#!/usr/bin/env python3
"""Comparison scatters for the pfcmp experiment: per-benchmark checking time
(carcara vs ethos) and proof size in bytes (Alethe vs CPC), over ALL
benchmarks. A side that failed is placed on the border band: for checking
time, a proof that was never produced or whose check timed out; for bytes,
a proof that was never produced (a checking timeout still has an honest
size).

Usage: cmp-scatters.py [alethe-dir cpc-dir [out-dir]]
Writes check-cmp.{pdf,png} and bytes-cmp.{pdf,png}.
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


CHECK_BAND = 3e3   # failed checking placed here (budget is 1200 s)
BYTES_BAND = 3e9   # missing proof placed here (largest proofs ~1 GB)


def load(d):
    return pl.read_parquet(os.path.join(d, 'pfchk_cache.v2.parquet')).select(
        ['benchmark', 'check_time', 'proof_bytes', 'check_result'])


def scatter(ax, xs, ys, bv, lo, hi, band, xlabel, ylabel, title):
    ax.plot([lo, hi], [lo, hi], linestyle='--', color='#999999',
            linewidth=1.0, zorder=1)
    ax.annotate('y = x', xy=(band * 0.05, band * 0.09), fontsize=8,
                color='#777777', rotation=45, ha='center', va='center')
    ax.axvline(band, color='#bbbbbb', linewidth=0.8)
    ax.axhline(band, color='#bbbbbb', linewidth=0.8)
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


def main():
    args = sys.argv[1:]
    d_a = args[0] if len(args) > 0 else os.path.expanduser('~/exp/results/pfcmp/all-alethe-share')
    d_c = args[1] if len(args) > 1 else os.path.expanduser('~/exp/results/pfcmp/all-cpc-fresh')
    out = args[2] if len(args) > 2 else os.path.expanduser('~/exp/pfcmp/plots-cmp5')
    os.makedirs(out, exist_ok=True)

    a = load(d_a)
    c = load(d_c)

    def cols(df, prefix):
        checked = pl.col('check_result') == 'valid'
        produced = pl.col('proof_bytes').is_not_null() & (pl.col('proof_bytes') > 0)
        return df.select(
            'benchmark',
            pl.when(checked).then(pl.col('check_time'))
            .otherwise(CHECK_BAND).alias(f'{prefix}_time'),
            pl.when(produced).then(pl.col('proof_bytes'))
            .otherwise(BYTES_BAND).alias(f'{prefix}_bytes'))

    j = cols(a, 'a').join(cols(c, 'c'), on='benchmark')
    n = len(j)

    both = j.filter((pl.col('a_time') < CHECK_BAND) & (pl.col('c_time') < CHECK_BAND))
    above = (both['c_time'] > both['a_time']).sum()
    fig, ax = plt.subplots(figsize=(6.5, 6))
    scatter(ax, j['a_time'].to_list(), j['c_time'].to_list(),
            bv_mask(j).to_list(), 1e-3, 8e3,
            CHECK_BAND,
            'carcara checking time on the Alethe proof (s); border = failed',
            'ethos checking time on the CPC proof (s); border = failed',
            f'checking time per benchmark ({n} benchmarks;\n'
            f'ethos slower on {100 * above / len(both):.0f}% of those both checked)')
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{out}/check-cmp.{ext}', dpi=200)
    plt.close(fig)

    both = j.filter((pl.col('a_bytes') < BYTES_BAND) & (pl.col('c_bytes') < BYTES_BAND))
    below = (both['c_bytes'] < both['a_bytes']).sum()
    fig, ax = plt.subplots(figsize=(6.5, 6))
    scatter(ax, j['a_bytes'].to_list(), j['c_bytes'].to_list(),
            bv_mask(j).to_list(), 1e2, 1e10,
            BYTES_BAND,
            'Alethe proof size (bytes); border = no proof',
            'CPC proof size (bytes); border = no proof',
            f'proof size per benchmark ({n} benchmarks;\n'
            f'CPC smaller on {100 * below / len(both):.0f}% of those produced by both)')
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{out}/bytes-cmp.{ext}', dpi=200)
    plt.close(fig)
    print(f'wrote {out}/check-cmp and bytes-cmp ({n} points)')


if __name__ == '__main__':
    main()
