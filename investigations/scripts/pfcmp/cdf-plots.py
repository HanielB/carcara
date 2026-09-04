#!/usr/bin/env python3
"""CDF plots for the pfcmp pipelines, plus the solving+printing scatter.

Over ALL 45,171 benchmarks (not only the commonly valid ones):
  cdf-check.pdf/png     CDFs of proof-checking time (carcara vs ethos); each
                        pipeline counts its own successfully checked proofs,
                        so the plateaus show the coverage difference
  cdf-pipeline.pdf/png  CDFs of total pipeline time (solve+print+check)
  solve-cmp.pdf/png     scatter of solving+printing time, Alethe vs CPC;
                        a side that failed to produce a proof (memout or
                        600 s budget) is placed on the border band

Usage: cdf-plots.py [alethe-dir cpc-dir [out-dir]]
"""

import os
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import polars as pl

CA, CC = '#2a78d6', '#eb6834'  # alethe/carcara blue, cpc/ethos orange

SOLVE_BAND = 1.5e3  # failed solve+print placed here (budget is 600 s)


def load(d):
    return pl.read_parquet(os.path.join(d, 'pfchk_cache.v2.parquet')).select(
        ['benchmark', 'solver_time', 'check_time', 'check_result'])


def style(ax):
    ax.spines[['top', 'right']].set_visible(False)
    ax.grid(color='#dddddd', linewidth=0.6)
    ax.set_axisbelow(True)


def cdf(ax, vals, color, label):
    vals = sorted(vals)
    ax.plot(vals, range(1, len(vals) + 1), color=color, linewidth=1.8,
            label=label)


def main():
    args = sys.argv[1:]
    d_a = args[0] if len(args) > 0 else os.path.expanduser('~/exp/results/pfcmp/all-alethe-share')
    d_c = args[1] if len(args) > 1 else os.path.expanduser('~/exp/results/pfcmp/all-cpc-fresh')
    out = args[2] if len(args) > 2 else os.path.expanduser('~/exp/pfcmp/plots-cmp5')
    os.makedirs(out, exist_ok=True)

    a = load(d_a)
    c = load(d_c)
    total = len(a)
    av = a.filter(pl.col('check_result') == 'valid')
    cv = c.filter(pl.col('check_result') == 'valid')
    print(f'{total} benchmarks; valid: alethe {len(av)}, cpc {len(cv)}')

    # ---- CDF of checking time ---------------------------------------------
    fig, ax = plt.subplots(figsize=(6.5, 4.4))
    cdf(ax, av['check_time'].to_list(), CA, f'carcara (Alethe), {len(av)}')
    cdf(ax, cv['check_time'].to_list(), CC, f'ethos (CPC), {len(cv)}')
    ax.axhline(total, color='#bbbbbb', linewidth=0.8, linestyle=':')
    ax.set_xscale('log')
    ax.set_xlim(1e-3, 2e3)
    ax.set_ylim(0, total * 1.02)
    ax.set_xlabel('proof-checking time (s)')
    ax.set_ylabel(f'benchmarks checked (of {total})')
    ax.legend(frameon=False, fontsize=9, loc='lower right')
    style(ax)
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{out}/cdf-check.{ext}', dpi=200)
    plt.close(fig)

    # ---- CDF of pipeline total --------------------------------------------
    fig, ax = plt.subplots(figsize=(6.5, 4.4))
    cdf(ax, (av['solver_time'] + av['check_time']).to_list(), CA,
        f'Alethe + carcara, {len(av)}')
    cdf(ax, (cv['solver_time'] + cv['check_time']).to_list(), CC,
        f'CPC + ethos, {len(cv)}')
    ax.axhline(total, color='#bbbbbb', linewidth=0.8, linestyle=':')
    ax.set_xscale('log')
    ax.set_xlim(1e-2, 2e3)
    ax.set_ylim(0, total * 1.02)
    ax.set_xlabel('pipeline time: solving + printing + checking (s)')
    ax.set_ylabel(f'benchmarks completed (of {total})')
    ax.legend(frameon=False, fontsize=9, loc='lower right')
    style(ax)
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{out}/cdf-pipeline.{ext}', dpi=200)
    plt.close(fig)

    # ---- scatter: solving + printing, all benchmarks ----------------------
    # A side without a produced proof (solver memout, or past the 600 s
    # budget) is placed on the border band. Rows whose only failure is in
    # checking still have honest solve+print times.
    def solve_col(df):
        produced = (pl.col('solver_time').is_not_null()
                    & pl.col('check_result').is_in(['valid', 'timeout', 'error', 'holey']))
        return df.with_columns(
            pl.when(produced).then(pl.col('solver_time'))
            .otherwise(SOLVE_BAND).alias('s'))

    j = solve_col(a).select(['benchmark', 's']).rename({'s': 'a_solve'}).join(
        solve_col(c).select(['benchmark', 's']).rename({'s': 'c_solve'}),
        on='benchmark')
    n = len(j)
    both = j.filter((pl.col('a_solve') < SOLVE_BAND) & (pl.col('c_solve') < SOLVE_BAND))
    above = (both['c_solve'] > both['a_solve']).sum()
    lo, hi = 1e-2, SOLVE_BAND * 1.6
    fig, ax = plt.subplots(figsize=(6.5, 6))
    ax.plot([lo, hi], [lo, hi], linestyle='--', color='#999999',
            linewidth=1.0, zorder=1)
    ax.annotate('y = x', xy=(2e2, 3.2e2), fontsize=8,
                color='#777777', rotation=45, ha='center', va='center')
    ax.axvline(SOLVE_BAND, color='#bbbbbb', linewidth=0.8)
    ax.axhline(SOLVE_BAND, color='#bbbbbb', linewidth=0.8)
    ax.scatter(j['a_solve'].to_list(), j['c_solve'].to_list(), s=7, color=CA,
               alpha=0.22, linewidths=0, zorder=2, rasterized=True)
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_aspect('equal')
    ax.set_xlabel('cvc5 solving + printing, Alethe (s); border = no proof')
    ax.set_ylabel('cvc5 solving + printing, CPC (s); border = no proof')
    ax.set_title(f'solving + proof printing per benchmark ({n} benchmarks;\n'
                 f'CPC cheaper on {100 * (len(both) - above) / len(both):.0f}% '
                 f'of those produced by both)', fontsize=10)
    style(ax)
    fig.tight_layout()
    for ext in ('pdf', 'png'):
        fig.savefig(f'{out}/solve-cmp.{ext}', dpi=200)
    plt.close(fig)
    print(f'wrote {out}/cdf-check, cdf-pipeline, solve-cmp')


if __name__ == '__main__':
    main()
