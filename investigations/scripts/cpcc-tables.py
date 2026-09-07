#!/usr/bin/env python3
"""Tables for the cpcCarcaraEval report: the CPC+carcara pipeline (cvc5 CPC
proofs with conclusions, checked by carcara through its CPC-to-Alethe
translation) against the two pfcmp pipelines, on the benchmarks of the
cpcCarcaraEval run:
  - CPC+ethos (all-cpc-union): the same proofs (minus the printed
    conclusions), so the checker comparison is like for like;
  - Alethe+carcara (all-alethe-union): the same checker on cvc5's native
    Alethe output.
Reuses the parsing and per-logic tables of ~/exp/pfcmp/logic-tables.py.
Usage: cpcc-tables.py <cpcc-dir> [<cpc-union-dir> <alethe-union-dir>] [--tex]
"""
import os
import sys

sys.path.insert(0, os.path.expanduser('~/exp/pfcmp'))
import polars as pl  # noqa: E402
from importlib import import_module  # noqa: E402

lt = import_module('logic-tables')

PFCMP = os.path.expanduser('~/exp/results/pfcmp')


def compare(x, y, nx, ny, tex):
    """Paired comparison of pipeline y against pipeline x (ratio = y/x) on
    the benchmarks both check valid, plus the unique-solve breakdown."""
    fx = x.with_columns(lt.fmt_fail(x).alias('fail'))
    fy = y.with_columns(lt.fmt_fail(y).alias('fail'))
    j = fx.join(fy, on='benchmark', suffix='_y')
    print(f'\n== {ny} vs {nx}: paired benchmarks {len(j)} ({nx} {len(x)}, {ny} {len(y)})')
    both = j.filter((pl.col('check_result') == 'valid') & (pl.col('check_result_y') == 'valid'))
    only_x = j.filter((pl.col('check_result') == 'valid') & (pl.col('check_result_y') != 'valid'))
    only_y = j.filter((pl.col('check_result') != 'valid') & (pl.col('check_result_y') == 'valid'))
    print(f'common valid {len(both)}; only {nx} {len(only_x)}; only {ny} {len(only_y)}; '
          f'neither {len(j) - len(both) - len(only_x) - len(only_y)}')
    print(f'  only-{nx}, {ny} side:', lt.only_c_breakdown(only_x, 'fail_y'))
    print(f'  only-{ny}, {nx} side:', lt.only_c_breakdown(only_y, 'fail'))
    n = len(both)
    if n == 0:
        return
    rows = []

    def add(name, a, b, unit=1.0, fmt='{:.0f}'):
        ta, tb = a.sum() / unit, b.sum() / unit
        r = b / a
        rows.append((name, fmt.format(ta), fmt.format(tb), tb / ta if ta else float('nan'),
                     r.median(), 100 * (b < a).sum() / n))

    add('checking time (s)', both['check_time'], both['check_time_y'], fmt='{:.1f}')
    # CPU times exist only for the GNU-time runners; compare them only when both sides have
    # them for every common benchmark
    if both['check_cpu'].null_count() == 0 and both['check_cpu_y'].null_count() == 0:
        add('checking CPU (s)', both['check_cpu'], both['check_cpu_y'], fmt='{:.1f}')
    add('proof size (MB)', both['proof_bytes'], both['proof_bytes_y'], 1e6, '{:.1f}')
    add('proof commands (k)', both['commands'], both['commands_y'], 1e3, '{:.1f}')
    add('proof steps (k)', both['proof_steps'], both['proof_steps_y'], 1e3, '{:.1f}')
    add('solving + printing (s)', both['solver_time'], both['solver_time_y'], fmt='{:.1f}')
    add('pipeline total (s)', both['solver_time'] + both['check_time'],
        both['solver_time_y'] + both['check_time_y'], fmt='{:.1f}')
    print(f'\n== on the {n} common benchmarks (ratio = {ny}/{nx}; median = per-benchmark; '
          f'"better" = {ny} smaller)')
    for name, ta, tb, ratio, med, pct in rows:
        if tex:
            print(f'  {name:24s} & {ta:>9s} & {tb:>9s} & {ratio:5.2f} & {med:5.2f} & {pct:.1f}\\% \\\\')
        else:
            print(f'  {name:24s} {nx:>14s} {ta:>9s}  {ny:>14s} {tb:>9s}  ratio {ratio:6.2f}  '
                  f'median {med:5.2f}  {ny} better on {pct:5.1f}%')

    g = both.group_by('logic').agg(
        pl.len().alias('n'),
        pl.col('check_time').sum().alias('chk_x'),
        pl.col('check_time_y').sum().alias('chk_y'),
        (pl.col('check_time_y') / pl.col('check_time')).median().alias('chk_med'),
        (pl.col('proof_bytes').sum() / 1e6).alias('mb_x'),
        (pl.col('proof_bytes_y').sum() / 1e6).alias('mb_y'),
        (pl.col('proof_bytes_y') / pl.col('proof_bytes')).median().alias('bytes_med'),
    )
    rows = {r['logic']: r for r in g.to_dicts()}
    q, qf = lt.logic_order(rows)
    print(f'\n== per logic on common benchmarks: n, check s ({nx}/{ny}), ratio, median ratio, '
          f'bytes MB ({nx}/{ny}), ratio, median ratio')
    for group in (q, qf):
        for l in group:
            r = rows[l]
            cr = r['chk_y'] / r['chk_x'] if r['chk_x'] else float('nan')
            br = r['mb_y'] / r['mb_x'] if r['mb_x'] else float('nan')
            name = l.replace('_', '\\_') if tex else l
            if tex:
                print(f"    {name:10s} & {r['n']:5d} & {r['chk_x']:8.1f} & {r['chk_y']:8.1f} & "
                      f"{cr:5.2f} & {r['chk_med']:5.2f} & {r['mb_x']:8.1f} & {r['mb_y']:8.1f} & "
                      f"{br:5.2f} & {r['bytes_med']:5.2f} \\\\")
            else:
                print(f"{name:10s} {r['n']:5d} {r['chk_x']:8.1f} {r['chk_y']:8.1f} {cr:6.2f} "
                      f"{r['chk_med']:6.2f} {r['mb_x']:8.1f} {r['mb_y']:8.1f} {br:5.2f} "
                      f"{r['bytes_med']:5.2f}")
        if tex:
            print('    \\midrule')


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    tex = '--tex' in sys.argv
    k = lt.parse(args[0])
    d_cpc = args[1] if len(args) > 1 else os.path.join(PFCMP, 'all-cpc-union')
    d_ale = args[2] if len(args) > 2 else os.path.join(PFCMP, 'all-alethe-union')
    bench = set(k['benchmark'].to_list())
    e = lt.parse(d_cpc).filter(pl.col('benchmark').is_in(bench))
    a = lt.parse(d_ale).filter(pl.col('benchmark').is_in(bench))

    print(f'== CPC + carcara: {len(k)} benchmarks, {k["logic"].n_unique()} logics')
    print(lt.outcome(k))
    unp = k.filter((pl.col('check_result') == 'none') & (pl.col('result') != 'unsat'))
    print('unproved (not unsat within the budget) per logic:', lt.only_c_breakdown(unp, 'logic'))
    print(lt.per_logic(k, tex))
    compare(e, k, 'CPC+ethos', 'CPC+carcara', tex)
    compare(a, k, 'Alethe+carcara', 'CPC+carcara', tex)


if __name__ == '__main__':
    main()
