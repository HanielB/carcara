#!/usr/bin/env python3
"""Per-logic tables and headline comparison numbers for the pfcmp
experiment, straight from the runners' results.json.gz (the [pfchk]
key=value lines), so proof_assumes / proof_defines are available too.

Usage: logic-tables.py <alethe-dir> <cpc-dir> [--tex]

Prints, for each pipeline: the outcome breakdown and the per-logic table
(valid checks only: problems, solving+printing time, checking time,
ratio); then the comparison on the commonly valid benchmarks (checking
time, bytes, commands, solve+print, pipeline; totals, CPC/Alethe ratio,
share of benchmarks on which CPC is better, median ratios), the unique
solves with the other side's failure class, and a per-logic comparison
table. With --tex the tables are emitted as LaTeX tabular rows.
"""

import gzip
import json
import os
import sys

import polars as pl

KEYS = ('solver_rc', 'solver_time', 'proof_bytes', 'proof_steps',
        'proof_assumes', 'proof_defines', 'check_rc', 'check_time',
        'check_result', 'ok')
NUM = {'solver_time', 'check_time', 'proof_bytes', 'proof_steps',
       'proof_assumes', 'proof_defines', 'ok'}


def parse(d):
    rows = []
    with gzip.open(os.path.join(d, 'results.json.gz'), 'rt') as f:
        for line in f:
            if not line.strip():
                continue
            rec = json.loads(line)
            if rec.get('type') != 'task':
                continue
            bench = rec['job_args'].split()[-1]
            logic = bench.split('/non-incremental/')[1].split('/')[0]
            out = rec.get('output_log') or ''
            row = {'benchmark': bench, 'logic': logic,
                   'status': rec.get('status'), 'result': None}
            for k in KEYS:
                row[k] = None
            lines = out.splitlines()
            # the runner echoes the cvc5 result line right after the header
            for i, l in enumerate(lines):
                if l.startswith('[pfchk] '):
                    k, _, v = l[8:].partition('=')
                    if k in NUM:
                        try:
                            v = float(v)
                        except ValueError:
                            v = None
                    row[k] = v
                    if row['result'] is None and i > 0:
                        row['result'] = lines[i - 1].strip()
            if row['check_result'] is None:
                # task killed before the runner printed its summary; the
                # runexec log says why
                run = rec.get('run_log') or ''
                row['check_result'] = ('memout' if 'terminationreason=memory' in run
                                       else 'killed')
            rows.append(row)
    df = pl.DataFrame(rows)
    return df.with_columns(
        (pl.col('proof_steps').fill_null(0) + pl.col('proof_assumes').fill_null(0)
         + pl.col('proof_defines').fill_null(0)).alias('commands'))


def outcome(df):
    return df.group_by('check_result').len().sort('len', descending=True)


def logic_order(logics):
    q = sorted(l for l in logics if not l.startswith('QF_'))
    qf = sorted(l for l in logics if l.startswith('QF_'))
    return q, qf


def per_logic(df, tex):
    v = df.filter(pl.col('check_result') == 'valid')
    g = v.group_by('logic').agg(pl.len().alias('n'),
                                pl.col('solver_time').sum().alias('solve'),
                                pl.col('check_time').sum().alias('check'))
    rows = {r['logic']: r for r in g.to_dicts()}
    q, qf = logic_order(rows)
    out = []

    def line(name, r):
        ratio = r['solve'] / r['check'] if r['check'] else float('nan')
        if tex:
            return (f"    {name.replace('_', chr(92) + '_'):10s} & {r['n']:6d} & "
                    f"{r['solve']:10.2f} & {r['check']:9.2f} & {ratio:6.2f} \\\\")
        return f"{name:10s} {r['n']:6d} {r['solve']:11.2f} {r['check']:10.2f} {ratio:7.2f}"

    for group in (q, qf):
        for l in group:
            out.append(line(l, rows[l]))
        out.append('    \\midrule' if tex else '')
    tot = {'n': len(v), 'solve': v['solver_time'].sum(), 'check': v['check_time'].sum()}
    out.append(line('Total', tot))
    return '\n'.join(out)


def fmt_fail(df):
    """Failure class of a benchmark on a pipeline, for the unique-solve
    breakdown."""
    return (pl.when(pl.col('check_result') == 'valid').then(pl.lit('valid'))
            .when(pl.col('check_result') == 'memout').then(pl.lit('memout (solve+print)'))
            .when(pl.col('check_result') == 'killed').then(pl.lit('killed'))
            .when(pl.col('check_result') == 'none')
            .then(pl.when(pl.col('result') == 'unsat').then(pl.lit('none/unsat'))
                  .otherwise(pl.lit('unproved in 600 s')))
            .when(pl.col('check_result') == 'no-proof').then(pl.lit('no proof (print > 600 s)'))
            .when(pl.col('check_result') == 'timeout').then(pl.lit('check timeout'))
            .otherwise(pl.col('check_result')))


def compare(a, c, tex):
    fa = a.with_columns(fmt_fail(a).alias('fail'))
    fc = c.with_columns(fmt_fail(c).alias('fail'))
    j = fa.join(fc, on='benchmark', suffix='_c')
    print(f'\n== paired benchmarks: {len(j)} '
          f'(alethe {len(a)}, cpc {len(c)})')
    both = j.filter((pl.col('check_result') == 'valid') & (pl.col('check_result_c') == 'valid'))
    only_a = j.filter((pl.col('check_result') == 'valid') & (pl.col('check_result_c') != 'valid'))
    only_c = j.filter((pl.col('check_result') != 'valid') & (pl.col('check_result_c') == 'valid'))
    neither = len(j) - len(both) - len(only_a) - len(only_c)
    print(f'common valid {len(both)}; only Alethe {len(only_a)}; only CPC {len(only_c)}; '
          f'neither {neither}')
    print('  only-Alethe, CPC side:', only_c_breakdown(only_a, 'fail_c'))
    print('  only-CPC, Alethe side:', only_c_breakdown(only_c, 'fail'))
    print('  neither, Alethe side:',
          only_c_breakdown(j.filter((pl.col('check_result') != 'valid')
                                    & (pl.col('check_result_c') != 'valid')), 'fail'))

    n = len(both)
    metrics = []

    def add(name, xa, xc, better_is_less, unit=1.0, fmt='{:.0f}'):
        ta, tc = xa.sum() / unit, xc.sum() / unit
        ratio = tc / ta if ta else float('nan')
        r = (xc / xa)
        med = r.median()
        better = ((xc < xa) if better_is_less else (xc > xa)).sum()
        metrics.append((name, fmt.format(ta), fmt.format(tc), ratio, med, 100 * better / n))

    add('checking time (s)', both['check_time'], both['check_time_c'], True)
    add('proof size (GB)', both['proof_bytes'], both['proof_bytes_c'], True, 1e9)
    add('proof commands (M)', both['commands'], both['commands_c'], True, 1e6)
    add('solving + printing (s)', both['solver_time'], both['solver_time_c'], True)
    add('pipeline total (s)', both['solver_time'] + both['check_time'],
        both['solver_time_c'] + both['check_time_c'], True)
    print(f'\n== on the {n} common benchmarks (ratio = CPC/Alethe; median = per-benchmark)')
    for name, ta, tc, ratio, med, pct in metrics:
        if tex:
            print(f'  {name:24s} & {ta:>8s} & {tc:>8s} & {ratio:5.2f} & {pct:.1f}\\% \\\\')
        else:
            print(f'  {name:24s} alethe {ta:>9s}  cpc {tc:>9s}  ratio {ratio:6.2f}  '
                  f'median {med:5.2f}  CPC better on {pct:5.1f}%')

    # per-logic comparison
    g = both.group_by('logic').agg(
        pl.len().alias('n'),
        pl.col('check_time').sum().alias('chk_a'),
        pl.col('check_time_c').sum().alias('chk_c'),
        (pl.col('proof_bytes').sum() / 1e6).alias('mb_a'),
        (pl.col('proof_bytes_c').sum() / 1e6).alias('mb_c'),
        (pl.col('proof_bytes_c') / pl.col('proof_bytes')).median().alias('bytes_med'),
        (pl.col('check_time_c') / pl.col('check_time')).median().alias('chk_med'),
        (pl.col('proof_bytes') / pl.col('proof_steps')).median().alias('bps_a'),
        (pl.col('proof_bytes_c') / pl.col('proof_steps_c')).median().alias('bps_c'),
    )
    rows = {r['logic']: r for r in g.to_dicts()}
    q, qf = logic_order(rows)
    print(f'\n== per logic on common benchmarks: n, check s (A/C), ratio, '
          f'bytes MB (A/C), ratio, median bytes ratio C/A, median B/step (A/C)')
    for group in (q, qf):
        for l in group:
            r = rows[l]
            name = l.replace('_', '\\_') if tex else l
            cr = r['chk_c'] / r['chk_a'] if r['chk_a'] else float('nan')
            br = r['mb_c'] / r['mb_a'] if r['mb_a'] else float('nan')
            if tex:
                print(f"    {name:10s} & {r['n']:6d} & {r['chk_a']:9.1f} & {r['chk_c']:9.1f} & "
                      f"{cr:6.2f} & {r['mb_a']:9.1f} & {r['mb_c']:9.1f} & {br:5.2f} & "
                      f"{r['bytes_med']:5.2f} \\\\")
            else:
                print(f"{name:10s} {r['n']:6d} {r['chk_a']:9.1f} {r['chk_c']:9.1f} {cr:6.2f} "
                      f"{r['mb_a']:9.1f} {r['mb_c']:9.1f} {br:5.2f} {r['bytes_med']:5.2f} "
                      f"{r['bps_a']:7.0f} {r['bps_c']:7.0f}")
        if tex:
            print('    \\midrule')


def only_c_breakdown(df, col):
    return dict(sorted(df.group_by(col).len().iter_rows(), key=lambda x: -x[1]))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    tex = '--tex' in sys.argv
    d_a, d_c = args[0], args[1]
    a, c = parse(d_a), parse(d_c)
    for name, df in (('Alethe + carcara', a), ('CPC + ethos', c)):
        print(f'== {name}: {len(df)} benchmarks, {df["logic"].n_unique()} logics')
        print(outcome(df))
        unp = df.filter((pl.col('check_result') == 'none') & (pl.col('result') != 'unsat'))
        print('unproved (not unsat within the budget) per logic:',
              only_c_breakdown(unp, 'logic'))
        print(per_logic(df, tex))
    compare(a, c, tex)


if __name__ == '__main__':
    main()
