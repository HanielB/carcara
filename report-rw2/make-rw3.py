#!/usr/bin/env python3
"""The addendum's tables and plots: run rw3 against rw2, and the dsl1 arm
(cvc5 at dsl-rewrite granularity, checked by Carcara) against the pipeline,
per proof.

Usage: make-rw3.py <rw3 results.json.gz> <rw2 results.json.gz> <dsl1 results.json.gz> [outdir]
Run with the analysis venv (~/cvc5/wt-diff/cluster/pyenv), which has matplotlib.

"Time to a checked proof" is, for dsl1, cvc5 plus the check; for the
pipeline with elaboration, cvc5 plus hoist, the elaboration pass and the
re-check; for the pipeline without elaboration, an estimate from the same
run: cvc5 plus hoist plus the elaboration pass with the reconstruction
phases (serialize, index, search, emit) of its holes taken out, summed over
the holes and divided by the eight workers, and no re-check.  The estimate
keeps the pass's parsing, its checking of the non-hole steps and every
egglog phase, which is what a checking-only pass does.
"""
import collections
import gzip
import json
import os
import re
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

rw3_path, rw2_path, dsl_path = sys.argv[1:4]
out = sys.argv[4] if len(sys.argv) > 4 else os.path.dirname(os.path.abspath(__file__))
os.makedirs(f'{out}/plots', exist_ok=True)
os.makedirs(f'{out}/tables', exist_ok=True)

LOGICS = ('QF_UF', 'QF_LIA', 'QF_LRA')
COLORS = {'QF_UF': '#1f77b4', 'QF_LIA': '#d62728', 'QF_LRA': '#2ca02c'}
KEY = re.compile(r'^\[pfchk\] ([\w-]+)=(.*)$', re.M)
PHASE = re.compile(r'^info: hole ([\w.]+): phases (.*)$', re.M)
WORKERS = 8


def F(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def I(x):
    try:
        return int(x)
    except (TypeError, ValueError):
        return None


def load(path, phases=False):
    tasks = {}
    for line in gzip.open(path, 'rt'):
        if not line.strip():
            continue
        r = json.loads(line)
        if r.get('type') != 'task':
            continue
        log = r.get('output_log', '') or ''
        d = dict(KEY.findall(log))
        d['_logic'] = next((l for l in LOGICS if f'/{l}/' in r['job_args']), None)
        if phases:
            # the reconstruction phases of every hole, summed (seconds)
            non_egglog = 0.0
            for _, rest in PHASE.findall(log):
                for kvp in rest.split():
                    k, v = kvp.split('=')
                    if k in ('serialize', 'index', 'search', 'emit'):
                        non_egglog += float(v)
            d['_non_egglog'] = non_egglog
        tasks[r['job_args'].split('/non-incremental/', 1)[-1]] = d
    return tasks


rw3 = load(rw3_path, phases=True)
rw2 = load(rw2_path)
dsl = load(dsl_path)


def fully(k):
    return k.get('okp') == '1' and k.get('holes_after') == '0'


def untagged(k):
    return k.get('holes_untagged', '0') not in ('0', 'none', '')


def fmt(n):
    if isinstance(n, float):
        return f'{n:,.1f}'
    return f'{n:,}'


def pct(a, b):
    return f'{100 * a / b:.2f}' if b else '--'


def L(l):
    return l.replace('_', '\\_')


def write_table(name, header, rows, align=None):
    align = align or ('l' + 'r' * (len(header) - 1))
    with open(f'{out}/tables/{name}.tex', 'w') as f:
        f.write('\\begin{tabular}{' + align + '}\n\\toprule\n')
        f.write(' & '.join(header) + ' \\\\\n\\midrule\n')
        for row in rows:
            if row == 'midrule':
                f.write('\\midrule\n')
                continue
            f.write(' & '.join(str(c) for c in row) + ' \\\\\n')
        f.write('\\bottomrule\n\\end{tabular}\n')


def q(v, p):
    if len(v) == 0:
        return float('nan')
    v = np.sort(np.asarray(v))
    return float(v[min(len(v) - 1, int(p * len(v)))])


# ---------------------------------------------------------------- times
def pipeline_time(k):
    return sum(F(k.get(x)) or 0.0 for x in ('solver_time', 'hoist_time', 'elab_time', 'check_time'))


def checking_only_time(k):
    elab = F(k.get('elab_time')) or 0.0
    return (F(k.get('solver_time')) or 0.0) + (F(k.get('hoist_time')) or 0.0) + max(elab - k.get('_non_egglog', 0.0) / WORKERS, 0.0)


def dsl_time(k):
    return (F(k.get('solver_time')) or 0.0) + (F(k.get('check_time')) or 0.0)


# ---------------------------------------------------------------- tables
# rw3 against rw2
rows = []
for l in LOGICS:
    b = [x for x in rw3 if rw3[x]['_logic'] == l]
    for name, run in (('rw3', rw3), ('rw2', rw2)):
        ks = [run[x] for x in b if x in run]
        ran = [k for k in ks if k.get('holes_after') not in (None, 'none', '')]
        tot = sum(I(k.get('holes_before')) or 0 for k in ran)
        just = sum((I(k.get('holes_before')) or 0) - (I(k.get('holes_after')) or 0) for k in ran)
        kept = sum(I(k.get('holes_kept')) or 0 for k in ran)
        skipped = sum(I(k.get('holes_skipped')) or 0 for k in ran)
        closed = sum(I(k.get('elab_closed')) or 0 for k in ran)
        fj = sum(fully(k) for k in ks)
        holey_clean = sum(fully(k) and not untagged(k) and k.get('check_result') == 'holey' for k in ks)
        valid = sum(k.get('check_result') == 'valid' for k in ks)
        hours = sum(F(k.get('elab_time')) or 0.0 for k in ks) / 3600
        rows.append([L(l) if name == 'rw3' else '', name, fmt(tot), pct(just, tot), fmt(kept), fmt(skipped), pct(closed, tot),
                     fmt(fj), fmt(holey_clean), fmt(valid), f'{hours:.1f}'])
    rows.append('midrule')
rows.pop()
write_table('rw3-vs-rw2', ['logic', 'run', 'holes', '\\% justified', 'kept', 'skipped', '\\% by the normalizer',
                           'every hole justified', 'of those, trust steps left', 're-check \\texttt{valid}', 'pass hours'], rows)

# dsl1 per logic
rows = []
for l in LOGICS:
    ks = [k for k in dsl.values() if k['_logic'] == l]
    comp = [k for k in ks if k.get('proof_complete') == '1']
    chk = collections.Counter(k.get('check_result') for k in comp)
    holes = sum(I(k.get('holes')) or 0 for k in comp)
    withholes = sum(1 for k in comp if (I(k.get('holes')) or 0) > 0)
    missing = sum(1 for k in comp if (I(k.get('rules_missing')) or 0) > 0)
    st = [F(k.get('solver_time')) or 0.0 for k in comp]
    ct = [F(k.get('check_time')) or 0.0 for k in comp]
    rows.append([L(l), fmt(len(ks)), fmt(len(comp)), fmt(chk['valid']), fmt(chk['holey']), fmt(chk['error']), fmt(chk['timeout']),
                 f'{holes:,} in {withholes:,}', fmt(missing), f'{q(st, .5):.2f} / {q(st, .9):.1f}', f'{q(ct, .5):.2f} / {q(ct, .9):.1f}',
                 f'{sum(ct) / 3600:.2f}'])
write_table('dsl1', ['logic', 'benchmarks', 'complete', '\\texttt{valid}', '\\texttt{holey}', 'error', 'time-out',
                     'holes left (proofs)', 'rule missing', 'cvc5 s, p50 / p90', 'check s, p50 / p90', 'check hours'], rows)

# head to head
rows = []
for l in LOGICS:
    b = [x for x in dsl if dsl[x]['_logic'] == l and x in rw3]
    dv = {x for x in b if dsl[x].get('check_result') == 'valid'}
    dc = {x for x in b if dsl[x].get('proof_complete') == '1'}
    rv = {x for x in b if rw3[x].get('check_result') == 'valid'}
    rf = {x for x in b if fully(rw3[x])}
    td = [dsl_time(dsl[x]) for x in dc]
    tr = [pipeline_time(rw3[x]) for x in b]
    tc = [checking_only_time(rw3[x]) for x in b]
    rows.append([L(l), fmt(len(b)), fmt(len(dc)), fmt(len(dv)), fmt(len(rf)), fmt(len(rv)), fmt(len(dv - rv)), fmt(len(rv - dv)),
                 f'{q(td, .5):.1f} / {q(td, .9):.1f}', f'{q(tr, .5):.1f} / {q(tr, .9):.1f}', f'{q(tc, .5):.1f} / {q(tc, .9):.1f}',
                 f'{sum(td) / 3600:.1f} / {sum(tr) / 3600:.1f} / {sum(tc) / 3600:.1f}'])
write_table('head-to-head', ['logic', 'benchmarks', 'dsl1 complete', 'dsl1 \\texttt{valid}', 'rw3 every hole justified',
                             'rw3 \\texttt{valid}', 'dsl1 only', 'rw3 only', 'dsl1 s, p50 / p90', 'rw3 s, p50 / p90',
                             'rw3 check-only s (est.), p50 / p90', 'hours, dsl1 / rw3 / est.'], rows)

# ---------------------------------------------------------------- plots
plt.rcParams.update({'font.size': 9, 'axes.grid': True, 'grid.alpha': .3, 'legend.frameon': False})


def cdf(ax, v, **kw):
    v = np.sort(np.asarray(v))
    ax.step(v, np.arange(1, len(v) + 1) / len(v), where='post', **kw)


# CDF of the time to a checked proof, per logic, three arms, over the
# benchmarks of the sets (a benchmark the arm does not finish is drawn at
# the right edge: the curve's height at the edge is the arm's coverage).
fig, axes = plt.subplots(1, 3, figsize=(8.6, 2.8), sharey=True)
EDGE = 4000.0
for ax, l in zip(axes, LOGICS):
    b = [x for x in dsl if dsl[x]['_logic'] == l and x in rw3]
    n = len(b)
    arms = (
        ('cvc5 dsl-rewrite + check', [dsl_time(dsl[x]) if dsl[x].get('check_result') == 'valid' else EDGE for x in b], '-'),
        ('pipeline, elaboration (valid)', [pipeline_time(rw3[x]) if rw3[x].get('check_result') == 'valid' else EDGE for x in b], '--'),
        ('pipeline, elaboration (every hole justified)', [pipeline_time(rw3[x]) if fully(rw3[x]) else EDGE for x in b], '-.'),
        ('pipeline, checking only (est., every hole proved)', [checking_only_time(rw3[x]) if (I(rw3[x].get('holes_kept')) == 0 and I(rw3[x].get('holes_skipped')) == 0 and rw3[x].get('okp') == '1') else EDGE for x in b], ':'),
    )
    for name, v, ls in arms:
        v = np.sort(np.maximum(np.asarray(v), 0.05))
        ax.step(v, np.arange(1, n + 1) / n, where='post', linestyle=ls, color=COLORS[l], label=name)
    ax.set_xscale('log')
    ax.set_xlim(0.05, EDGE)
    ax.set_title(f'{l} ({n})')
    ax.set_xlabel('time to a checked proof (s)')
axes[0].set_ylabel('fraction of benchmarks')
axes[0].legend(loc='upper left', fontsize=6)
fig.tight_layout()
fig.savefig(f'{out}/plots/dsl-cdf.pdf')

# scatter, per proof: dsl1 against the pipeline with elaboration (left) and
# against the checking-only estimate (right); a proof an arm does not
# finish sits on the edge.
for suffix, right_time, right_ok, right_label in (
    ('elab', pipeline_time, lambda k: k.get('check_result') == 'valid', 'pipeline with elaboration (s)'),
    ('check', checking_only_time, lambda k: I(k.get('holes_kept')) == 0 and I(k.get('holes_skipped')) == 0 and k.get('okp') == '1', 'pipeline, checking only, estimate (s)'),
):
    fig, ax = plt.subplots(figsize=(4.6, 4.2))
    for l in LOGICS:
        b = [x for x in dsl if dsl[x]['_logic'] == l and x in rw3]
        xs = [max(dsl_time(dsl[x]), 0.05) if dsl[x].get('check_result') == 'valid' else EDGE for x in b]
        ys = [max(right_time(rw3[x]), 0.05) if right_ok(rw3[x]) else EDGE for x in b]
        ax.scatter(xs, ys, s=4, alpha=.35, color=COLORS[l], label=l, linewidths=0)
    ax.plot([0.05, EDGE], [0.05, EDGE], color='k', linewidth=.8, linestyle=':')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlim(0.04, EDGE * 1.3)
    ax.set_ylim(0.04, EDGE * 1.3)
    ax.set_xlabel('cvc5 dsl-rewrite + check (s)')
    ax.set_ylabel(right_label)
    ax.legend(loc='upper left', markerscale=3)
    fig.tight_layout()
    fig.savefig(f'{out}/plots/dsl-scatter-{suffix}.pdf')

# macros
allb = [x for x in dsl if x in rw3]
dv = sum(dsl[x].get('check_result') == 'valid' for x in allb)
rv = sum(rw3[x].get('check_result') == 'valid' for x in allb)
with open(f'{out}/tables/rw3-macros.tex', 'w') as f:
    f.write(f'\\newcommand{{\\dslvalid}}{{{dv:,}}}\n')
    f.write(f'\\newcommand{{\\rwthreevalid}}{{{rv:,}}}\n')
    f.write(f'\\newcommand{{\\dslonly}}{{{sum(dsl[x].get("check_result") == "valid" and rw3[x].get("check_result") != "valid" for x in allb):,}}}\n')
    f.write(f'\\newcommand{{\\rwthreefully}}{{{sum(fully(rw3[x]) for x in allb):,}}}\n')
    f.write(f'\\newcommand{{\\dslhours}}{{{sum(dsl_time(dsl[x]) for x in allb if dsl[x].get("proof_complete") == "1") / 3600:,.1f}}}\n')
    f.write(f'\\newcommand{{\\rwthreehours}}{{{sum(pipeline_time(rw3[x]) for x in allb) / 3600:,.1f}}}\n')
    f.write(f'\\newcommand{{\\rwthreecheckhours}}{{{sum(checking_only_time(rw3[x]) for x in allb) / 3600:,.1f}}}\n')
print('done:', len(rw3), len(rw2), len(dsl))
