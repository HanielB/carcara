#!/usr/bin/env python3
"""The second addendum's tables and plots: runs rw5 and rw4 against rw3, the
kept holes by class, rw4 against rw5 hole by hole, and rw5 against the dsl1
arm (cvc5 at dsl-rewrite granularity, checked by Carcara), per proof.

Usage: make-rw5.py <rw5 results.json.gz> <rw4 results.json.gz> <rw3 results.json.gz> <dsl1 results.json.gz> [outdir]
Run with the analysis venv (~/cvc5/wt-diff/cluster/pyenv), which has matplotlib.

Times are as in make-rw3.py: for dsl1, cvc5 plus the check; for the pipeline
with elaboration, cvc5 plus hoist, the elaboration pass and the re-check; for
the pipeline without elaboration, the estimate from the same run (the
elaboration pass with the reconstruction phases of its holes taken out,
summed over the holes and divided by the eight workers, and no re-check).

A hole's outcome in a run is the class it was kept with (the elaboration
pass's `hole <id>: kept as trusted: [<class>]` lines), or justified when the
pass ran to its summary and did not keep it; hole ids agree across runs
because cvc5 and the hoist are the same.
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

rw5_path, rw4_path, rw3_path, dsl_path = sys.argv[1:5]
out = sys.argv[5] if len(sys.argv) > 5 else os.path.dirname(os.path.abspath(__file__))
os.makedirs(f'{out}/plots', exist_ok=True)
os.makedirs(f'{out}/tables', exist_ok=True)

LOGICS = ('QF_UF', 'QF_LIA', 'QF_LRA')
COLORS = {'QF_UF': '#1f77b4', 'QF_LIA': '#d62728', 'QF_LRA': '#2ca02c'}
KEY = re.compile(r'^\[pfchk\] ([\w-]+)=(.*)$', re.M)
PHASE = re.compile(r'^info: hole ([\w.]+): phases (.*)$', re.M)
KEPT = re.compile(r'hole (\S+): kept as trusted: \[([a-z-]+)\]')
WORKERS = 8
CLASSES = ('hole-time', 'memory', 'unproved', 'no-certificate', 'checker-rejected', 'out-of-scope', 'pass-budget')


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


def load(path, phases=False, holes=False):
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
            non_egglog = 0.0
            for _, rest in PHASE.findall(log):
                for kvp in rest.split():
                    k, _, v = kvp.partition('=')
                    if k in ('serialize', 'index', 'search', 'emit'):
                        non_egglog += F(v) or 0.0
            d['_non_egglog'] = non_egglog
        if holes:
            body = log.split('=== carcara elaborate stderr ===', 1)
            body = body[1].split('=== carcara check stdout ===', 1)[0] if len(body) > 1 else ''
            d['_ran'] = 'hole summary:' in body
            d['_kept'] = dict(KEPT.findall(body))
        tasks[r['job_args'].split('/non-incremental/', 1)[-1]] = d
    return tasks


rw5 = load(rw5_path, phases=True, holes=True)
rw4 = load(rw4_path, holes=True)
rw3 = load(rw3_path)
dsl = load(dsl_path)
RUNS = (('rw5', rw5), ('rw4', rw4), ('rw3', rw3))


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


def pipeline_time(k):
    return sum(F(k.get(x)) or 0.0 for x in ('solver_time', 'hoist_time', 'elab_time', 'check_time'))


def checking_only_time(k):
    elab = F(k.get('elab_time')) or 0.0
    return (F(k.get('solver_time')) or 0.0) + (F(k.get('hoist_time')) or 0.0) + max(elab - k.get('_non_egglog', 0.0) / WORKERS, 0.0)


def dsl_time(k):
    return (F(k.get('solver_time')) or 0.0) + (F(k.get('check_time')) or 0.0)


def ran(k):
    return k.get('holes_after') not in (None, 'none', '')


# ---------------------------------------------------------------- the runs side by side
rows = []
for l in LOGICS:
    b = [x for x in rw5 if rw5[x]['_logic'] == l]
    for name, run in RUNS:
        ks = [run[x] for x in b if x in run]
        rs = [k for k in ks if ran(k)]
        tot = sum(I(k.get('holes_before')) or 0 for k in rs)
        just = sum((I(k.get('holes_before')) or 0) - (I(k.get('holes_after')) or 0) for k in rs)
        kept = sum(I(k.get('holes_kept')) or 0 for k in rs)
        skipped = sum(I(k.get('holes_skipped')) or 0 for k in rs)
        closed = sum(I(k.get('elab_closed')) or 0 for k in rs)
        fj = sum(fully(k) for k in ks)
        holey_clean = sum(fully(k) and not untagged(k) and k.get('check_result') == 'holey' for k in ks)
        valid = sum(k.get('check_result') == 'valid' for k in ks)
        hours = sum(F(k.get('elab_time')) or 0.0 for k in ks) / 3600
        rows.append([L(l) if name == 'rw5' else '', name, fmt(tot), pct(just, tot), fmt(kept), fmt(skipped), pct(closed, tot),
                     fmt(fj), fmt(holey_clean), fmt(valid), f'{hours:.1f}'])
    rows.append('midrule')
rows.pop()
write_table('rw5-vs-rw4', ['logic', 'run', 'holes', '\\% justified', 'kept', 'skipped', '\\% by the normalizer',
                           'every hole justified', 'of those, trust steps left', 're-check \\texttt{valid}', 'pass hours'], rows)

# ---------------------------------------------------------------- kept holes by class
rows = []
for l in LOGICS:
    b = [x for x in rw5 if rw5[x]['_logic'] == l]
    for name, run in RUNS:
        cls = collections.Counter()
        for x in b:
            if x not in run:
                continue
            for key, v in run[x].items():
                if key.startswith('elab_kept_'):
                    cls[key[len('elab_kept_'):]] += I(v) or 0
        other = sum(n for c, n in cls.items() if c not in CLASSES)
        rows.append([L(l) if name == 'rw5' else '', name] + [fmt(cls[c]) for c in CLASSES] + [fmt(other)])
    rows.append('midrule')
rows.pop()
write_table('rw5-kept', ['logic', 'run'] + [c for c in CLASSES] + ['other'], rows)

# ---------------------------------------------------------------- rw4 to rw5, hole by hole
trans = collections.Counter()
by_logic = collections.defaultdict(collections.Counter)
for x, k5 in rw5.items():
    k4 = rw4.get(x)
    if not k4 or not (k5.get('_ran') and k4.get('_ran')):
        continue
    for h in set(k4['_kept']) | set(k5['_kept']):
        t = (k4['_kept'].get(h, 'justified'), k5['_kept'].get(h, 'justified'))
        if t[0] != t[1]:
            trans[t] += 1
            by_logic[t][k5['_logic']] += 1
gains = sum(n for (a, b), n in trans.items() if b == 'justified')
losses = sum(n for (a, b), n in trans.items() if a == 'justified')
shifts = sum(n for (a, b), n in trans.items() if 'justified' not in (a, b))
rows = []
for group, test in (('now justified', lambda a, b: b == 'justified'),
                    ('kept in both, the class changed', lambda a, b: 'justified' not in (a, b)),
                    ('justified in \\texttt{rw4}, kept in \\texttt{rw5}', lambda a, b: a == 'justified')):
    first = True
    for (a, b), n in trans.most_common():
        if not test(a, b) or n < 3:
            continue
        rows.append([group if first else '', a, b, fmt(n)] + [fmt(by_logic[(a, b)][l]) for l in LOGICS])
        first = False
    rows.append('midrule')
rows.pop()
write_table('rw5-transitions', ['', '\\texttt{rw4}', '\\texttt{rw5}', 'holes'] + [L(l) for l in LOGICS], rows, align='lllrrrr')

# ---------------------------------------------------------------- rw5 against dsl1
rows = []
for l in LOGICS:
    b = [x for x in dsl if dsl[x]['_logic'] == l and x in rw5]
    dv = {x for x in b if dsl[x].get('check_result') == 'valid'}
    dc = {x for x in b if dsl[x].get('proof_complete') == '1'}
    rv = {x for x in b if rw5[x].get('check_result') == 'valid'}
    rf = {x for x in b if fully(rw5[x])}
    td = [dsl_time(dsl[x]) for x in dc]
    tr = [pipeline_time(rw5[x]) for x in b]
    tc = [checking_only_time(rw5[x]) for x in b]
    rows.append([L(l), fmt(len(b)), fmt(len(dc)), fmt(len(dv)), fmt(len(rf)), fmt(len(rv)), fmt(len(dv - rv)), fmt(len(rv - dv)),
                 f'{q(td, .5):.1f} / {q(td, .9):.1f}', f'{q(tr, .5):.1f} / {q(tr, .9):.1f}', f'{q(tc, .5):.1f} / {q(tc, .9):.1f}',
                 f'{sum(td) / 3600:.1f} / {sum(tr) / 3600:.1f} / {sum(tc) / 3600:.1f}'])
write_table('rw5-head-to-head', ['logic', 'benchmarks', 'dsl1 complete', 'dsl1 \\texttt{valid}', 'rw5 every hole justified',
                                 'rw5 \\texttt{valid}', 'dsl1 only', 'rw5 only', 'dsl1 s, p50 / p90', 'rw5 s, p50 / p90',
                                 'rw5 check-only s (est.), p50 / p90', 'hours, dsl1 / rw5 / est.'], rows)

# ---------------------------------------------------------------- the CDF, as Figure dsl-cdf for rw5
plt.rcParams.update({'font.size': 9, 'axes.grid': True, 'grid.alpha': .3, 'legend.frameon': False})
fig, axes = plt.subplots(1, 3, figsize=(8.6, 2.8), sharey=True)
EDGE = 4000.0
for ax, l in zip(axes, LOGICS):
    b = [x for x in dsl if dsl[x]['_logic'] == l and x in rw5]
    n = len(b)
    arms = (
        ('cvc5 dsl-rewrite + check', [dsl_time(dsl[x]) if dsl[x].get('check_result') == 'valid' else EDGE for x in b], '-', 1.0),
        ('rw5, elaboration (valid)', [pipeline_time(rw5[x]) if rw5[x].get('check_result') == 'valid' else EDGE for x in b], '--', 1.0),
        ('rw5, elaboration (every hole justified)', [pipeline_time(rw5[x]) if fully(rw5[x]) else EDGE for x in b], '-.', 1.0),
        ('rw5, checking only (est., every hole proved)', [checking_only_time(rw5[x]) if (I(rw5[x].get('holes_kept')) == 0 and I(rw5[x].get('holes_skipped')) == 0 and rw5[x].get('okp') == '1') else EDGE for x in b], ':', 1.0),
        ('rw3, elaboration (valid)', [pipeline_time(rw3[x]) if x in rw3 and rw3[x].get('check_result') == 'valid' else EDGE for x in b], '--', .35),
    )
    for name, v, ls, alpha in arms:
        v = np.sort(np.maximum(np.asarray(v), 0.05))
        ax.step(v, np.arange(1, n + 1) / n, where='post', linestyle=ls, color=COLORS[l] if alpha == 1.0 else 'gray',
                alpha=1.0, label=name)
    ax.set_xscale('log')
    ax.set_xlim(0.05, EDGE)
    ax.set_title(f'{l} ({n})')
    ax.set_xlabel('time to a checked proof (s)')
axes[0].set_ylabel('fraction of benchmarks')
axes[0].legend(loc='upper left', fontsize=6)
fig.tight_layout()
fig.savefig(f'{out}/plots/rw5-cdf.pdf')

# ---------------------------------------------------------------- macros
allb = [x for x in dsl if x in rw5]
with open(f'{out}/tables/rw5-macros.tex', 'w') as f:
    def m(name, value):
        f.write(f'\\newcommand{{\\{name}}}{{{value}}}\n')
    m('rwfivevalid', f'{sum(rw5[x].get("check_result") == "valid" for x in rw5):,}')
    m('rwfourvalid', f'{sum(rw4[x].get("check_result") == "valid" for x in rw4):,}')
    m('rwthreevalidall', f'{sum(rw3[x].get("check_result") == "valid" for x in rw3):,}')
    m('rwfivefully', f'{sum(fully(rw5[x]) for x in rw5):,}')
    m('rwfourfully', f'{sum(fully(rw4[x]) for x in rw4):,}')
    m('rwfivehours', f'{sum(pipeline_time(rw5[x]) for x in allb) / 3600:,.1f}')
    m('rwfivecheckhours', f'{sum(checking_only_time(rw5[x]) for x in allb) / 3600:,.1f}')
    m('rwfivepasshours', f'{sum(F(rw5[x].get("elab_time")) or 0.0 for x in rw5) / 3600:,.1f}')
    m('rwfourpasshours', f'{sum(F(rw4[x].get("elab_time")) or 0.0 for x in rw4) / 3600:,.1f}')
    m('dslvalidfive', f'{sum(dsl[x].get("check_result") == "valid" for x in allb):,}')
    m('rwfivevalidh', f'{sum(rw5[x].get("check_result") == "valid" for x in allb):,}')
    m('dslonlyfive', f'{sum(dsl[x].get("check_result") == "valid" and rw5[x].get("check_result") != "valid" for x in allb):,}')
    m('rwfiveonly', f'{sum(rw5[x].get("check_result") == "valid" and dsl[x].get("check_result") != "valid" for x in allb):,}')
    m('rwfivegains', f'{gains:,}')
    m('rwfivelosses', f'{losses:,}')
    m('rwfiveshifts', f'{shifts:,}')
print('done:', len(rw5), len(rw4), len(rw3), len(dsl), 'transitions', gains, shifts, losses)
