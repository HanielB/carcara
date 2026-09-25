#!/usr/bin/env python3
"""Extract the numbers of the egglog-holes run rw2 and render the plots and
tables that report.tex includes.

Usage: make-rw2.py <results.json.gz> [outdir]
Run with the analysis venv (~/cvc5/wt-diff/cluster/pyenv), which has matplotlib.

rw2 has one elaboration pass per proof (no checking pass): "proved" is
derived from it as justified + no-certificate + checker-rejected + killed
after egglog, since a hole whose worker died in serialization or in the
search had its goal proved by egglog.
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

path = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else os.path.dirname(os.path.abspath(__file__))
os.makedirs(f'{out}/plots', exist_ok=True)
os.makedirs(f'{out}/tables', exist_ok=True)

LOGICS = ('QF_UF', 'QF_LIA', 'QF_LRA')
COLORS = {'QF_UF': '#1f77b4', 'QF_LIA': '#d62728', 'QF_LRA': '#2ca02c'}
KEY = re.compile(r'^\[pfchk\] ([\w-]+)=(.*)$', re.M)
HOLE = re.compile(r'^(?:info|warn): hole ([\w.]+): (justified in|kept as trusted:|skipped:) ?(.*)$', re.M)
PHASE = re.compile(r'^info: hole ([\w.]+): phases (.*)$', re.M)
PRENORM = re.compile(r'^info: hole prenorm: (\d+) normalized goals tried, (\d+) proved and bridged, (\d+) of the (\d+) retried', re.M)
DURING = re.compile(r'killed after [\d.]+s during (\w+)')
SECS = re.compile(r'([\d.]+)s')
ELAB_BUDGET, HOLE_LIMIT, HOLE_MEM = 1500, 60, 6
PHASES = ('egglog', 'serialize', 'index', 'search', 'emit')

REASON_ORDER = ['killed at the per-hole limit, inside egglog', 'killed at the per-hole limit, after egglog',
                'no certificate', 'killed at the 6 GB limit', 'egglog could not prove', 'checker rejected',
                'killed by the pass budget', 'certificate failed to decode', 'worker error']


def reason_class(reason):
    if 'hard budget exhausted' in reason:
        return 'killed at the per-hole limit, inside egglog' if 'during egglog' in reason else 'killed at the per-hole limit, after egglog'
    if "proof's hole budget" in reason:
        return 'killed by the pass budget'
    if 'signal 6' in reason or 'allocation of' in reason:
        return 'killed at the 6 GB limit'
    if 'no certificate found' in reason:
        return 'no certificate'
    if 'checking the reconstructed steps' in reason:
        return 'checker rejected'
    if 'failed to decode' in reason:
        return 'certificate failed to decode'
    if 'egglog check' in reason or 'Check failed' in reason:
        return 'egglog could not prove'
    return 'worker error'


PROVED_CLASSES = {'killed at the per-hole limit, after egglog', 'no certificate', 'checker rejected',
                  'certificate failed to decode'}


def rejected_rule(reason):
    m = re.search(r"with rule '?([\w_]+)", reason)
    return m.group(1) if m else 'unknown'


def section(log, name):
    m = re.search(rf'=== {re.escape(name)} ===\n(.*?)(?=\n=== |\Z)', log, re.S)
    return m.group(1) if m else ''


def q(v, p):
    if len(v) == 0:
        return float('nan')
    v = np.sort(np.asarray(v))
    return float(v[min(len(v) - 1, int(p * len(v)))])


def I(x):
    try:
        return int(x)
    except (TypeError, ValueError):
        return None


def F(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


# ---------------------------------------------------------------- parse
tasks = []
holes = {l: {} for l in LOGICS}          # (bench, hid) -> (outcome, time, class, reason)
phases = {l: {} for l in LOGICS}         # (bench, hid) -> {phase: seconds}
killed_in = collections.Counter()
rejected = collections.Counter()
for line in gzip.open(path, 'rt'):
    if not line.strip():
        continue
    r = json.loads(line)
    if r.get('type') != 'task':
        continue
    args = r['job_args']
    logic = next((l for l in LOGICS if f'/{l}/' in args), None)
    if logic is None:
        continue
    log = r.get('output_log', '') or ''
    kv = dict(KEY.findall(log))
    run = r.get('run_log', '') or ''
    mem = re.search(r'^memory=(\d+)B', run, re.M)
    wall = re.search(r'^walltime=([\d.]+)s', run, re.M)
    hoist_err = re.sub(r'\x1b\[[\d;]*m', '', section(log, 'carcara hoist stderr'))
    t = {
        'logic': logic, 'bench': args.rsplit('/', 1)[-1],
        'family': args.split('/non-incremental/')[-1].split('/')[1],
        'mem_gb': int(mem.group(1)) / 2**30 if mem else 0.0,
        'wall': float(wall.group(1)) if wall else 0.0,
        'hoist_pivot': 'pivot was not found' in hoist_err,
    }
    for k in ('solver_rc', 'proof_complete', 'hoist_rc', 'upfront', 'okp', 'elab_rc', 'check_rc', 'check_result', 'ok'):
        t[k] = kv.get(k)
    for k in ('solver_time', 'hoist_time', 'elab_time', 'check_time', 'elab_holes_time'):
        t[k] = F(kv.get(k))
    for k in ('proof_bytes', 'holes_orig', 'holes_untagged', 'holes_before', 'holes_after', 'holes_kept',
              'holes_skipped', 'elab_closed', 'elab_rewritten', 'elab_bridged',
              'elab_killed_during_egglog', 'elab_killed_after_egglog'):
        t[k] = I(kv.get(k))
    text = section(log, 'carcara elaborate stderr')
    pre = PRENORM.search(text)
    t['pre_tried'], t['pre_bridged'], t['pre_retry_ok'], t['pre_retry'] = (int(x) for x in pre.groups()) if pre else (0, 0, 0, 0)
    tasks.append(t)
    bench = t['bench']
    d = holes[logic]
    for hid, what, rest in HOLE.findall(text):
        if what == 'justified in':
            d[(bench, hid)] = ('ok', float(SECS.search(rest).group(1)), None, None)
        elif what == 'kept as trusted:':
            tm = SECS.search(rest) if 'killed after' in rest else None
            cls = reason_class(rest)
            d[(bench, hid)] = ('kept', float(tm.group(1)) if tm else None, cls, rest)
            if cls == 'checker rejected':
                rejected[(logic, rejected_rule(rest))] += 1
            m = DURING.search(rest)
            if m:
                killed_in[(logic, m.group(1))] += 1
        else:
            d[(bench, hid)] = ('skipped', None, 'skipped', None)
    for hid, rest in PHASE.findall(text):
        phases[logic][(bench, hid)] = {k: float(v) for k, v in (kvp.split('=') for kvp in rest.split())}

by_logic = {l: [t for t in tasks if t['logic'] == l] for l in LOGICS}
ran = {l: [t for t in by_logic[l] if t['holes_after'] is not None] for l in LOGICS}


def fmt(n):
    if isinstance(n, float):
        return f'{n:,.1f}'
    return f'{n:,}'


def pct(a, b):
    return f'{100 * a / b:.1f}' if b else '--'


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


def fully(t):
    return t['okp'] == '1' and t['holes_after'] == 0


def untagged(t):
    return (t['holes_untagged'] or 0) > 0


# ---------------------------------------------------------------- tables
# 1. yield
rows = []
for l in LOGICS:
    ts = by_logic[l]
    hb = np.array([t['holes_before'] or 0 for t in ts])
    nf = sum(fully(t) for t in ts)
    rows.append([L(l), fmt(len(ts)), fmt(sum(t['holes_orig'] or 0 for t in ts)), fmt(int(hb.sum())),
                 fmt(int(q(hb, .5))), fmt(int(q(hb, .9))), fmt(int(hb.max())),
                 f'{nf:,} ({pct(nf, len(ts))}\\%)', fmt(sum(t['check_result'] == 'valid' for t in ts))])
write_table('yield', ['logic', 'proofs', 'hole steps', 'holes', 'p50', 'p90', 'max', 'every hole justified', 're-check \\texttt{valid}'], rows)

# 2. outcome of every benchmark
OUTCOMES = ['re-check \\texttt{valid}',
            're-check \\texttt{holey}: every hole justified, untagged holes left',
            're-check \\texttt{holey}: every hole justified, a trust step of the elaborator left',
            're-check \\texttt{holey}: a hole kept or skipped',
            're-check timeout (900 s)',
            'hoist + prune rejected the proof (resolution pivot)',
            'hoist + prune timeout (300 s)',
            'elaboration pass external limit (1,600 s)',
            'task killed at the job memory limit (60 GB) before the pass ended',
            'other']


def outcome(t):
    if t['hoist_rc'] not in ('0', None):
        return OUTCOMES[5] if t['hoist_pivot'] else OUTCOMES[6]
    if t['elab_rc'] is None:
        return OUTCOMES[8]
    if t['elab_rc'] == '124':
        return OUTCOMES[7]
    if t['check_result'] == 'timeout':
        return OUTCOMES[4]
    if t['check_result'] == 'valid':
        return OUTCOMES[0]
    if t['check_result'] == 'holey':
        if not fully(t):
            return OUTCOMES[3]
        return OUTCOMES[1] if untagged(t) else OUTCOMES[2]
    return OUTCOMES[9]


counts = {l: collections.Counter(outcome(t) for t in by_logic[l]) for l in LOGICS}
write_table('outcomes', ['outcome'] + [L(l) for l in LOGICS],
            [[k] + [fmt(counts[l][k]) for l in LOGICS] for k in OUTCOMES if any(counts[l][k] for l in LOGICS)], 'p{8.6cm}rrr')

# 3. hole outcomes of the pass, with the derived checking view
rows = []
for l in LOGICS:
    ts = ran[l]
    tot = sum(t['holes_before'] for t in ts)
    just = sum(t['holes_before'] - t['holes_after'] for t in ts)
    kept = sum(t['holes_kept'] or 0 for t in ts)
    skipped = sum(t['holes_skipped'] or 0 for t in ts)
    proved_lost = sum(1 for rec in holes[l].values() if rec[0] == 'kept' and rec[2] in PROVED_CLASSES)
    att = just + kept
    rows.append([L(l), fmt(tot), fmt(att), fmt(just), fmt(kept), fmt(skipped), pct(just, att), pct(just, tot),
                 fmt(proved_lost), f'{100 * (just + proved_lost) / tot:.2f}'])
write_table('passes', ['logic', 'holes', 'attempted', 'justified', 'kept', 'skipped', '\\% of attempted', '\\% of all',
                       'proved, lost after egglog', 'proved, \\% of all'], rows)

# 4. the normalizer's share
rows = []
for l in LOGICS:
    ts = ran[l]
    tot = sum(t['holes_before'] for t in ts)
    closed = sum(t['elab_closed'] or 0 for t in ts)
    tried = sum(t['pre_tried'] for t in ts)
    bridged = sum(t['pre_bridged'] for t in ts)
    retry, retry_ok = sum(t['pre_retry'] for t in ts), sum(t['pre_retry_ok'] for t in ts)
    just = sum(t['holes_before'] - t['holes_after'] for t in ts)
    stated = just - closed - bridged - retry_ok
    rows.append([L(l), fmt(tot), f'{closed:,} ({pct(closed, tot)}\\%)', fmt(tried), fmt(bridged), f'{retry_ok:,} of {retry:,}',
                 fmt(stated), pct(just, tot)])
write_table('normalizer', ['logic', 'holes', 'closed by the normalizer', 'normal form to egglog', 'proved, bridged',
                           'retried as stated, proved', 'stated goal only', '\\% justified'], rows)

# 5. budget
rows = []
for l in LOGICS:
    ts = ran[l]
    hit = [t for t in ts if (t['holes_skipped'] or 0) > 0 or (t['elab_time'] or 0) >= ELAB_BUDGET]
    ext = [t for t in by_logic[l] if t['elab_rc'] == '124']
    hb = [t['holes_before'] for t in ts]
    big = [h for h in hb if h > 10000]
    rows.append([L(l), fmt(len(ts)), fmt(len(hit)), fmt(sum(t['holes_skipped'] or 0 for t in hit)), fmt(len(ext)),
                 fmt(len(big)), pct(sum(big), sum(hb))])
write_table('budget', ['logic', 'proofs run', 'hit 1,500 s', 'holes skipped there', 'hit the 1,600 s external limit',
                       'proofs $>$10k holes', '\\% of holes'], rows)

# 6. kept reasons
reasons = collections.Counter()
for l in LOGICS:
    for rec in holes[l].values():
        if rec[0] == 'kept':
            reasons[(l, rec[2])] += 1
rows = []
for why in REASON_ORDER:
    if sum(reasons[(l, why)] for l in LOGICS) == 0:
        continue
    rows.append([why] + [fmt(reasons[(l, why)]) for l in LOGICS] + [fmt(sum(reasons[(l, why)] for l in LOGICS))])
rows.append('midrule')
rows.append(['total'] + [fmt(sum(v for (ll, w), v in reasons.items() if ll == l)) for l in LOGICS] + [fmt(sum(reasons.values()))])
write_table('reasons', ['reason'] + [L(l) for l in LOGICS] + ['all'], rows, 'p{6.4cm}rrrr')

# 7. checker rejections by rule
rows = []
for rule in sorted({r for (_, r) in rejected}, key=lambda r: -sum(rejected[(l, r)] for l in LOGICS)):
    rows.append(['\\texttt{' + rule.replace('_', '\\_') + '}'] + [fmt(rejected[(l, rule)]) for l in LOGICS])
write_table('errors', ['rule of the rejected step'] + [L(l) for l in LOGICS], rows)

# 8. per-hole timing
rows = []
for l in LOGICS:
    allt = np.array([rec[1] for rec in holes[l].values() if rec[0] == 'ok'])
    egg = np.array([rec[1] for k, rec in holes[l].items() if rec[0] == 'ok' and k in phases[l]])
    for name, ts in (('all justified', allt), ('through egglog', egg)):
        rows.append([L(l) if name == 'all justified' else '', name, fmt(len(ts)), f'{q(ts, .5):.2f}', f'{q(ts, .9):.2f}',
                     f'{q(ts, .99):.2f}', f'{ts.max():.1f}', fmt(int((ts >= 10).sum())), f'{ts.sum() / 3600:.1f}'])
write_table('timing', ['logic', 'holes', 'finished', 'p50', 'p90', 'p99', 'max', '$\\geq$10 s', 'CPU hours'], rows)

# 9. phases
rows = []
for l in LOGICS:
    per = {ph: np.array([p.get(ph, 0.0) for p in phases[l].values()]) for ph in PHASES}
    tot = sum(v.sum() for v in per.values())
    for ph in PHASES:
        v = per[ph]
        rows.append([L(l) if ph == 'egglog' else '', ph, fmt(len(v)), f'{q(v, .5):.3f}', f'{q(v, .9):.3f}',
                     f'{v.max():.1f}', pct(v.sum(), tot), fmt(killed_in[(l, ph)])])
    rows.append('midrule')
rows.pop()
write_table('phases', ['logic', 'phase', 'holes', 'p50', 'p90', 'max', '\\% of time', 'kills in phase'], rows)

# 10. families with the most holes
rows = []
for l in LOGICS:
    fam = collections.defaultdict(lambda: [0, 0, 0, 0, 0])
    for t in ran[l]:
        f = fam[t['family']]
        f[0] += 1
        f[1] += t['holes_before']
        f[2] += t['holes_before'] - t['holes_after']
        f[3] += t['holes_kept'] or 0
        f[4] += t['holes_skipped'] or 0
    for name, (n, h, j, k, s) in sorted(fam.items(), key=lambda x: -x[1][1])[:5]:
        rows.append([L(l), '\\texttt{' + L(name) + '}', fmt(n), fmt(h), pct(j, h), pct(k, h), pct(s, h)])
    rows.append('midrule')
rows.pop()
write_table('families', ['logic', 'family', 'proofs', 'holes', '\\% justified', '\\% kept', '\\% skipped'], rows)

# 11. residue by family
rows = []
for l in LOGICS:
    fam = collections.defaultdict(lambda: {'proofs': 0, 'fully': 0, 'kept': 0, 'skipped': 0, 'cls': collections.Counter()})
    for t in by_logic[l]:
        f = fam[t['family']]
        f['proofs'] += 1
        f['fully'] += fully(t)
        f['kept'] += t['holes_kept'] or 0
        f['skipped'] += t['holes_skipped'] or 0
    for (bench, hid), rec in holes[l].items():
        if rec[0] == 'kept':
            fam[next(t['family'] for t in by_logic[l] if t['bench'] == bench)]['cls'][rec[2]] += 1
    for name, f in sorted(fam.items(), key=lambda x: -(x[1]['kept'] + x[1]['skipped']))[:6]:
        if f['kept'] + f['skipped'] == 0:
            continue
        top = ', '.join(f'{v:,} {w}' for w, v in f['cls'].most_common(2))
        rows.append([L(l), '\\texttt{' + L(name) + '}', fmt(f['proofs']), fmt(f['fully']), fmt(f['kept']), fmt(f['skipped']), top])
    rows.append('midrule')
rows.pop()
write_table('residue-families', ['logic', 'family', 'proofs', 'every hole justified', 'kept', 'skipped', 'dominant classes'], rows,
            'llrrrrp{6.2cm}')

# 12. fully justified x untagged x re-check
rows = []
for l in LOGICS:
    ts = by_logic[l]
    fj_unt = [t for t in ts if fully(t) and untagged(t)]
    fj_clean = [t for t in ts if fully(t) and not untagged(t)]
    rows.append([L(l), fmt(sum(untagged(t) for t in ts)), fmt(len(fj_unt)), fmt(len(fj_clean)),
                 fmt(sum(t['check_result'] == 'valid' for t in fj_clean)), fmt(sum(t['check_result'] == 'holey' for t in fj_clean)),
                 fmt(sum(t['check_result'] == 'timeout' for t in ts))])
write_table('valid', ['logic', 'proofs with an untagged hole', 'every hole justified, untagged', 'every hole justified, no untagged',
                      'of those \\texttt{valid}', 'of those \\texttt{holey}', 're-check timeouts'], rows)

# ---------------------------------------------------------------- plots
plt.rcParams.update({'font.size': 9, 'axes.grid': True, 'grid.alpha': .3, 'legend.frameon': False})


def cdf(ax, v, **kw):
    v = np.sort(np.asarray(v))
    ax.step(v, np.arange(1, len(v) + 1) / len(v), where='post', **kw)


fig, ax = plt.subplots(figsize=(4.2, 2.8))
for l in LOGICS:
    hb = np.array([t['holes_before'] or 0 for t in by_logic[l]])
    cdf(ax, np.maximum(hb, 0.5), color=COLORS[l], label=l)
ax.set_xscale('log')
ax.set_xlabel('holes in the proof (after hoist + prune)')
ax.set_ylabel('fraction of proofs')
ax.legend(loc='lower right')
fig.tight_layout()
fig.savefig(f'{out}/plots/holes-per-proof.pdf')

fig, ax = plt.subplots(figsize=(4.2, 2.8))
for l in LOGICS:
    v = [t['solver_time'] for t in by_logic[l] if t['solver_time'] is not None]
    cdf(ax, np.maximum(v, 0.005), color=COLORS[l], label=f'{l} ({len(v)} proofs)')
ax.set_xscale('log')
ax.set_xlabel('cvc5 solve + proof time (s)')
ax.set_ylabel('fraction of proofs')
ax.legend(loc='lower right')
fig.tight_layout()
fig.savefig(f'{out}/plots/cvc5-time.pdf')

fig, axes = plt.subplots(1, 3, figsize=(8.4, 2.6), sharey=True)
for ax, l in zip(axes, LOGICS):
    allt = [rec[1] for rec in holes[l].values() if rec[0] == 'ok']
    egg = [rec[1] for k, rec in holes[l].items() if rec[0] == 'ok' and k in phases[l]]
    cdf(ax, np.maximum(allt, 1e-3), color=COLORS[l], label='all justified')
    cdf(ax, np.maximum(egg, 1e-3), color=COLORS[l], linestyle='--', label='through egglog')
    ax.set_xscale('log')
    ax.set_title(l)
    ax.set_xlabel('time per hole (s)')
axes[0].set_ylabel('fraction of justified holes')
axes[0].legend(loc='upper left')
fig.tight_layout()
fig.savefig(f'{out}/plots/hole-time-cdf.pdf')

# pass outcomes stacked bars: closed by normalizer / bridged / stated / kept / skipped
fig, ax = plt.subplots(figsize=(4.6, 2.8))
x = np.arange(len(LOGICS))
parts = collections.defaultdict(list)
for l in LOGICS:
    ts = ran[l]
    closed = sum(t['elab_closed'] or 0 for t in ts)
    bridged = sum(t['pre_bridged'] for t in ts)
    just = sum(t['holes_before'] - t['holes_after'] for t in ts)
    parts['closed by the normalizer'].append(closed / 1e6)
    parts['egglog on the normal form'].append(bridged / 1e6)
    parts['egglog on the stated goal'].append((just - closed - bridged) / 1e6)
    parts['kept'].append(sum(t['holes_kept'] or 0 for t in ts) / 1e6)
    parts['skipped (budget)'].append(sum(t['holes_skipped'] or 0 for t in ts) / 1e6)
bottom = np.zeros(len(LOGICS))
for name, col in zip(parts, ['#2a6f2a', '#4c9a2a', '#a8d08d', '#e07b39', '#bbbbbb']):
    v = np.array(parts[name])
    ax.bar(x, v, 0.55, bottom=bottom, color=col, label=name)
    bottom += v
ax.set_xticks(x)
ax.set_xticklabels(LOGICS)
ax.set_ylabel('holes (millions)')
ax.legend(loc='upper right', fontsize=7)
fig.tight_layout()
fig.savefig(f'{out}/plots/pass-outcome.pdf')

fig, ax = plt.subplots(figsize=(7.2, 2.2))
palette = ['#d62728', '#e377c2', '#ff7f0e', '#9467bd', '#17becf', '#8c564b', '#7f7f7f', '#bcbd22', '#000000']
y = np.arange(len(LOGICS))
left = np.zeros(len(LOGICS))
for why, col in zip(REASON_ORDER, palette):
    vals = np.array([reasons[(l, why)] for l in LOGICS]) / 1e3
    if vals.sum() == 0:
        continue
    ax.barh(y, vals, left=left, color=col, label=why)
    left += vals
ax.set_yticks(y)
ax.set_yticklabels(LOGICS)
ax.invert_yaxis()
ax.set_xlabel('kept holes (thousands)')
ax.legend(loc='center left', bbox_to_anchor=(1.0, 0.5), fontsize=7)
fig.tight_layout()
fig.savefig(f'{out}/plots/reasons.pdf')

fig, ax = plt.subplots(figsize=(4.6, 3.0))
for l in LOGICS:
    ts = [t for t in ran[l] if t['elab_time'] is not None]
    ax.scatter([max(t['holes_before'], 0.5) for t in ts], [max(t['elab_time'], 0.05) for t in ts],
               s=4, alpha=.35, color=COLORS[l], label=l, linewidths=0)
ax.axhline(ELAB_BUDGET, color='k', linestyle=':', linewidth=1)
ax.set_xscale('log')
ax.set_yscale('log')
ax.set_ylim(0.04, 2500)
ax.set_xlabel('holes in the proof')
ax.set_ylabel('elaboration pass wall time (s)')
ax.legend(loc='upper left', markerscale=3)
fig.tight_layout()
fig.savefig(f'{out}/plots/size-vs-time.pdf')

buckets = [(0, 100), (100, 1000), (1000, 10000), (10000, 10**9)]
blabels = ['$\\leq$100', '100--1k', '1k--10k', '$>$10k']
fig, axes = plt.subplots(1, 3, figsize=(8.4, 2.6), sharey=True)
for ax, l in zip(axes, LOGICS):
    just, kept, skip, n = [], [], [], []
    for lo, hi in buckets:
        cs = [t for t in ran[l] if lo < t['holes_before'] <= hi]
        h = sum(t['holes_before'] for t in cs)
        n.append(len(cs))
        if h == 0:
            just.append(0); kept.append(0); skip.append(0)
            continue
        just.append(sum(t['holes_before'] - t['holes_after'] for t in cs) / h)
        kept.append(sum(t['holes_kept'] or 0 for t in cs) / h)
        skip.append(sum(t['holes_skipped'] or 0 for t in cs) / h)
    xb = np.arange(len(buckets))
    just, kept, skip = np.array(just), np.array(kept), np.array(skip)
    ax.bar(xb, just, color='#4c9a2a', label='justified')
    ax.bar(xb, kept, bottom=just, color='#e07b39', label='kept')
    ax.bar(xb, skip, bottom=just + kept, color='#bbbbbb', label='skipped')
    for i, k in enumerate(n):
        ax.text(i, 1.02, str(k), ha='center', fontsize=7)
    ax.set_xticks(xb)
    ax.set_xticklabels(blabels, fontsize=7)
    ax.set_ylim(0, 1.08)
    ax.set_title(l)
    ax.set_xlabel('holes in the proof (proof count above)')
axes[0].set_ylabel('share of holes')
axes[0].legend(loc='lower left', fontsize=7)
fig.tight_layout()
fig.savefig(f'{out}/plots/outcome-by-size.pdf')

fig, ax = plt.subplots(figsize=(4.2, 2.8))
for l in LOGICS:
    v = [(t['holes_before'] - t['holes_after']) / t['holes_before'] for t in ran[l] if t['holes_before']]
    cdf(ax, v, color=COLORS[l], label=l)
ax.set_xlabel('fraction of the proof\'s holes justified')
ax.set_ylabel('fraction of proofs with holes')
ax.set_xlim(0.9, 1.001)
ax.legend(loc='upper left')
fig.tight_layout()
fig.savefig(f'{out}/plots/justified-per-proof.pdf')

fig, ax = plt.subplots(figsize=(4.2, 2.6))
ph_colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd']
bottom = np.zeros(len(LOGICS))
tot = np.array([sum(sum(p.values()) for p in phases[l].values()) for l in LOGICS])
for ph, col in zip(PHASES, ph_colors):
    v = np.array([sum(p.get(ph, 0.0) for p in phases[l].values()) for l in LOGICS])
    ax.bar(np.arange(len(LOGICS)), v / tot, bottom=bottom, color=col, label=ph)
    bottom += v / tot
ax.set_xticks(np.arange(len(LOGICS)))
ax.set_xticklabels(LOGICS)
ax.set_ylabel('share of the hole time through egglog')
ax.legend(loc='center left', bbox_to_anchor=(1.0, 0.5), fontsize=8)
fig.tight_layout()
fig.savefig(f'{out}/plots/phases.pdf')

fig, ax = plt.subplots(figsize=(4.2, 2.8))
for l in LOGICS:
    cdf(ax, np.maximum([t['mem_gb'] for t in by_logic[l]], 0.01), color=COLORS[l], label=l)
ax.set_xscale('log')
ax.set_xlabel('peak task memory (GB, 8 workers + parent)')
ax.set_ylabel('fraction of proofs')
ax.legend(loc='lower right')
fig.tight_layout()
fig.savefig(f'{out}/plots/memory.pdf')

# ---------------------------------------------------------------- macros
allran = [t for l in LOGICS for t in ran[l]]
nholes = sum(t['holes_before'] for t in allran)
njust = sum(t['holes_before'] - t['holes_after'] for t in allran)
nkept = sum(reasons.values())
nskipped = sum(t['holes_skipped'] or 0 for t in allran)
proved_lost = sum(v for (l, w), v in reasons.items() if w in PROVED_CLASSES)
egg_kills = sum(v for (l, w), v in reasons.items() if w in ('killed at the per-hole limit, inside egglog', 'killed at the 6 GB limit'))
with open(f'{out}/tables/macros.tex', 'w') as f:
    f.write(f'\\newcommand{{\\ntasks}}{{{len(tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nholes}}{{{nholes:,}}}\n')
    f.write(f'\\newcommand{{\\nholesteps}}{{{sum(t["holes_orig"] or 0 for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\njustshare}}{{{100 * njust / nholes:.1f}}}\n')
    f.write(f'\\newcommand{{\\nprovedshare}}{{{100 * (njust + proved_lost) / nholes:.1f}}}\n')
    f.write(f'\\newcommand{{\\nkept}}{{{nkept:,}}}\n')
    f.write(f'\\newcommand{{\\nskipped}}{{{nskipped:,}}}\n')
    f.write(f'\\newcommand{{\\nfully}}{{{sum(fully(t) for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nvalid}}{{{sum(t["check_result"] == "valid" for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nuntagged}}{{{sum(untagged(t) for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nfullyclean}}{{{sum(fully(t) and not untagged(t) for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nfullycleanholey}}{{{sum(fully(t) and not untagged(t) and t["check_result"] == "holey" for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\npivot}}{{{sum(t["hoist_pivot"] for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nhoistto}}{{{sum(t["hoist_rc"] == "124" for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\nrecheckto}}{{{sum(t["check_result"] == "timeout" for t in tasks):,}}}\n')
    f.write(f'\\newcommand{{\\eggshare}}{{{100 * egg_kills / nkept:.0f}}}\n')
    f.write(f'\\newcommand{{\\nclosednorm}}{{{sum(t["elab_closed"] or 0 for t in allran):,}}}\n')
    f.write(f'\\newcommand{{\\normshare}}{{{100 * sum(t["elab_closed"] or 0 for t in allran) / nholes:.1f}}}\n')
    f.write(f'\\newcommand{{\\passhours}}{{{sum(t["elab_time"] or 0 for t in tasks) / 3600:,.0f}}}\n')
    f.write(f'\\newcommand{{\\cpuhours}}{{{sum(t["wall"] for t in tasks) * 8 / 3600:,.0f}}}\n')
    f.write(f'\\newcommand{{\\wallhours}}{{{sum(t["wall"] for t in tasks) / 3600:,.0f}}}\n')
print('done:', len(tasks), 'tasks')
