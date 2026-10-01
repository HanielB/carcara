#!/usr/bin/env python3
"""Tables and plots of the rw5 cost report: the normalizer, the cost of a
hole, elaboration against checking, and cvc5's own expansion (dsl1).

Usage: make.py <rw5 results.json.gz> <dsl1 results.json.gz> [outdir]
Run with the analysis venv (~/cvc5/wt-diff/cluster/pyenv), which has
matplotlib.  Prints a plain-text summary of every number it writes.

What a hole costs is read off the elaboration pass's log, which has one line
per hole:
  `hole <id>: justified in <T>s (check <C>s)`   T: the hole's worker time,
      from the worker's start to its answer, every attempt included (the
      normalized goal, the goal as stated, the abstract goal, the descent's
      pairs, each in a process of its own); 0 for a hole the normalizer
      closed, which never reaches a worker.  C: the parent's insertion of
      the returned steps (parse and check), sequential.
  `hole <id>: phases egglog=.. serialize=.. index=.. search=.. emit=..`
      the phases each child process reported, one line per attempt:
      egglog is the saturation that decides the goal (what a checking-only
      pass runs), serialize/index/search/emit the reconstruction of the
      certificate from the saturated e-graph (what elaboration adds).
  `hole <id>: kept as trusted: [<class>] <reason>` for the others; a killed
      attempt's reason says `killed after <X>s`.
  `hole prenorm: ...` per proof: the holes the normalizer closed, the goals
      it rewrote, its time, and how many normalized goals were proved and
      bridged.
"""
import collections
import gzip
import json
import os
import re
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.lines
import matplotlib.ticker
import matplotlib.pyplot as plt
import numpy as np

rw5_path, dsl_path = sys.argv[1:3]
out = sys.argv[3] if len(sys.argv) > 3 else os.path.dirname(os.path.abspath(__file__))
os.makedirs(f'{out}/plots', exist_ok=True)
os.makedirs(f'{out}/tables', exist_ok=True)

LOGICS = ('QF_UF', 'QF_LIA', 'QF_LRA')
COLORS = {'QF_UF': '#1f77b4', 'QF_LIA': '#d62728', 'QF_LRA': '#2ca02c'}
WORKERS = 8
KEY = re.compile(r'^\[pfchk\] ([\w-]+)=(.*)$', re.M)
JUST = re.compile(r'^info: hole (\S+): justified in ([\d.]+)s \(check ([\d.]+)s\)$', re.M)
PHASE = re.compile(r'^info: hole (\S+): phases (.*)$', re.M)
KEPT = re.compile(r'hole (\S+): kept as trusted: \[([a-z-]+)\] ?(.*)$', re.M)
OPEN = re.compile(r'^info: hole (\S+): prenorm open, goal (rewritten|unchanged) \((\d+) nodes(?: to (\d+) nodes)?', re.M)
PRENORM = re.compile(r'hole prenorm: (\d+) of (\d+) holes closed by normalization, (\d+) goals rewritten, in ([\d.]+)s')
BRIDGE = re.compile(r'hole prenorm: (\d+) normalized goals tried, (\d+) proved and bridged, (\d+) of the (\d+) retried proved as stated')
ABSTRACT = re.compile(r'hole abstraction: (\d+) of (\d+) holes share a subterm of \d+ nodes or more; (\d+) proved abstract, (\d+) kept on the abstract attempt\'s time or memory, (\d+) of the (\d+) retried')
KILLED = re.compile(r'killed after ([\d.]+)s(?: during (\w+))?')
HOISTED = re.compile(r'hoisting: lifted (\d+) steps to depth 0, dropped (\d+) repeated derivations \((\d+) of them holey\)')
PRUNED = re.compile(r'prune: dropped (\d+) of (\d+) commands')
DURATION = re.compile(r'^(parsing|checking):\s+([\d.]+)(ns|µs|us|ms|s)\b', re.M)
RECON = ('serialize', 'index', 'search', 'emit')
UNIT = {'ns': 1e-9, 'µs': 1e-6, 'us': 1e-6, 'ms': 1e-3, 's': 1.0}


def F(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return 0.0


def I(x):
    try:
        return int(x)
    except (TypeError, ValueError):
        return 0


def section(log, name):
    """The text between `=== name ===` and the next `===` header."""
    i = log.find(f'=== {name} ===\n')
    if i < 0:
        return ''
    j = log.find('\n=== ', i + len(name) + 8)
    return log[i + len(name) + 8: j if j >= 0 else len(log)]


def rule_counts(text):
    counts = {}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[1].isdigit():
            counts[parts[0]] = int(parts[1])
    return counts


def check_stats(log):
    stats = {}
    for name, value, unit in DURATION.findall(section(log, 'carcara check stdout')):
        stats[name] = float(value) * UNIT[unit]
    return stats


MARKERS = ('whole-first', 'descent-failed', 'atoms-failed', 'descent', 'atoms')


def kept_bucket(cls, why, tokens):
    """Whether egglog proved a kept hole's goal: 'checked' (the
    reconstruction lost it), 'not checked', 'undetermined' (killed inside a
    descent, the whole goal not proved) or 'not attempted' -- the reading of
    notes 47.32 (analysis-rw5/questions.py).  `tokens` are the phase names of
    the hole's last phases line."""
    if cls in ('out-of-scope', 'pass-budget'):
        return 'not attempted'
    if cls == 'unproved':
        return 'not checked'
    if cls in ('no-certificate', 'checker-rejected'):
        return 'checked'
    m = re.search(r'during (\w+)', why)
    phase = m.group(1) if m else None
    after = re.search(r'\(after ([^)]*)\)', why)
    names = [t.split('=')[0] for t in after.group(1).split()] if after else tokens
    segs, cur = [], []
    for t in names:
        if t in MARKERS:
            segs.append((t, cur))
            cur = []
        else:
            cur.append(t)
    # a whole-goal attempt that reached serialize: egglog proved the goal
    whole_proved = any(marker == 'whole-first' and 'serialize' in seg for marker, seg in segs)
    last = segs[-1][0] if segs else None
    if whole_proved:
        return 'checked'
    if cls == 'memory':
        return 'not checked'
    if phase == 'egglog' and not (last == 'whole-first' and cur):
        return 'not checked'
    if phase in RECON:
        return 'undetermined' if last == 'whole-first' else 'checked'
    return 'undetermined'


def logic_of(name):
    return next((l for l in LOGICS if name.startswith(l + '/')), None)


def records(path):
    for line in gzip.open(path, 'rt'):
        if not line.strip():
            continue
        r = json.loads(line)
        if r.get('type') != 'task':
            continue
        yield r['job_args'].split('/non-incremental/', 1)[-1], r


def run_log(r):
    run = r.get('run_log', '') or ''
    m = re.search(r'^memory=(\d+)B', run, re.M)
    c = re.search(r'^cputime=([\d.]+)s', run, re.M)
    return (int(m.group(1)) / 2**30 if m else 0.0), (float(c.group(1)) if c else 0.0)


# ---------------------------------------------------------------- rw5, per proof and per hole
proofs = {}
# per logic: arrays of the justified egglog holes' times, the closed holes'
# insertion checks, the kept holes' times
H = {l: collections.defaultdict(list) for l in LOGICS}
C = {l: collections.Counter() for l in LOGICS}  # counters and sums per logic
kept_by = {l: collections.Counter() for l in LOGICS}
for name, r in records(rw5_path):
    l = logic_of(name)
    log = r.get('output_log', '') or ''
    k = dict(KEY.findall(log))
    mem, cpu = run_log(r)
    p = {'logic': l, 'family': name.split('/')[1], 'mem': mem, 'cpu': cpu}
    for key in ('solver_time', 'hoist_time', 'elab_time', 'elab_holes_time', 'check_time'):
        p[key] = F(k.get(key))
    for key in ('proof_bytes', 'holes_orig', 'holes_untagged', 'holes_before', 'holes_kept', 'holes_skipped',
                'elab_closed', 'elab_rewritten', 'elab_bridged'):
        p[key] = I(k.get(key))
    p['complete'] = k.get('proof_complete') == '1'
    p['hoist'] = k.get('hoist')
    hoist_log = section(log, 'carcara hoist stderr')
    p['pivot'] = p['hoist'] != 'ok' and 'pivot was not found' in hoist_log
    m = HOISTED.search(hoist_log)
    p['lifted'], p['dropped'], p['dropped_holey'] = (int(x) for x in m.groups()) if m else (0, 0, 0)
    m = PRUNED.search(hoist_log)
    p['pruned'], p['commands'] = (int(x) for x in m.groups()) if m else (0, 0)
    p['ran'] = k.get('holes_after') not in (None, 'none', '')
    p['okp'] = k.get('okp') == '1'
    p['fully'] = k.get('okp') == '1' and k.get('holes_after') == '0'
    p['result'] = k.get('check_result')
    p['hoisted_steps'] = sum(rule_counts(section(log, 'rule counts')).values())
    elaborated = rule_counts(section(log, 'elaborated rule counts'))
    p['elab_steps'] = sum(elaborated.values())
    p['elab_rare'] = elaborated.get('rare_rewrite', 0)
    stats = check_stats(log)
    p['check_parse'], p['check_check'] = stats.get('parsing', 0.0), stats.get('checking', 0.0)
    proofs[name] = p
    if not p['ran']:
        continue
    body = log.split('=== carcara elaborate stderr ===', 1)
    body = body[1].split('=== carcara check stdout ===', 1)[0] if len(body) > 1 else ''
    c = C[l]
    c['proofs'] += 1
    m = PRENORM.search(body)
    p['prenorm_s'] = float(m.group(4)) if m else 0.0
    c['prenorm_s'] += p['prenorm_s']
    m = BRIDGE.search(body)
    if m:
        c['tried'] += int(m.group(1)); c['bridged'] += int(m.group(2))
        c['retried'] += int(m.group(4)); c['retried_proved'] += int(m.group(3))
    m = ABSTRACT.search(body)
    if m:
        c['abstract_share'] += int(m.group(1)); c['abstract_proved'] += int(m.group(3))
        c['abstract_retried'] += int(m.group(6)); c['abstract_retried_proved'] += int(m.group(5))
    status = {}
    for h, kind, a, b in OPEN.findall(body):
        status[h] = kind
        if kind == 'rewritten':
            a, b = int(a), int(b)
            c['nf smaller' if b < a else 'nf larger' if b > a else 'nf same'] += 1
            c['goal nodes'] += a; c['nf nodes'] += b
    phases = collections.defaultdict(lambda: collections.Counter())
    attempts = collections.Counter()
    last_names = {}
    for h, rest in PHASE.findall(body):
        attempts[h] += 1
        last_names[h] = [t.split('=')[0] for t in rest.split()]
        for token in rest.split():
            key, _, value = token.partition('=')
            if key == 'egglog' or key in RECON:
                phases[h][key] += F(value)
    # every hole's reconstruction phases, kept holes' included: what a
    # checking-only pass would not run
    p['recon'] = sum(ph[x] for ph in phases.values() for x in RECON)
    insertion = 0.0
    for h, t, chk in JUST.findall(body):
        t, chk = float(t), float(chk)
        insertion += chk
        if h not in status:  # closed by the normalizer: no worker
            H[l]['closed_check'].append(chk)
            continue
        ph = phases.get(h, collections.Counter())
        egg = ph['egglog']
        rec = sum(ph[x] for x in RECON)
        H[l]['total'].append(t)
        H[l]['egglog'].append(egg)
        H[l]['recon'].append(rec)
        H[l]['check'].append(chk)
        H[l]['overhead'].append(max(t - egg - rec, 0.0))
        for x in RECON:
            c[f'sum {x}'] += ph[x]
        c['rewritten justified' if status[h] == 'rewritten' else 'unchanged justified'] += 1
        c['several attempts'] += attempts[h] > 1
    p['insertion'] = insertion
    p['unchecked'] = p['holes_skipped']
    for h, cls, why in KEPT.findall(body):
        if kept_bucket(cls, why, last_names.get(h, [])) != 'checked':
            p['unchecked'] += 1
        ph = phases.get(h, collections.Counter())
        spent = sum(ph.values())
        m = KILLED.search(why)
        if m:
            spent = max(spent, float(m.group(1)))
        H[l]['kept'].append(spent)
        kept_by[l][cls] += 1
        kept_by[l][f'{cls} ' + status.get(h, 'closed?')] += 1
        # lost by the reconstruction: killed in one of its phases, or no
        # certificate, or the certificate rejected
        if (m and m.group(2) in RECON) or cls in ('no-certificate', 'checker-rejected'):
            c['recon lost'] += 1
            c['recon lost s'] += spent
    c['holes'] += p['holes_before']
    c['skipped'] += p['holes_skipped']
    c['closed'] += p['elab_closed']
    c['rewritten'] += p['elab_rewritten']
    c['prepass_s'] += p['elab_holes_time']
    c['elab_s'] += p['elab_time']
    c['insertion_s'] += insertion

# ---------------------------------------------------------------- dsl1
dsl = {}
for name, r in records(dsl_path):
    log = r.get('output_log', '') or ''
    k = dict(KEY.findall(log))
    stats = check_stats(log)
    dsl[name] = {'logic': logic_of(name), 'solver_time': F(k.get('solver_time')), 'check_time': F(k.get('check_time')),
                 'proof_bytes': I(k.get('proof_bytes')), 'steps': I(k.get('proof_steps')),
                 'rare': I(k.get('rare_rewrite_steps')), 'complete': k.get('proof_complete') == '1',
                 'result': k.get('check_result'), 'check_parse': stats.get('parsing', 0.0),
                 'check_check': stats.get('checking', 0.0)}


# ---------------------------------------------------------------- helpers
def fmt(n, d=1):
    if isinstance(n, float):
        return f'{n:,.{d}f}'
    return f'{n:,}'


def pct(a, b, d=1):
    return f'{100 * a / b:.{d}f}' if b else '--'


def q(v, p):
    if len(v) == 0:
        return float('nan')
    return float(np.quantile(np.asarray(v), p))


def secs(x):
    """A time for a table cell: ms below a second."""
    if x != x:
        return '--'
    if x < 0.01:
        return f'{1000 * x:.1f}\\,ms'
    if x < 1:
        return f'{1000 * x:.0f}\\,ms'
    return f'{x:.1f}\\,s'


def L(l):
    return '\\' + {'QF_UF': 'UF', 'QF_LIA': 'LIA', 'QF_LRA': 'LRA'}[l] + '{}'


def write_table(name, header, rows, align=None):
    align = align or ('l' + 'r' * (len(header) - 1))
    with open(f'{out}/tables/{name}.tex', 'w') as f:
        f.write('\\begin{tabular}{' + align + '}\n\\toprule\n')
        f.write(' & '.join(header) + ' \\\\\n\\midrule\n')
        for row in rows:
            if row == 'midrule':
                f.write('\\midrule\n')
                continue
            f.write(' & '.join(str(x) for x in row) + ' \\\\\n')
        f.write('\\bottomrule\n\\end{tabular}\n')


hours = lambda s: f'{s / 3600:,.1f}'
report = []
say = report.append

# ---------------------------------------------------------------- pass 0: hoist and prune
rows = []
cols = {l: [p for p in proofs.values() if p['logic'] == l and p['complete']] for l in LOGICS}
allc = [p for p in proofs.values() if p['complete']]
def hoist_row(label, f):
    return [label] + [f(cols[l]) for l in LOGICS] + [f(allc)]
hoisted = lambda ps: [p for p in ps if p['hoist'] == 'ok']
rows.append(hoist_row('proofs (complete in 60\\,s)', lambda ps: fmt(len(ps))))
rows.append(hoist_row('\\quad hoisted', lambda ps: fmt(len(hoisted(ps)))))
rows.append(hoist_row('\\quad rejected upfront (cvc5\'s resolution pivots)', lambda ps: fmt(sum(p['pivot'] for p in ps))))
rows.append(hoist_row('\\quad hoist out of time (300\\,s)', lambda ps: fmt(sum(p['hoist'] != 'ok' and not p['pivot'] for p in ps))))
rows.append('midrule')
rows.append(hoist_row('hoisted proofs: hole steps printed by cvc5', lambda ps: fmt(sum(p['holes_orig'] for p in hoisted(ps)))))
rows.append(hoist_row('\\quad distinct holes after hoist and prune', lambda ps: fmt(sum(p['holes_before'] for p in hoisted(ps)))))
rows.append(hoist_row('\\quad ratio', lambda ps: f"{sum(p['holes_orig'] for p in hoisted(ps)) / max(1, sum(p['holes_before'] for p in hoisted(ps))):.2f}"))
rows.append(hoist_row('\\quad proofs with fewer holes after it', lambda ps: fmt(sum(p['holes_before'] < p['holes_orig'] for p in hoisted(ps)))))
rows.append(hoist_row('\\quad commands pruned, of all', lambda ps: f"{pct(sum(p['pruned'] for p in hoisted(ps)), sum(p['commands'] for p in hoisted(ps)))}\\%"))
rows.append(hoist_row('\\quad time, median / max', lambda ps: f"{secs(q([p['hoist_time'] for p in hoisted(ps)], .5))} / {secs(max(p['hoist_time'] for p in hoisted(ps)))}"))
rows.append(hoist_row('\\quad time, summed (h)', lambda ps: hours(sum(p['hoist_time'] for p in ps))))
write_table('hoist', ['', L('QF_UF'), L('QF_LIA'), L('QF_LRA'), 'all'], rows)
say('hoist: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows if r != 'midrule'))

# ---------------------------------------------------------------- 1. the normalizer
rows = []
tot = collections.Counter()
for l in LOGICS:
    for key, v in C[l].items():
        tot[key] += v
def nrow(label, f):
    return [label] + [f(C[l]) for l in LOGICS] + [f(tot)]
attempted = lambda c: c['holes']
rows.append(nrow('holes (proofs whose pass finished)', lambda c: fmt(attempted(c))))
rows.append(nrow('closed by the normalizer', lambda c: f"{fmt(c['closed'])} ({pct(c['closed'], attempted(c))}\\%)"))
rows.append(nrow('normal form tried first', lambda c: f"{fmt(c['tried'])} ({pct(c['tried'], attempted(c))}\\%)"))
rows.append(nrow('\\quad proved and bridged', lambda c: f"{fmt(c['bridged'])} ({pct(c['bridged'], c['tried'], 2)}\\%)"))
rows.append(nrow('\\quad not, retried as stated: proved', lambda c: f"{fmt(c['retried_proved'])} of {fmt(c['retried'])}"))
rows.append(nrow('\\quad normal form smaller / same / larger (\\%)',
                 lambda c: f"{pct(c['nf smaller'], c['tried'], 0)} / {pct(c['nf same'], c['tried'], 0)} / {pct(c['nf larger'], c['tried'], 0)}"))
rows.append(nrow('goal unchanged by the normalizer',
                 lambda c: f"{fmt(attempted(c) - c['closed'] - c['tried'])} ({pct(attempted(c) - c['closed'] - c['tried'], attempted(c))}\\%)"))
rows.append('midrule')
rows.append(nrow('normalization and closing certificates (s)', lambda c: fmt(c['prenorm_s'])))
closed_check = {l: sum(H[l]['closed_check']) for l in LOGICS}
rows.append(['inserting the closed holes\' certificates (s)'] + [fmt(closed_check[l]) for l in LOGICS] + [fmt(sum(closed_check.values()))])
eg_hours = {l: sum(H[l]['total']) for l in LOGICS}
rows.append(['worker time of the other justified holes (h)'] + [hours(eg_hours[l]) for l in LOGICS] + [hours(sum(eg_hours.values()))])
write_table('normalizer', ['', L('QF_UF'), L('QF_LIA'), L('QF_LRA'), 'all'], rows)
say('normalizer: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows if r != 'midrule'))
kept_status = {l: {s: sum(n for key, n in kept_by[l].items() if key.endswith(' ' + s)) for s in ('rewritten', 'unchanged', 'closed?')} for l in LOGICS}
say(f'kept holes by the normalizer\'s outcome: {kept_status}')
say(f"abstraction: {[(l, C[l]['abstract_share'], C[l]['abstract_proved'], C[l]['abstract_retried'], C[l]['abstract_retried_proved']) for l in LOGICS]}")
say(f"justified egglog holes, rewritten / unchanged: {[(l, C[l]['rewritten justified'], C[l]['unchanged justified']) for l in LOGICS]}")
say(f"nodes: goal {tot['goal nodes']} nf {tot['nf nodes']}")

# ---------------------------------------------------------------- 2. cost per hole
rows = []
def dist(v):
    return [secs(q(v, .5)), secs(q(v, .9)), secs(q(v, .99)), secs(max(v) if v else float('nan'))]
for l in LOGICS:
    h = H[l]
    n_closed = len(h['closed_check'])
    closed_cost = [C[l]['prenorm_s'] / max(1, n_closed) + x for x in h['closed_check']]
    n_all = n_closed + len(h['total']) + len(h['kept'])
    for label, v in (('closed by the normalizer', closed_cost), ('justified through egglog', h['total']), ('kept', h['kept']),
                     ('all', closed_cost + h['total'] + h['kept'])):
        rows.append([L(l) if label.startswith('closed') else '', label, fmt(len(v)), pct(len(v), n_all, 2), secs(np.mean(v))]
                    + dist(v) + [hours(sum(v))])
    rows.append('midrule')
rows.pop()
write_table('cost', ['', 'holes', 'number', '\\%', 'mean', 'median', 'p90', 'p99', 'max', 'hours'], rows, align='llrrrrrrrr')
say('cost: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows if r != 'midrule'))

# per proof: the pass's parts, and the workers' utilization
rows = []
ran = {l: [p for p in proofs.values() if p['logic'] == l and p['ran']] for l in LOGICS}
allran = [p for l in LOGICS for p in ran[l]]
def prow(label, f):
    return [label] + [f(ran[l], l) for l in LOGICS] + [f(allran, None)]
worker = {l: sum(H[l]['total']) + sum(H[l]['kept']) for l in LOGICS}
rows.append(prow('proofs whose pass finished', lambda ps, l: fmt(len(ps))))
rows.append(prow('elaboration pass (h)', lambda ps, l: hours(sum(p['elab_time'] for p in ps))))
rows.append(prow('\\quad normalizer', lambda ps, l: hours(sum(p.get('prenorm_s', 0) for p in ps))))
rows.append(prow('\\quad holes in the workers', lambda ps, l: hours(sum(p['elab_holes_time'] - p.get('prenorm_s', 0) for p in ps))))
rows.append(prow('\\quad inserting and checking the certificates', lambda ps, l: hours(sum(p['insertion'] for p in ps))))
rows.append(prow('\\quad the rest: parsing, the other steps, printing',
                 lambda ps, l: hours(sum(p['elab_time'] - p['elab_holes_time'] - p['insertion'] for p in ps))))
rows.append(prow('worker time (h)', lambda ps, l: hours(worker[l] if l else sum(worker.values()))))
rows.append(prow('\\quad utilization of the 8 workers (\\%)', lambda ps, l: pct(worker[l] if l else sum(worker.values()),
                                                                               WORKERS * sum(p['elab_holes_time'] - p.get('prenorm_s', 0) for p in ps))))
rows.append(prow('pass time per proof, median / p90', lambda ps, l: f"{secs(q([p['elab_time'] for p in ps], .5))} / {secs(q([p['elab_time'] for p in ps], .9))}"))
rows.append(prow('task memory, p99 / max (GB)', lambda ps, l: f"{q([p['mem'] for p in ps], .99):.1f} / {max(p['mem'] for p in ps):.1f}"))
pass_rows = rows
say('pass: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows))

# ---------------------------------------------------------------- 4. elaboration against checking, per hole
rows = []
def comp(l):
    h = H[l]
    return {'egglog': sum(h['egglog']), 'recon': sum(h['recon']), 'check': sum(h['check']), 'overhead': sum(h['overhead']),
            **{x: C[l][f'sum {x}'] for x in RECON}}
comps = {l: comp(l) for l in LOGICS}
allcomp = {key: sum(comps[l][key] for l in LOGICS) for key in comps['QF_UF']}
def share(d, key):
    total = d['egglog'] + d['recon'] + d['check'] + d['overhead']
    return f"{hours(d[key])} ({pct(d[key], total, 0)}\\%)"
for key, label in (('egglog', 'egglog: saturation, the goal decided'), ('recon', 'reconstruction'),
                   ('serialize', '\\quad serializing the e-graph'), ('index', '\\quad indexing it'),
                   ('search', '\\quad searching for the certificate'), ('emit', '\\quad emitting the steps'),
                   ('check', 'inserting and checking the steps'), ('overhead', 'process start and input parsing')):
    rows.append([label] + [share(comps[l], key) for l in LOGICS] + [share(allcomp, key)])
rows.append('midrule')
ratio = {l: np.asarray(H[l]['recon']) + np.asarray(H[l]['check']) for l in LOGICS}
egg = {l: np.asarray(H[l]['egglog']) for l in LOGICS}
rows.append(['per hole, median: egglog / elaboration'] + [f"{secs(np.median(egg[l]))} / {secs(np.median(ratio[l]))}" for l in LOGICS]
            + [f"{secs(np.median(np.concatenate([egg[l] for l in LOGICS])))} / {secs(np.median(np.concatenate([ratio[l] for l in LOGICS])))}"])
def over(l_list):
    e = np.concatenate([egg[l] for l in l_list]); r = np.concatenate([ratio[l] for l in l_list])
    return pct(np.sum(r > e), len(e), 1)
rows.append(['holes whose elaboration costs more than egglog (\\%)'] + [over([l]) for l in LOGICS] + [over(LOGICS)])
rows.append('midrule')
lost = lambda c: f"{fmt(c['recon lost'])}, {hours(c['recon lost s'])}\\,h"
rows.append(['kept after egglog proved the goal: holes, worker time'] + [lost(C[l]) for l in LOGICS] + [lost(tot)])
write_table('phases', ['justified holes through egglog, hours', L('QF_UF'), L('QF_LIA'), L('QF_LRA'), 'all'], rows)
say('phases: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows if r != 'midrule'))
ovh = np.concatenate([np.asarray(H[l]['overhead']) for l in LOGICS])
say(f"process start and parse per hole: median {np.median(ovh):.3f} s, p90 {q(ovh, .9):.3f} s, p99 {q(ovh, .99):.3f} s")
say(f"justified holes with more than one attempt line: {[(l, C[l]['several attempts']) for l in LOGICS]}")


# per proof, the checking-only estimate
def checking_only(p):
    """The pass without the reconstruction: the reconstruction phases of the
    proof's holes divided over the workers, and the insertions."""
    return max(p['elab_time'] - p['recon'] / WORKERS - p['insertion'], 0.0)


rows = pass_rows[:6]
rows.append(prow('checking-only pass, estimated (h)', lambda ps, l: hours(sum(checking_only(p) for p in ps))))
rows.append(prow('\\quad elaboration\'s share of the pass (\\%)', lambda ps, l: pct(sum(p['elab_time'] - checking_only(p) for p in ps), sum(p['elab_time'] for p in ps))))
rows += pass_rows[6:]
fullyv = {l: [p for p in ran[l] if p['result'] in ('valid', 'holey') and p['fully']] for l in LOGICS}
allf = [p for l in LOGICS for p in fullyv[l]]
def frow(label, f):
    return [label] + [f(fullyv[l]) for l in LOGICS] + [f(allf)]
rows.append('midrule')
rows.append(frow('proofs with every hole justified, re-checked', lambda ps: fmt(len(ps))))
rows.append(frow('\\quad elaboration pass, median / sum', lambda ps: f"{secs(q([p['elab_time'] for p in ps], .5))} / {hours(sum(p['elab_time'] for p in ps))}\\,h"))
rows.append(frow('\\quad re-check of the elaborated proof, median / sum', lambda ps: f"{secs(q([p['check_time'] for p in ps], .5))} / {hours(sum(p['check_time'] for p in ps))}\\,h"))
rows.append(frow('\\quad steps: hoisted proof / elaborated, median', lambda ps: f"{q([p['hoisted_steps'] for p in ps], .5):,.0f} / {q([p['elab_steps'] for p in ps], .5):,.0f}"))
write_table('perproof', ['', L('QF_UF'), L('QF_LIA'), L('QF_LRA'), 'all'], rows)
say('perproof: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows if r != 'midrule'))

# ---------------------------------------------------------------- 3. cvc5's own expansion
rows = []
common = {l: sorted(x for x in dsl if dsl[x]['logic'] == l and x in proofs) for l in LOGICS}
allcommon = [x for l in LOGICS for x in common[l]]
def crow(label, f):
    return [label] + [f(common[l]) for l in LOGICS] + [f(allcommon)]
rv = lambda xs: {x for x in xs if proofs[x]['result'] == 'valid'}
dv = lambda xs: {x for x in xs if dsl[x]['result'] == 'valid'}
both = lambda xs: sorted(rv(xs) & dv(xs))
rows.append(crow('benchmarks', lambda xs: fmt(len(xs))))
rows.append(crow('complete proof in 60\\,s: rewrite / dsl-rewrite',
                 lambda xs: f"{fmt(sum(proofs[x]['complete'] for x in xs))} / {fmt(sum(dsl[x]['complete'] for x in xs))}"))
bothc = lambda xs: [x for x in xs if proofs[x]['complete'] and dsl[x]['complete']]
rows.append(crow('cvc5 time, median: rewrite / dsl-rewrite',
                 lambda xs: f"{secs(q([proofs[x]['solver_time'] for x in bothc(xs)], .5))} / {secs(q([dsl[x]['solver_time'] for x in bothc(xs)], .5))}"))
rows.append(crow('cvc5 time, summed (h): rewrite / dsl-rewrite',
                 lambda xs: f"{hours(sum(proofs[x]['solver_time'] for x in bothc(xs)))} / {hours(sum(dsl[x]['solver_time'] for x in bothc(xs)))}"))
rows.append(crow('proof text (GB): rewrite / dsl-rewrite',
                 lambda xs: f"{sum(proofs[x]['proof_bytes'] for x in bothc(xs)) / 1e9:.1f} / {sum(dsl[x]['proof_bytes'] for x in bothc(xs)) / 1e9:.1f}"))
rows.append('midrule')
rows.append(crow('re-checked \\code{valid}: rw5 / dsl1', lambda xs: f"{fmt(len(rv(xs)))} / {fmt(len(dv(xs)))}"))
rows.append(crow('\\quad both / rw5 only / dsl1 only', lambda xs: f"{fmt(len(both(xs)))} / {fmt(len(rv(xs) - dv(xs)))} / {fmt(len(dv(xs) - rv(xs)))}"))
pipe = lambda x: proofs[x]['solver_time'] + proofs[x]['hoist_time'] + proofs[x]['elab_time'] + proofs[x]['check_time']
dslt = lambda x: dsl[x]['solver_time'] + dsl[x]['check_time']
# The three routes to a proof checked in full, per benchmark: (done, seconds).
#   cvc5-dsl + check: cvc5 at dsl-rewrite and carcara check, re-checked valid;
#   cvc5-rw + check: cvc5 at rewrite, hoist, and a checking-only pass (the
#     estimate from the elaboration pass), every hole checked -- justified,
#     or proved by egglog and lost in the reconstruction -- and no untagged
#     hole left;
#   cvc5-rw + check + elab: cvc5 at rewrite, hoist, the elaboration pass and
#     the re-check, re-checked valid.
def route_dsl(x):
    return dsl[x]['result'] == 'valid', dslt(x)


def route_check(x):
    p = proofs[x]
    done = p['ran'] and p['okp'] and p.get('unchecked', 1) == 0 and p['holes_untagged'] == 0
    return done, p['solver_time'] + p['hoist_time'] + (checking_only(p) if p['ran'] else 0.0)


def route_elab(x):
    return proofs[x]['result'] == 'valid', pipe(x)


ROUTES = (('cvc5-dsl + check', route_dsl, 'black', '-'),
          ('cvc5-rw + check', route_check, '#ff7f0e', '--'),
          ('cvc5-rw + check + elab', route_elab, '#9467bd', '-.'))
rows.append(crow('checked in full: cvc5-dsl + check / cvc5-rw + check / + elab',
                 lambda xs: ' / '.join(fmt(sum(f(x)[0] for x in xs)) for _, f, _, _ in ROUTES)))
rows.append(crow('valid in both, time to a checked proof, median: rw5 / dsl1',
                 lambda xs: f"{secs(q([pipe(x) for x in both(xs)], .5))} / {secs(q([dslt(x) for x in both(xs)], .5))}"))
rows.append(crow('\\quad summed (h): rw5 / dsl1', lambda xs: f"{hours(sum(pipe(x) for x in both(xs)))} / {hours(sum(dslt(x) for x in both(xs)))}"))
rows.append(crow('\\quad final proof\'s check, median: rw5 / dsl1',
                 lambda xs: f"{secs(q([proofs[x]['check_time'] for x in both(xs)], .5))} / {secs(q([dsl[x]['check_time'] for x in both(xs)], .5))}"))
rows.append(crow('\\quad final proof\'s check, summed (h): rw5 / dsl1',
                 lambda xs: f"{hours(sum(proofs[x]['check_time'] for x in both(xs)))} / {hours(sum(dsl[x]['check_time'] for x in both(xs)))}"))
rows.append(crow('\\quad steps, median: rw5 elaborated / dsl1',
                 lambda xs: f"{q([proofs[x]['elab_steps'] for x in both(xs)], .5):,.0f} / {q([dsl[x]['steps'] for x in both(xs)], .5):,.0f}"))
rows.append(crow('\\quad steps, summed (M): rw5 elaborated / dsl1',
                 lambda xs: f"{sum(proofs[x]['elab_steps'] for x in both(xs)) / 1e6:.1f} / {sum(dsl[x]['steps'] for x in both(xs)) / 1e6:.1f}"))
rows.append(crow('\\quad \\code{rare\\_rewrite} steps, summed (M): rw5 / dsl1',
                 lambda xs: f"{sum(proofs[x]['elab_rare'] for x in both(xs)) / 1e6:.2f} / {sum(dsl[x]['rare'] for x in both(xs)) / 1e6:.2f}"))
write_table('cvc5', ['', L('QF_UF'), L('QF_LIA'), L('QF_LRA'), 'all'], rows)
say('cvc5: ' + ' | '.join(' '.join(str(x) for x in r) for r in rows if r != 'midrule'))

# why dsl1-only
why = collections.Counter()
for x in allcommon:
    if dsl[x]['result'] == 'valid' and proofs[x]['result'] != 'valid':
        p = proofs[x]
        if not p['complete']:
            why['rw5: no complete proof'] += 1
        elif not p['ran']:
            why['rw5: pass did not finish'] += 1
        elif p['holes_kept'] or p['holes_skipped']:
            why['rw5: a hole kept or skipped'] += 1
        elif p['holes_untagged']:
            why['rw5: untagged hole left'] += 1
        else:
            why[f"rw5: other ({p['result']})"] += 1
say(f'dsl1 only, why: {dict(why)}')

# ---------------------------------------------------------------- plots
plt.rcParams.update({'font.size': 9, 'axes.grid': True, 'grid.alpha': .3, 'legend.frameon': False})
fig, axes = plt.subplots(1, 3, figsize=(8.6, 2.7), sharey=True)
for ax, l in zip(axes, LOGICS):
    h = H[l]
    n = len(h['total'])
    for v, label, ls in ((h['total'], 'worker time', '-'), (h['egglog'], 'egglog (checking)', '--'),
                         (np.asarray(h['recon']) + np.asarray(h['check']), 'reconstruction + insertion', ':')):
        v = np.sort(np.maximum(np.asarray(v), 1e-3))
        ax.step(v, np.arange(1, n + 1) / n, where='post', linestyle=ls, color=COLORS[l], label=label)
    ax.set_xscale('log')
    ax.set_xlim(1e-2, 100)
    ax.set_title(f'{l} ({n:,} holes)')
    ax.set_xlabel('seconds per hole')
axes[0].set_ylabel('fraction of the holes')
handles, labels = axes[0].get_legend_handles_labels()
fig.legend([matplotlib.lines.Line2D([], [], color='black', linestyle=h.get_linestyle()) for h in handles], labels,
           loc='lower center', ncol=3, fontsize=8)
fig.tight_layout(rect=(0, 0.08, 1, 1))
fig.savefig(f'{out}/plots/hole-cost.pdf')

XMAX = 5000.0


def route_lines(path, counts):
    """Figure 2: the three routes, the y axis the fraction of the benchmarks
    or, with `counts`, their number (each panel up to its logic's total)."""
    fig, axes = plt.subplots(1, 3, figsize=(8.6, 3.0), sharey=not counts)
    for ax, l in zip(axes, LOGICS):
        xs = common[l]
        n = len(xs)
        for label, route, color, ls in ROUTES:
            v = np.sort([max(t, 0.01) for done, t in map(route, xs) if done])
            y = np.arange(1, len(v) + 1) / (1 if counts else n)
            # the plateau to the right edge: how many benchmarks the route finishes
            ax.step(np.append(v, XMAX), np.append(y, y[-1]), where='post', linestyle=ls, color=color, label=label)
        ax.set_xscale('log')
        ax.set_xlim(0.01, XMAX)
        ax.set_ylim(0, n if counts else 1)
        if counts:
            ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f'{v:,.0f}'))
        ax.set_title(f'{l} ({n:,} benchmarks)')
        ax.set_xlabel('time to a proof checked in full (s)')
    axes[0].set_ylabel('benchmarks checked in full' if counts else 'fraction of the benchmarks')
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='lower center', ncol=3, fontsize=8)
    fig.tight_layout(rect=(0, 0.09, 1, 1))
    fig.savefig(path)


route_lines(f'{out}/plots/vs-cvc5.pdf', counts=False)
route_lines(f'{out}/plots/vs-cvc5-count.pdf', counts=True)

# Figure 3: per benchmark.  (a), (b): cvc5-dsl + check against the two
# rewrite-granularity routes, every benchmark; one a route does not finish
# sits on the edge.  (c), (d): the final proofs of the benchmarks valid in
# both, their check time and their size.
EDGE = 5000.0
fig, axes = plt.subplots(2, 2, figsize=(8.0, 7.6))
panels = (
    (axes[0][0], '(a) with elaboration', route_elab, 'cvc5-rw + check + elab (s)'),
    (axes[0][1], '(b) checking only (estimated)', route_check, 'cvc5-rw + check (s)'),
)
quadrants = {}
for ax, title, route, ylabel in panels:
    counts = collections.Counter()
    for l in LOGICS:
        xs = common[l]
        xv, yv = [], []
        for x in xs:
            dd, dt = route_dsl(x)
            rd, rt = route(x)
            xv.append(max(dt, 0.05) if dd else EDGE)
            yv.append(max(rt, 0.05) if rd else EDGE)
            counts['both' if dd and rd else 'cvc5-dsl only' if dd else 'rewrite route only' if rd else 'neither'] += 1
            if dd and rd:
                counts['rewrite route faster'] += rt < dt
        ax.scatter(xv, yv, s=4, alpha=.35, color=COLORS[l], label=l, linewidths=0)
    quadrants[title] = counts
    ax.plot([0.05, EDGE], [0.05, EDGE], color='k', linewidth=.8, linestyle=':')
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlim(0.04, EDGE * 1.4); ax.set_ylim(0.04, EDGE * 1.4)
    ax.set_title(title, fontsize=9)
    ax.set_xlabel('cvc5-dsl + check (s)')
    ax.set_ylabel(ylabel)
    ax.legend(loc='lower right', markerscale=3, fontsize=7)
finals = {}
for ax, title, fx, fy, xlabel, ylabel, floor in (
        (axes[1][0], '(c) checking the final proof, valid in both', lambda x: dsl[x]['check_time'],
         lambda x: proofs[x]['check_time'], 'check of the cvc5-dsl proof (s)', 'check of the elaborated proof (s)', 0.005),
        (axes[1][1], '(d) size of the final proof, valid in both', lambda x: dsl[x]['steps'],
         lambda x: proofs[x]['elab_steps'], 'steps of the cvc5-dsl proof', 'steps of the elaborated proof', 1)):
    xs_all, ys_all = [], []
    for l in LOGICS:
        xs = both(common[l])
        xv = [max(fx(x), floor) for x in xs]
        yv = [max(fy(x), floor) for x in xs]
        xs_all += xv; ys_all += yv
        ax.scatter(xv, yv, s=4, alpha=.35, color=COLORS[l], label=l, linewidths=0)
    lo = min(xs_all + ys_all) / 1.5; hi = max(xs_all + ys_all) * 1.5
    ax.plot([lo, hi], [lo, hi], color='k', linewidth=.8, linestyle=':')
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlim(lo, hi); ax.set_ylim(lo, hi)
    ax.set_title(title, fontsize=9)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.legend(loc='lower right', markerscale=3, fontsize=7)
    ratio = np.asarray(ys_all) / np.asarray(xs_all)
    finals[title] = (len(ratio), int(np.sum(ratio < 1)), float(np.median(ratio)), float(q(ratio, .1)), float(q(ratio, .9)))
fig.tight_layout()
fig.savefig(f'{out}/plots/vs-cvc5-scatter.pdf')
for title, counts in quadrants.items():
    say(f'scatter {title}: {dict(counts)}')
for title, (n, below, med, p10, p90) in finals.items():
    say(f'scatter {title}: {n} proofs, elaborated below cvc5-dsl on {below}, ratio median {med:.2f} (p10 {p10:.2f}, p90 {p90:.2f})')

# ---------------------------------------------------------------- macros
with open(f'{out}/tables/macros.tex', 'w') as f:
    def m(name, value):
        f.write(f'\\newcommand{{\\{name}}}{{{value}}}\n')
    m('nbench', fmt(len(proofs)))
    m('ncomplete', fmt(sum(p['complete'] for p in proofs.values())))
    m('nran', fmt(len(allran)))
    m('nholes', fmt(tot['holes']))
    m('nattempted', fmt(attempted(tot)))
    m('nclosed', fmt(tot['closed']))
    m('closedshare', pct(tot['closed'], attempted(tot)))
    m('ntried', fmt(tot['tried']))
    m('triedshare', pct(tot['tried'], attempted(tot)))
    m('bridgedshare', pct(tot['bridged'], tot['tried'], 2))
    m('nkept', fmt(sum(len(H[l]['kept']) for l in LOGICS)))
    m('workerhours', hours(sum(worker.values())))
    m('passhours', hours(sum(p['elab_time'] for p in allran)))
    m('checkonlyhours', hours(sum(checking_only(p) for p in allran)))
    m('egglogshare', pct(allcomp['egglog'], allcomp['egglog'] + allcomp['recon'] + allcomp['check'] + allcomp['overhead'], 0))
    m('reconshare', pct(allcomp['recon'] + allcomp['check'], allcomp['egglog'] + allcomp['recon'] + allcomp['check'] + allcomp['overhead'], 0))
    m('rwvalid', fmt(len(rv(allcommon))))
    m('dslvalid', fmt(len(dv(allcommon))))
    m('nboth', fmt(len(both(allcommon))))
    m('dslonly', fmt(len(dv(allcommon) - rv(allcommon))))
    m('rwonly', fmt(len(rv(allcommon) - dv(allcommon))))
    m('checkfull', fmt(sum(route_check(x)[0] for x in allcommon)))
    qa = quadrants['(a) with elaboration']; qb = quadrants['(b) checking only (estimated)']
    m('elabfaster', fmt(qa['rewrite route faster']))
    m('checkboth', fmt(qb['both']))
    m('checkfaster', fmt(qb['rewrite route faster']))
    m('checkonly', fmt(qb['rewrite route only']))
    m('checkdslonly', fmt(qb['cvc5-dsl only']))
    fc = finals['(c) checking the final proof, valid in both']; fd = finals['(d) size of the final proof, valid in both']
    m('checkratio', f'{fc[2]:.2f}')
    m('checkbelow', fmt(fc[1]))
    m('stepsratio', f'{fd[2]:.2f}')
    m('stepsbelow', fmt(fd[1]))

with open(f'{out}/summary.txt', 'w') as f:
    f.write('\n'.join(report) + '\n')
print('\n'.join(report))
