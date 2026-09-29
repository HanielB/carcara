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
    for h, rest in PHASE.findall(body):
        attempts[h] += 1
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
    for h, cls, why in KEPT.findall(body):
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

fig, axes = plt.subplots(1, 3, figsize=(8.6, 3.0), sharey=True)
for ax, l in zip(axes, LOGICS):
    xs = both(common[l])
    n = len(xs)
    for label, v, ls in (('cvc5 at dsl-rewrite + check (dsl1)', [dslt(x) for x in xs], '-'),
                         ('cvc5 at rewrite + hoist + elaboration + re-check (rw5)', [pipe(x) for x in xs], '--'),
                         ('cvc5 at rewrite + hoist + checking only (rw5, estimated)',
                          [proofs[x]['solver_time'] + proofs[x]['hoist_time'] + checking_only(proofs[x]) for x in xs], ':')):
        v = np.sort(np.maximum(np.asarray(v), 0.01))
        ax.step(v, np.arange(1, n + 1) / n, where='post', linestyle=ls, color=COLORS[l], label=label)
    ax.set_xscale('log')
    ax.set_xlim(0.01, 2000)
    ax.set_title(f'{l} ({n:,} valid in both)')
    ax.set_xlabel('seconds per benchmark')
axes[0].set_ylabel('fraction of the benchmarks')
handles, labels = axes[0].get_legend_handles_labels()
fig.legend([matplotlib.lines.Line2D([], [], color='black', linestyle=h.get_linestyle()) for h in handles], labels,
           loc='lower center', ncol=2, fontsize=8)
fig.tight_layout(rect=(0, 0.14, 1, 1))
fig.savefig(f'{out}/plots/vs-cvc5.pdf')

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

with open(f'{out}/summary.txt', 'w') as f:
    f.write('\n'.join(report) + '\n')
print('\n'.join(report))
