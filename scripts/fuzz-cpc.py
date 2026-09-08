#!/usr/bin/env python3
"""Soundness fuzzer for Carcara's CPC proof checking.

Takes CPC proofs that Carcara accepts and corrupts them, one mutation at a time, in ways that
should make them unacceptable: dropping or reordering the premises of a step, restating its
conclusion, renaming its rule, perturbing its arguments, or tampering with an assumption.
Carcara must then reject the proof (or report it holey, if the mutation lands on a step that
becomes a hole). A mutant that still checks *valid* is reported: either the mutation was
harmless (the rule is insensitive to it, e.g. the order of the premises of a conjunction
introduction) or Carcara accepts something it should not.

Only steps the final step transitively depends on are mutated, since the translation prunes
everything else, and only proofs that Carcara accepts as valid (not holey) are used, since a
`hole` step accepts any conclusion.

Usage: fuzz-cpc.py <proof.cpc>... [--carcara BIN] [--rare FILE] [--per-proof N] [--seed N]
       [--keep DIR]
"""

import argparse
import os
import random
import re
import subprocess
import sys
import tempfile

STEP = re.compile(r'^\(step(-pop)? (\S+) (.*)$')
ASSUME = re.compile(r'^\(assume(-push)? (\S+) (.*)\)\s*$')
PREMISES = re.compile(r':premises \(([^)]*)\)')
RULE = re.compile(r':rule (\S+)')


class Command:
    """One line of a CPC proof: a step, an assumption, or anything else."""

    def __init__(self, index, line):
        self.index = index
        self.line = line
        self.id = None
        self.kind = 'other'
        m = ASSUME.match(line)
        if m:
            self.id, self.kind = m.group(2), 'assume'
            return
        m = STEP.match(line)
        if m:
            self.id, self.kind = m.group(2), 'step'
            self.rule = (RULE.search(line) or [None, ''])[1] if RULE.search(line) else ''
            self.rule = RULE.search(line).group(1) if RULE.search(line) else ''
            p = PREMISES.search(line)
            self.premises = p.group(1).split() if p else []

    def conclusion(self):
        """The conclusion of a step: what stands between the id and the first keyword."""
        m = STEP.match(self.line)
        if not m:
            return None
        rest = m.group(3)
        i = rest.find(' :')
        return rest[:i] if i > 0 else None


def parse(path):
    with open(path) as f:
        lines = f.read().splitlines()
    return [Command(i, l) for i, l in enumerate(lines)]


def reachable(commands):
    """The ids of the commands the last step transitively depends on. Scopes are approximated
    by keeping every command of a scope whose closing `step-pop` is reached."""
    by_id = {c.id: c for c in commands if c.id}
    last = next((c for c in reversed(commands) if c.kind == 'step'), None)
    if last is None:
        return set()
    seen, work = {last.id}, [last.id]
    while work:
        c = by_id.get(work.pop())
        if c is None or c.kind != 'step':
            continue
        for p in c.premises:
            if p not in seen:
                seen.add(p)
                work.append(p)
    # A reached `step-pop` keeps the whole scope it closes
    if any(c.line.startswith('(step-pop') and c.id in seen for c in commands):
        for c in commands:
            if c.id:
                seen.add(c.id)
    return seen


def mutations(commands, targets, rng):
    """Yields (name, mutated lines) for one mutation of a randomly chosen target."""
    steps = [c for c in targets if c.kind == 'step' and c.rule not in ('trust', 'trust_theory_rewrite')]
    assumes = [c for c in targets if c.kind == 'assume']
    conclusions = [c.conclusion() for c in commands if c.kind == 'step' and c.conclusion()]
    rules = sorted({c.rule for c in commands if c.kind == 'step' and c.rule})
    kinds = []
    if steps:
        kinds += ['conclusion', 'rule', 'args']
        if any(len(c.premises) >= 1 for c in steps):
            kinds.append('premise-drop')
        if any(len(c.premises) >= 2 for c in steps):
            kinds.append('premise-swap')
    if assumes:
        kinds.append('assume')
    if not kinds:
        return None
    kind = rng.choice(kinds)
    lines = [c.line for c in commands]

    if kind == 'assume':
        c = rng.choice(assumes)
        m = ASSUME.match(c.line)
        other = rng.choice([t for t in conclusions if t != m.group(3)] or [m.group(3)])
        lines[c.index] = f'(assume{m.group(1) or ""} {c.id} {other})'
        return f'assume/{c.id}', lines

    if kind == 'conclusion':
        c = rng.choice(steps)
        old = c.conclusion()
        others = [t for t in conclusions if t != old]
        if not others:
            return None
        lines[c.index] = c.line.replace(old, rng.choice(others), 1)
        return f'conclusion/{c.id}', lines

    if kind == 'rule':
        c = rng.choice(steps)
        others = [r for r in rules if r != c.rule]
        if not others:
            return None
        lines[c.index] = c.line.replace(f':rule {c.rule}', f':rule {rng.choice(others)}', 1)
        return f'rule/{c.id}:{c.rule}', lines

    if kind == 'args':
        c = rng.choice(steps)
        m = re.search(r':args \((.*)\)\s*\)\s*$', c.line)
        if not m:
            return None
        args = m.group(1)
        # perturb an integer argument if there is one, otherwise drop the last argument
        ints = list(re.finditer(r'(?<![\w@.-])(\d+)(?![\w.])', args))
        if ints:
            i = rng.choice(ints)
            new_args = args[:i.start()] + str(int(i.group(1)) + 1) + args[i.end():]
        else:
            parts = args.split()
            if len(parts) < 2:
                return None
            new_args = ' '.join(parts[:-1])
        lines[c.index] = c.line[:m.start(1)] + new_args + c.line[m.end(1):]
        return f'args/{c.id}', lines

    if kind == 'premise-drop':
        c = rng.choice([s for s in steps if s.premises])
        dropped = rng.randrange(len(c.premises))
        keep = [p for i, p in enumerate(c.premises) if i != dropped]
        lines[c.index] = PREMISES.sub(f':premises ({" ".join(keep)})', c.line, count=1)
        return f'premise-drop/{c.id}', lines

    c = rng.choice([s for s in steps if len(s.premises) >= 2])
    ps = list(c.premises)
    i, j = rng.sample(range(len(ps)), 2)
    ps[i], ps[j] = ps[j], ps[i]
    lines[c.index] = PREMISES.sub(f':premises ({" ".join(ps)})', c.line, count=1)
    return f'premise-swap/{c.id}', lines


def check(carcara, rare, proof, problem, timeout=60):
    """Runs Carcara on a CPC proof; returns (verdict, stderr)."""
    cmd = [carcara, 'check', '--proof-format', 'cpc', '--allow-int-real-subtyping',
           '--rare-file', rare, proof, problem]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'timeout', ''
    verdict = (r.stdout.strip().splitlines() or ['none'])[-1]
    return verdict, r.stderr


def problem_checks(carcara, rare, proof, problem, tmpdir):
    """Checks the proof against corrupted problems, which must all be rejected: the proof's
    assumptions are checked against the problem's assertions, so dropping or negating one of
    them (which can only make the problem weaker, or satisfiable) must break the check."""
    with open(problem) as f:
        lines = f.read().splitlines()
    asserts = [i for i, l in enumerate(lines) if l.strip().startswith('(assert')]
    results = []
    for kind in ('drop', 'negate'):
        if not asserts:
            break
        i = asserts[len(asserts) // 2]
        new_lines = list(lines)
        if kind == 'drop':
            del new_lines[i]
        else:
            body = new_lines[i].strip()
            if not (body.startswith('(assert ') and body.endswith(')')):
                continue
            new_lines[i] = '(assert (not ' + body[len('(assert '):-1] + '))'
        path = os.path.join(tmpdir, f'problem-{kind}.smt2')
        with open(path, 'w') as f:
            f.write('\n'.join(new_lines) + '\n')
        verdict, err = check(carcara, rare, proof, path)
        results.append((kind, verdict, err))
        os.unlink(path)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('proofs', nargs='+')
    ap.add_argument('--carcara', default='target/release/carcara')
    ap.add_argument('--rare', default=os.path.expanduser('~/carcara/rewrites.eo'))
    ap.add_argument('--per-proof', type=int, default=10)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--keep', default=None, help='directory to save surviving mutants in')
    args = ap.parse_args()
    rng = random.Random(args.seed)
    if args.keep:
        os.makedirs(args.keep, exist_ok=True)

    totals = {'valid': 0, 'rejected': 0, 'holey': 0, 'timeout': 0, 'crash': 0, 'skipped': 0,
              'problem-valid': 0, 'problem-rejected': 0}
    survivors = []
    for path in args.proofs:
        problem = path[:-4] + '.smt2'
        if not os.path.exists(problem):
            continue
        base = check(args.carcara, args.rare, path, problem)[0]
        if base != 'valid':
            totals['skipped'] += 1
            continue
        with tempfile.TemporaryDirectory() as tmpdir:
            for kind, verdict, err in problem_checks(args.carcara, args.rare, path, problem, tmpdir):
                if verdict == 'valid':
                    totals['problem-valid'] += 1
                    print(f'SURVIVED-PROBLEM {os.path.basename(path)} [{kind}]', flush=True)
                elif 'panicked' in err or 'fatal runtime' in err:
                    totals['crash'] += 1
                    print(f'CRASH-PROBLEM {os.path.basename(path)} [{kind}]', flush=True)
                else:
                    totals['problem-rejected'] += 1

        commands = parse(path)
        keep = reachable(commands)
        targets = [c for c in commands if c.id in keep]
        for _ in range(args.per_proof):
            out = mutations(commands, targets, rng)
            if out is None:
                continue
            name, lines = out
            with tempfile.NamedTemporaryFile('w', suffix='.cpc', delete=False) as f:
                f.write('\n'.join(lines) + '\n')
                mutant = f.name
            verdict, err = check(args.carcara, args.rare, mutant, problem)
            if verdict == 'valid':
                totals['valid'] += 1
                survivors.append((path, name))
                print(f'SURVIVED {os.path.basename(path)} [{name}]', flush=True)
                if args.keep:
                    dst = os.path.join(args.keep,
                                       f'{os.path.basename(path)[:-4]}.{name.replace("/", "_")}.cpc')
                    os.replace(mutant, dst)
                    mutant = None
            elif verdict == 'holey':
                totals['holey'] += 1
            elif verdict == 'timeout':
                totals['timeout'] += 1
            elif 'panicked' in err or 'fatal runtime' in err:
                totals['crash'] += 1
                print(f'CRASH {os.path.basename(path)} [{name}] '
                      f'{[l for l in err.splitlines() if "panicked" in l or "fatal" in l][:1]}',
                      flush=True)
                if args.keep:
                    dst = os.path.join(args.keep,
                                       f'crash.{os.path.basename(path)[:-4]}.{name.replace("/", "_")}.cpc')
                    os.replace(mutant, dst)
                    mutant = None
            else:
                totals['rejected'] += 1
            if mutant:
                os.unlink(mutant)

    print('\n== mutants:', ', '.join(f'{k} {v}' for k, v in totals.items()))
    if survivors:
        print(f'== {len(survivors)} mutants still check valid (triage needed):')
        for path, name in survivors:
            print(f'   {os.path.basename(path)} [{name}]')
    return 0


if __name__ == '__main__':
    sys.exit(main())
