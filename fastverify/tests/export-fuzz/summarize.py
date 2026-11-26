#!/usr/bin/env python3
"""summarize.py RUNDIR... : markdown summary of runfuzz.py results (per base, per op class, statuses, parser statuses,
availability reasons). RUNDIR = a campaign root (with <base>/results.tsv) or a single run dir."""
import os, sys, collections
rows = []
for root in sys.argv[1:]:
    cands = [os.path.join(root, 'results.tsv')] + [os.path.join(root, d, 'results.tsv') for d in sorted(os.listdir(root)) if os.path.isdir(os.path.join(root, d))]
    for f in cands:
        if os.path.exists(f):
            base = os.path.basename(os.path.dirname(f))
            for l in open(f):
                p = l.rstrip('\n').split('\t')
                if len(p) >= 10:
                    rows.append([base] + p)
ST = ['FAIL-CRITICAL', 'FAIL-PARSER', 'OK-ACCEPT', 'OK-REJECT', 'OK-DECLINE', 'WARN-AVAIL', 'OF-ERROR']
def table(key, title):
    c = collections.defaultdict(collections.Counter)
    for r in rows:
        c[key(r)][r[10]] += 1
    print(f'| {title} | mutants | ' + ' | '.join(ST) + ' |')
    print('|---|---:|' + '---:|' * len(ST))
    tot = collections.Counter()
    for k in sorted(c):
        n = sum(c[k].values()); tot.update(c[k])
        print(f'| {k} | {n} | ' + ' | '.join(str(c[k].get(s, 0)) for s in ST) + ' |')
    print(f'| **total** | **{sum(tot.values())}** | ' + ' | '.join(f'**{tot.get(s, 0)}**' for s in ST) + ' |')
    print()
table(lambda r: r[0], 'base')
table(lambda r: r[3], 'class')
pd = collections.Counter(r[5] for r in rows)
print('Parser differential (parsediff) statuses: ' + ', '.join(f'{k} {v}' for k, v in sorted(pd.items())) + '\n')
av = collections.Counter()
for r in rows:
    if r[10] == 'WARN-AVAIL':
        reason = r[13][:110]
        av[(r[2], r[6], reason)] += 1
print('| availability (official ACCEPTED, CS not) op | CS verdict | CS reason | n |\n|---|---|---|---:|')
for (op, v, why), n in av.most_common():
    print(f'| {op} | {v} | {why} | {n} |')

def leg(reason):
    r = reason
    if 'Invalid JSON' in r or 'not found ' in r.lower() and ('Expr' in r or 'Name' in r or 'Level' in r) or 'bound twice' in r or 'Unknown export object' in r \
       or 'Expected JSON object' in r or 'invalid' in r and 'Expr.' in r or 'Duplicate declaration' in r or 'unknown quot kind' in r or 'safety parameter' in r \
       or 'Invalid binder info' in r or ' invalid' in r:
        return 'parser (both readers fail)'
    if 'gruszka' in r and 'exited with 1' in r:
        return 'second kernel (gruszka)'
    if 'Lean default exited with 1' in r:
        return 'official kernel leg'
    if any(k in r for k in ('does not match', 'do not match', "don't match", 'Illegal axiom', 'Const not found', 'Constant not found', 'not a theorem', 'not a definition')):
        return 'comparison / axioms (official judge code)'
    return 'other: ' + r[:60]
print('\n| official REJECTED: who decided in CS | n |\n|---|---:|')
k = collections.Counter()
for r in rows:
    if r[8] == 'REJECTED':
        k[leg(r[13]) if r[6] == 'REJECTED' else 'CS ' + r[6]] += 1
for a, n in k.most_common():
    print(f'| {a} | {n} |')
g = collections.Counter()
for r in rows:
    if len(r) > 16 and r[16] != 'NA':
        okind = 'official kernel rejected' if 'Lean default exited with 1' in r[14] or 'Lean default kernel rejected' in r[14] else ('official accepted' if r[8] == 'ACCEPTED' else 'official rejected (parser/comparison)')
        g[(okind, r[16])] += 1
if g:
    print('\n| second kernel alone (gruszka, sandboxed) vs official | gruszka | n |\n|---|---|---:|')
    for (a, b), n in sorted(g.items()):
        print(f'| {a} | {b} | {n} |')
