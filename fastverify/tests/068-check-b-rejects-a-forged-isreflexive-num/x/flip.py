#!/usr/bin/env python3
"""flip.py MAIN.export OUTDIR : forge ONE field of the exported InductiveVal (types[0]) of the solution-only inductives
Helper / Tree (all other bytes unchanged): Helper isReflexive false->true, Tree isReflexive false->true, Tree numNested 1->2,
and (control: rejected by official nanoda too) Tree numNested 1->0."""
import json, sys, os
src, out = sys.argv[1], sys.argv[2]
names = {}; L = open(src).read().split('\n')
for l in L:
    if l.startswith('{"in"'):
        o = json.loads(l); s = o.get('str') or o.get('num')
        names[o['in']] = (names[s['pre']] + '.' if s['pre'] else '') + str(s.get('str', s.get('i')))
J = lambda o: json.dumps(o, separators=(',', ':'), sort_keys=True)
muts = {'Helper': {'isReflexive': lambda t: t.__setitem__('isReflexive', not t['isReflexive'])},
        'Tree': {'isReflexive': lambda t: t.__setitem__('isReflexive', not t['isReflexive']),
                 'numNested': lambda t: t.__setitem__('numNested', t['numNested'] + 1),
                 'numNested0': lambda t: t.__setitem__('numNested', 0)}}
for i, l in enumerate(L):
    if l.startswith('{"inductive"'):
        o = json.loads(l); t = o['inductive']['types'][0]; n = names[t['name']]
        if n in muts:
            for mn, f in muts[n].items():
                o2 = json.loads(l); f(o2['inductive']['types'][0])
                open(os.path.join(out, f'sol_{n}_{mn}.export'), 'w').write('\n'.join(L[:i] + [J(o2)] + L[i+1:]))
