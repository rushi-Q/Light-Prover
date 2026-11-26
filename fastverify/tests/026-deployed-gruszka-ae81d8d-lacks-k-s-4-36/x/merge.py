#!/usr/bin/env python3
"""merge.py BASE.export EXTRA.ndjson OUT.export : append EXTRA's records to BASE with renumbered indices (names/levels
continue BASE's dense numbering, name 0 / level 0 shared); EXTRA declarations whose name BASE already declares are dropped."""
import json, sys
base = open(sys.argv[1], encoding='utf-8').read().rstrip('\n').split('\n')
extra = open(sys.argv[2], encoding='utf-8').read().rstrip('\n').split('\n')
names = {0: ()}; mn = ml = 0; me = -1; declared = set()
def nm(o, tab):
    d = o.get('str') or o.get('num'); tab[o['in']] = tab[d['pre']] + (d['str'] if 'str' in o else d['i'],)
def decl_names(o, tab):
    (k, d), = o.items()
    if k == 'inductive': return [tab[t['name']] for t in d['types']] + [tab[c['name']] for c in d['ctors']] + [tab[r['name']] for r in d['recs']]
    return [tab[d['name']]]
for l in base[1:]:
    o = json.loads(l)
    if 'in' in o: nm(o, names); mn = max(mn, o['in'])
    elif 'il' in o: ml = max(ml, o['il'])
    elif 'ie' in o: me = max(me, o['ie'])
    else: declared.update(decl_names(o, names))
xnames = {0: ()}
nmap = {0: 0}; lmap = {0: 0}; emap = {}
def bind(tab, i, nxt):
    if i not in tab: tab[i] = nxt
    return tab[i]
cnt = {'n': mn, 'l': ml, 'e': me}
def N(i): return nmap[i]
def L(i): return lmap[i]
def E(i): return emap[i]
out = list(base)
NAMEF = {'name', 'induct', 'ctor', 'typeName', 'param', 'pre'}
def fix(o, key=None):
    if isinstance(o, dict):
        r = {}
        for k, v in o.items():
            if k in ('in',): cnt['n'] += 1; nmap[v] = cnt['n']; r[k] = cnt['n']
            elif k == 'il': cnt['l'] += 1; lmap[v] = cnt['l']; r[k] = cnt['l']
            elif k == 'ie': cnt['e'] += 1; emap[v] = cnt['e']; r[k] = cnt['e']
            elif k in ('name', 'induct', 'ctor', 'typeName', 'pre') and isinstance(v, int): r[k] = N(v)
            elif k == 'param' and isinstance(v, int): r[k] = N(v)
            elif k in ('levelParams', 'all', 'ctors') and isinstance(v, list) and all(isinstance(x, int) for x in v): r[k] = [N(x) for x in v]
            elif k == 'us': r[k] = [L(x) for x in v]
            elif k in ('succ', 'sort') and isinstance(v, int): r[k] = L(v)
            elif k in ('max', 'imax'): r[k] = [L(x) for x in v]
            elif k in ('fn', 'arg', 'type', 'body', 'value', 'struct', 'expr', 'rhs') and isinstance(v, int): r[k] = E(v)
            elif k in ('bvar', 'idx', 'i', 'cidx', 'numParams', 'numIndices', 'numNested', 'numFields', 'numMotives', 'numMinors', 'nfields'): r[k] = v
            else: r[k] = fix(v, k)
        return r
    if isinstance(o, list): return [fix(x, key) for x in o]
    return o
dropped = []
for l in extra[1:]:
    o = json.loads(l)
    if 'in' in o: nm(o, xnames)
    if not ('in' in o or 'il' in o or 'ie' in o):
        dn = decl_names(o, xnames)
        if any(n in declared for n in dn): dropped.append('.'.join(map(str, dn[0]))); continue
    out.append(json.dumps(fix(o), separators=(',', ':'), ensure_ascii=False))
open(sys.argv[3], 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('dropped (already declared in base):', dropped)
