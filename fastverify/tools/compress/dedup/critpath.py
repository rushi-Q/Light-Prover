#!/usr/bin/env python3
"""critpath.py IMPORTS_JSON COSTS_JSON_GZ [EDITS.tsv ...] : longest weighted import path (build critical path estimate)
of the project before and after the import lines added by edit lists (insert_before lines 'import X')."""
import sys, json, gzip, collections
imp = json.load(open(sys.argv[1])); cost = json.load(gzip.open(sys.argv[2]))
deps = {m: [d for d in v['imports'] if d in imp] for m, v in imp.items()}
def cp(deps):
    memo = {}
    order = []; state = {}
    for m0 in deps:
        if m0 in state: continue
        st = [(m0, iter(deps[m0]))]; state[m0] = 1
        while st:
            m, it = st[-1]; nxt = None
            for d in it:
                if d not in state: nxt = d; break
            if nxt is None: st.pop(); order.append(m)
            else: state[nxt] = 1; st.append((nxt, iter(deps[nxt])))
    for m in order:
        memo[m] = cost.get(m, 1.0) + max((memo[d] for d in deps[m]), default=0.0)
    top = max(memo, key=memo.get)
    return memo[top], top, sum(cost.get(m, 1.0) for m in deps)
b = cp(deps); print('before: critical path %.0f s (ends at %s), work %.0f s' % b)
added = 0
for f in sys.argv[3:]:
    for ln in open(f):
        p = ln.rstrip('\n').split('\t')
        if len(p) > 5 and p[3] == 'insert_before':
            for x in p[5].split('\\n'):
                if x.startswith('import '):
                    for d in x[7:].split():
                        if d in imp and d not in deps[p[0]]:
                            deps[p[0]] = deps[p[0]] + [d]; added += 1
a = cp(deps); print('after (+%d import edges): critical path %.0f s (ends at %s), work %.0f s' % ((added,) + a))
