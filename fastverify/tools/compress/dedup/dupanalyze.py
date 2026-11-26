#!/usr/bin/env python3
"""dupanalyze.py SCAN_OUT_DIR OUTDIR : duplicate-statement analysis over dupscan scan output.
Writes OUTDIR/closure.txt (project constants in the closure of the 5 targets), OUTDIR/groups.tsv
(group id, member: module, kind, name, nlev, tyhash, lines, inClosure, indegree), OUTDIR/summary.json."""
import sys, glob, collections, json, os
D, O = sys.argv[1], sys.argv[2]
os.makedirs(O, exist_ok=True)
TARGETS = ["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"]
ids = {}; names = []
def iid(s):
    i = ids.get(s)
    if i is None:
        i = len(names); ids[s] = i; names.append(s)
    return i
info = {}   # cid -> (mod, kind, nlev, tyhash, valhash, depth, l1, l2)
uses = {}
for f in sorted(glob.glob(D + '/c*.tsv')):
    for ln in open(f, encoding='utf-8', errors='replace'):
        p = ln.rstrip('\n').split('\t')
        if p[0] != 'K': continue
        c = iid(p[3])
        info[c] = (p[1], p[2], int(p[4]), p[5], p[6], int(p[7]), int(p[8]), int(p[9]))
        uses[c] = [iid(u) for u in p[10].split(' ')] if len(p) > 10 and p[10] else []
print('consts', len(info), flush=True)
# closure of targets over project constants
seen = set(); st = [ids[t] for t in TARGETS if t in ids]
while st:
    c = st.pop()
    if c in seen or c not in info: continue
    seen.add(c); st.extend(uses[c])
print('closure project consts', len(seen), flush=True)
indeg = collections.Counter()
for c, us in uses.items():
    for u in us: indeg[u] += 1
with open(O + '/closure.txt', 'w') as fh:
    for c in seen: fh.write(names[c] + '\n')
# statement groups of user-written theorems
g = collections.defaultdict(list)
for c, r in info.items():
    if r[1] == 't' and r[6] > 0:
        g[(r[2], r[3])].append(c)
groups = [v for v in g.values() if len(v) > 1]
def lines(c): r = info[c]; return r[7] - r[6] + 1
groups.sort(key=lambda v: -sum(lines(c) for c in v))
S = collections.Counter()
with open(O + '/groups.tsv', 'w') as fh:
    for gi, v in enumerate(groups):
        # canonical: in closure first, then fewest lines, then name
        v.sort(key=lambda c: (c not in seen, lines(c), names[c]))
        mods = set(info[c][0] for c in v)
        S['groups'] += 1; S['members'] += len(v); S['removable'] += len(v) - 1
        S['removable_lines'] += sum(lines(c) for c in v[1:])
        S['group_lines'] += sum(lines(c) for c in v)
        S['groups_samemodule_only'] += (len(mods) == 1)
        S['removable_inclosure'] += sum(1 for c in v[1:] if c in seen)
        S['removable_lines_inclosure'] += sum(lines(c) for c in v[1:] if c in seen)
        S['groups_all_inclosure'] += all(c in seen for c in v)
        S['groups_some_inclosure'] += any(c in seen for c in v)
        for c in v:
            r = info[c]
            fh.write(f"{gi}\t{r[0]}\t{r[1]}\t{names[c]}\t{r[2]}\t{r[3]}\t{lines(c)}\t{int(c in seen)}\t{indeg[c]}\t{r[5]}\t{r[6]}\t{r[7]}\n")
sz = collections.Counter(min(len(v), 20) for v in groups)
S['size_hist'] = dict(sorted(sz.items()))
ut = [c for c, r in info.items() if r[1] == 't' and r[6] > 0]
S['user_thms'] = len(ut); S['user_thm_lines'] = sum(lines(c) for c in ut)
S['user_thms_inclosure'] = sum(1 for c in ut if c in seen)
S['user_thm_lines_inclosure'] = sum(lines(c) for c in ut if c in seen)
json.dump(S, open(O + '/summary.json', 'w'), indent=1)
print(json.dumps(S, indent=1))
