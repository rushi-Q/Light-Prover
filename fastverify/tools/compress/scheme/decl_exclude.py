#!/usr/bin/env python3
"""decl_exclude.py EDITS OTHER_EDITS DECLS_TSV OUT -- drop every edit of EDITS that lies in a declaration (prune.py's
R.json.decls.tsv ranges, original coordinates) which also contains an edit of OTHER_EDITS. Used for automation edits
(autoshorten) vs dead-have elimination: an automated closer may use a hypothesis that was dead before."""
import bisect, collections, sys
ed, other, decls, out = sys.argv[1:5]
R = collections.defaultdict(list)
for ln in open(decls, encoding='utf-8'):
    if ln.startswith('#'): continue
    p = ln.split('\t')
    if len(p) >= 3: R[p[0]].append((int(p[1]), int(p[2])))
for m in R: R[m].sort()
def decl_of(m, s):
    L = R.get(m, []); i = bisect.bisect_right(L, (s, 10**9)) - 1
    return (m, L[i]) if i >= 0 and L[i][0] <= s <= L[i][1] else None
busy = set()
for ln in open(other, encoding='utf-8'):
    p = ln.split('\t')
    d = decl_of(p[0], int(p[1]))
    if d: busy.add(d)
k = d_ = 0
with open(out, 'w', encoding='utf-8') as fo:
    for ln in open(ed, encoding='utf-8'):
        p = ln.split('\t')
        if decl_of(p[0], int(p[1])) in busy: d_ += 1; continue
        fo.write(ln); k += 1
print(f'kept {k}, dropped {d_} (declarations with an edit of the other list: {len(busy)})')
