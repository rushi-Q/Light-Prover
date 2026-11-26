#!/usr/bin/env python3
"""rename_deny.py RENAME_EDITS OUT FAILING_MODULES -- drop every rename (all its subst and line-replace edits) that touches
a failing module: a rename OLD -> NEW is identified by its subst text 'OLD NEW'; replace edits whose text mentions a
dropped NEW name are dropped too (failure-driven repair of the de-_alt renames in the composite candidate)."""
import re, sys
ed, out, mf = sys.argv[1:4]
fail = {l.split()[0] for l in open(mf) if l.strip()}
rows = [l.rstrip('\n').split('\t', 5) for l in open(ed, encoding='utf-8')]
bad = set()
for p in rows:
    if p[3] == 'subst' and p[0] in fail:
        bad.add(p[5].split(' ', 1)[0].split('.')[-1])
newbad = set()
for p in rows:
    if p[3] == 'subst' and p[5].split(' ', 1)[0].split('.')[-1] in bad:
        newbad.add(p[5].split(' ', 1)[1].split('.')[-1])
k = d = 0
with open(out, 'w', encoding='utf-8') as f:
    for p in rows:
        if p[3] == 'subst' and p[5].split(' ', 1)[0].split('.')[-1] in bad: d += 1; continue
        if p[3] == 'replace' and any(re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'!?])", p[5]) or re.search(r'\.' + re.escape(n) + r"(?![\w'!?])", p[5]) for n in newbad): d += 1; continue
        f.write('\t'.join(p) + '\n'); k += 1
print(f'renames dropped {len(bad)} ({sorted(bad)[:8]}), edits dropped {d}, kept {k}')
