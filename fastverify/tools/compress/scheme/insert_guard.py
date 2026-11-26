#!/usr/bin/env python3
"""insert_guard.py EDITS OUT OTHER_EDITS... -- drop the insert_before edits of EDITS (e.g. docstrings) whose anchor line
is deleted by a delete edit of an OTHER list (the declaration they document is gone; apply_edits treats an insert as a
point edit that does not overlap the deletion, so the docstring would be left dangling: 'unexpected end of input;
expected lemma' in the RH C3b build, Development...CharacterBoxes.MainConclusion). Also drops inserts into modules that
an OTHER list deletes as a whole (deletefile)."""
import collections, sys
ed, out = sys.argv[1:3]
dels = collections.defaultdict(list); gone = set()
for f in sys.argv[3:]:
    for ln in open(f, encoding='utf-8'):
        p = ln.rstrip('\n').split('\t')
        if len(p) < 4: continue
        if p[3] == 'delete': dels[p[0]].append((int(p[1]), int(p[2])))
        elif p[3] == 'deletefile': gone.add(p[0])
k = d = 0
with open(out, 'w', encoding='utf-8') as fo:
    for ln in open(ed, encoding='utf-8'):
        p = ln.split('\t')
        if p[3] == 'insert_before':
            L = int(p[1])
            if p[0] in gone or any(s <= L <= e for s, e in dels.get(p[0], ())):
                d += 1; continue
        fo.write(ln); k += 1
print(f'kept {k}, dropped {d} inserts anchored in deleted code')
