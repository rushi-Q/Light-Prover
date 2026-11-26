#!/usr/bin/env python3
"""apply_inplace.py SRC_DIR EDITS.tsv -- apply a team-P edit list IN PLACE to a private copy of the sources (each edited
file is unlinked and rewritten, so hard links to other trees are never written through). Prints a JSON summary."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from editlib import read_edits, apply
src, ed = sys.argv[1], sys.argv[2]
E, _ = read_edits(ed)
S = {'files': 0, 'edits': 0, 'lines_before': 0, 'lines_after': 0}
for mod, es in E.items():
    p = os.path.join(src, mod.replace('.', '/') + '.lean')
    L = open(p, encoding='utf-8').read().split('\n')
    N = apply(L, es)
    os.unlink(p)
    with open(p, 'w', encoding='utf-8') as f:
        f.write('\n'.join(N))
    S['files'] += 1; S['edits'] += len(es); S['lines_before'] += len(L); S['lines_after'] += len(N)
S['lines_removed'] = S['lines_before'] - S['lines_after']
print(json.dumps(S))
