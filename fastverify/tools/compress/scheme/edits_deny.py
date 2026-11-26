#!/usr/bin/env python3
"""edits_deny.py EDITS OUT MODULES_FILE -- drop every edit of the team-format list EDITS whose module is listed in
MODULES_FILE (one module name per line; '#' comments). Used for failure-driven repairs of the composite candidate:
a module that failed to build with an owner's edits gets its original text back for that owner."""
import sys
ed, out, mf = sys.argv[1:4]
deny = {l.split()[0] for l in open(mf) if l.strip() and not l.startswith('#')}
k = d = 0
with open(out, 'w', encoding='utf-8') as fo:
    for ln in open(ed, encoding='utf-8'):
        if ln.split('\t', 1)[0] in deny: d += 1; continue
        fo.write(ln); k += 1
print(f'{ed}: kept {k} edits, dropped {d} (modules denied: {len(deny)})')
