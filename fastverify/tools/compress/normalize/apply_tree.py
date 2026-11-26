#!/usr/bin/env python3
"""apply_tree.py PROJECT_DIR OUT_DIR EDITS.tsv [--srcdir src] -- copy a Lean project (without .lake/.git) and apply a
delete-only team-format edit list (line numbers of the PROJECT_DIR files). Prints a JSON summary.
Resolves package srcDir via normalize.resolve_srcdir so root-layout projects (Cedar, Cslib, Clean, SampCert, ArkLib) work identically to src/-layout projects."""
import sys, os, shutil, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import normalize as NZ

proj, out, ed = sys.argv[1], sys.argv[2], sys.argv[3]
srcdir_arg = sys.argv[sys.argv.index('--srcdir') + 1] if '--srcdir' in sys.argv else 'src'
if os.path.exists(out):
    sys.exit(f'apply_tree: {out} exists')
D = collections.defaultdict(set)
for ln in open(ed, encoding='utf-8'):
    p = ln.rstrip('\n').split('\t')
    if len(p) < 5:
        continue
    if p[3] != 'delete':
        sys.exit('apply_tree: only delete edits supported')
    for i in range(int(p[1]), int(p[2]) + 1):
        D[p[0]].add(i)
shutil.copytree(proj, out, symlinks=True, ignore=shutil.ignore_patterns('.lake', '.git'))
osrc = NZ.resolve_srcdir(out, srcdir_arg)
n = 0
for m, dels in D.items():
    q = os.path.join(osrc, m.replace('.', '/') + '.lean')
    lines = open(q, encoding='utf-8').read().split('\n')
    new = [l for i, l in enumerate(lines, 1) if i not in dels]
    os.unlink(q)
    with open(q, 'w', encoding='utf-8') as f:
        f.write('\n'.join(new))
    n += len(lines) - len(new)
print(json.dumps({'modules_edited': len(D), 'lines_deleted': n}))
