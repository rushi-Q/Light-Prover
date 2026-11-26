#!/usr/bin/env python3
"""redirects.py DECLS_TSV OUT_TSV [--project ALLCONSTS_TSV] [--targets FILE] [--defs]

Sharing plan for expcompress from exphash's decls.tsv (rows are in export order = dependency order):
  * theorems: class = (statement kernel hash, binder-info hash, level-parameter names); every member that is a
    PROJECT theorem (--project: allconsts.tsv) and not an export target is redirected to the EARLIEST member of
    its class (earliest = cannot depend on any other member -> no cycles); the earliest may be a library theorem;
  * --defs: also project definitions with identical (type, value, reducibility kind, level names) [same rule].
Proof irrelevance makes theorem redirects type-preserving; identical definitions unfold identically."""
import sys, argparse
ap = argparse.ArgumentParser()
ap.add_argument('decls'); ap.add_argument('out')
ap.add_argument('--project'); ap.add_argument('--targets'); ap.add_argument('--defs', action='store_true')
a = ap.parse_args()
proj = None
if a.project:
    proj = set(l.split('\t', 1)[0] for l in open(a.project))
targets = set(open(a.targets).read().split()) if a.targets else set()
first = {}
n = {'thm': 0, 'def': 0}
with open(a.decls) as f, open(a.out, 'w') as o:
    h = f.readline().rstrip('\n').split('\t'); ix = {k: i for i, k in enumerate(h)}
    for line in f:
        p = line.rstrip('\n').split('\t')
        k = p[0]
        if k == 'thm':
            key = ('t', p[ix['type_hk']], p[ix['type_hs']], p[ix['lvl_h']])
        elif k == 'def' and a.defs:
            hk = p[ix['extra']].split(' ')[0]
            hk = 'regular' if 'regular' in hk else hk
            key = ('d', p[ix['type_hk']], p[ix['type_hs']], p[ix['lvl_h']], p[ix['value_hk']], hk)
        else:
            continue
        name = p[ix['name']]
        if key not in first:
            first[key] = name
            continue
        if name in targets or (proj is not None and name not in proj):
            continue
        o.write('%s\t%s\n' % (name, first[key]))
        n[k] += 1
print('redirects', n, file=sys.stderr)
