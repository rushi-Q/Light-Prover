#!/usr/bin/env python3
"""redirects_sem.py CLASSES_DECLS_TSV OUT_TSV --project ALLCONSTS_TSV [--targets FILE] [--kinds thm,def,ind,ctor,rec]
                    [--exclude-modules Statements,Main]

Sharing plan from `exphash --classes --project ...` output (column `class` = semantic class: constant references
hashed by the class of the referenced constant; theorem class = statement only; def class = type + value + level names
+ reducibility kind; inductive rows = block shape with self-references normalized).  Every project constant (not a
target, not defined in an excluded module, i.e. not part of the challenge's statements) is redirected to the EARLIEST
row of its class and kind (export order = dependency order -> no cycles).  Rows of library constants are nominal
(their class is their name) and are never redirected."""
import sys, argparse, collections
ap = argparse.ArgumentParser()
ap.add_argument('decls'); ap.add_argument('out')
ap.add_argument('--project', required=True); ap.add_argument('--targets')
ap.add_argument('--kinds', default='thm,def,ind,ctor,rec')
ap.add_argument('--exclude-modules', default='Statements,Main')
a = ap.parse_args()
excl = set(a.exclude_modules.split(','))
proj = {}
for l in open(a.project):
    p = l.rstrip('\n').split('\t')
    proj[p[0]] = p[1]
targets = set(open(a.targets).read().split()) if a.targets else set()
kinds = set(a.kinds.split(','))
first = {}
n = collections.Counter()
with open(a.decls) as f, open(a.out, 'w') as o:
    h = f.readline().rstrip('\n').split('\t'); ix = {k: i for i, k in enumerate(h)}
    for line in f:
        p = line.rstrip('\n').split('\t')
        k = p[0]
        if k not in kinds:
            continue
        key = (k, p[ix['class']])
        name = p[ix['name']]
        if key not in first:
            first[key] = name
            continue
        if name in targets or name not in proj or proj[name] in excl:
            continue
        o.write('%s\t%s\n' % (name, first[key]))
        n[k] += 1
print('redirects', dict(n), file=sys.stderr)
