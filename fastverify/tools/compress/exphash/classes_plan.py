#!/usr/bin/env python3
"""classes_plan.py DECLS_TSV OUT_TSV --project ALLCONSTS_TSV [--targets FILE] [--semantic] [--exclude-modules Statements,Main]

Input for `expcompress --choose`: one line per theorem/definition `name<TAB>class<TAB>redirectable<TAB>cost`
(class = statement hash for theorems [+ value hash for definitions]; with --semantic the `class` column of
`exphash --classes`; redirectable = project constant, not a target, not in an excluded module; cost = the bytes of
export lines the declaration introduces = its own proof size), plus, with --semantic, fixed redirects
`R<TAB>FROM<TAB>TO` for every row of a project inductive block that is a shape copy of an earlier block (whole blocks
always go to the earliest one).  expcompress then picks per class the cheapest member that does not use another member,
and falls back to the earliest member for classes caught in a cycle."""
import sys, argparse, collections
ap = argparse.ArgumentParser()
ap.add_argument('decls'); ap.add_argument('out')
ap.add_argument('--project', help='allconsts.tsv (name, module, kind): only these are redirectable')
ap.add_argument('--nominal', help='names that are never redirected (e.g. every constant of the challenge export: '
                'exphash decls.tsv of it, or a name list); without --project everything else is redirectable')
ap.add_argument('--targets')
ap.add_argument('--semantic', action='store_true')
ap.add_argument('--exclude-modules', default='Statements,Main')
a = ap.parse_args()
excl = set(a.exclude_modules.split(','))
proj = None
if a.project:
    proj = {}
    for l in open(a.project):
        p = l.rstrip('\n').split('\t'); proj[p[0]] = p[1]
nominal = set()
if a.nominal:
    for l in open(a.nominal):
        p = l.rstrip('\n').split('\t')
        nominal.add(p[1] if len(p) > 1 and p[0] in ('thm', 'def', 'ind', 'ctor', 'rec', 'axiom', 'opaque', 'quot') else p[0])
targets = set(open(a.targets).read().split()) if a.targets else set()
first = {}
n = collections.Counter()
with open(a.decls) as f, open(a.out, 'w') as o:
    h = f.readline().rstrip('\n').split('\t'); ix = {k: i for i, k in enumerate(h)}
    for line in f:
        p = line.rstrip('\n').split('\t')
        k, name = p[0], p[ix['name']]
        red = name not in targets and name not in nominal and (proj is None or (name in proj and proj[name] not in excl))
        if k in ('ind', 'ctor', 'rec'):
            if not a.semantic:
                continue
            key = (k, p[ix['class']])
            if key not in first:
                first[key] = name
            elif red:
                o.write('R\t%s\t%s\n' % (name, first[key])); n['block_rows'] += 1
            continue
        # semantic mode: the statement/value hashes are computed modulo classes; nominal constants (class column = their
        # name) are grouped by the same hashes so that they can serve as representatives (they are never redirected)
        if k == 'thm':
            key = 't|' + ('|'.join((p[ix['type_hk']], p[ix['lvl_h']])) if a.semantic else '|'.join((p[ix['type_hk']], p[ix['type_hs']], p[ix['lvl_h']])))
        elif k == 'def':
            if a.semantic:
                hk = p[ix['extra']].split(' ')[0]
                hk = 'regular' if 'regular' in hk else hk
                key = 'd|' + '|'.join((p[ix['type_hk']], p[ix['lvl_h']], p[ix['value_hk']], hk))
            else:
                hk = p[ix['extra']].split(' ')[0]
                hk = 'regular' if 'regular' in hk else hk
                key = 'd|' + '|'.join((p[ix['type_hk']], p[ix['type_hs']], p[ix['lvl_h']], p[ix['value_hk']], hk))
        else:
            continue
        o.write('%s\t%s\t%d\t%s\n' % (name, key, 1 if red else 0, p[ix['new_bytes']]))
        n[k] += 1
print(dict(n), file=sys.stderr)
