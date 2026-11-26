#!/usr/bin/env python3
"""r2_to_orig.py ROUND2_DELETED_TSV ORIG_DECLS_TSV CHAINMERGE_TSV OUT_EDITS [--owner P01r2] -- translate the deletions of a
second pruning round (computed on a candidate tree's OWN oleans: module, kind, name, start, end in candidate coordinates)
into 'delete' edits against the ORIGINAL sources (prune.py's R.json.decls.tsv of the first round: module, start, end, kind,
live, deleted, names), so the round composes with every other edit list in one pipeline run.
Names are matched exactly; private names `_private.<M>.0.<x>` are matched by <x> within the original modules that were
chain-merged into the candidate module M. A declaration already deleted by round 1 or not found is skipped (reported)."""
import argparse, collections, re, sys
ap = argparse.ArgumentParser(); ap.add_argument('deleted'); ap.add_argument('decls'); ap.add_argument('chainmerge')
ap.add_argument('out'); ap.add_argument('--owner', default='P01r2')
ap.add_argument('--protect-texts', nargs='*', default=[], help='DO NOT USE (kept for the record): protecting names AFTER the prune fixpoint breaks it - a kept declaration can cite a deleted one (RH C4 v1: 178 cases). Pass the new lists to prune.py --other-edits instead (round2.sh OTHER_EDITS)')
a = ap.parse_args()
TOK = re.compile(r"[A-Za-z0-9_'!?\u0370-\u03ff\u1f00-\u1ffe\u2100-\u214f\u2080-\u209c]+")
protected = set()
for f in a.protect_texts:
    for ln in open(f, encoding='utf-8'):
        p = ln.rstrip('\n').split('\t', 5)
        if len(p) > 5: protected.update(TOK.findall(p[5].replace('\\n', ' ')))
PRIV = re.compile(r'^_private\.(.+?)\.0\.(.+)$')
merged_into = collections.defaultdict(set)       # candidate module -> original modules in it
for ln in open(a.chainmerge):
    x, k = ln.split(); merged_into[k].add(x)
by_name = {}; by_priv = {}
for ln in open(a.decls, encoding='utf-8'):
    if ln.startswith('#'): continue
    p = ln.rstrip('\n').split('\t')
    if len(p) < 7: continue
    mod, s, e, kind, live, dele, names = p[0], int(p[1]), int(p[2]), p[3], p[4], p[5], p[6]
    rec = (mod, s, e, dele == '1')
    for n in names.split(','):
        n = n.strip()
        if not n: continue
        mo = PRIV.match(n)
        if mo: by_priv[(mo.group(1), mo.group(2))] = rec
        else: by_name.setdefault(n, []).append(rec)   # a public name can be declared in several modules (never imported
                                                       # together): pick the one in the candidate module (D17 C4 v3 fix)
st = collections.Counter(); out = set()
for ln in open(a.deleted, encoding='utf-8'):
    p = ln.rstrip('\n').split('\t')
    if len(p) < 5: continue
    mod, kind, name = p[0], p[1], p[2]
    if name.rsplit('.', 1)[-1] in protected: st['protected_by_other_lists'] += 1; continue
    mo = PRIV.match(name); rec = None
    if mo:
        for om in [mo.group(1)] + sorted(merged_into.get(mo.group(1), ())):
            rec = by_priv.get((om, mo.group(2)))
            if rec: break
    else:
        recs = by_name.get(name, [])
        allowed = {mod} | merged_into.get(mod, set())
        here = [r for r in recs if r[0] in allowed]
        if len(here) == 1: rec = here[0]
        elif len(recs) == 1 and not here: rec = None; st['module_mismatch'] += 1
        elif len(here) > 1: rec = None; st['ambiguous_in_module'] += 1
        else: rec = None
    if rec is None: st['not_found'] += 1; continue
    if rec[3]: st['already_deleted_round1'] += 1; continue
    out.add(rec[:3]); st['translated'] += 1
with open(a.out, 'w', encoding='utf-8') as f:
    for mod, s, e in sorted(out):
        f.write(f'{mod}\t{s}\t{e}\tdelete\t{a.owner}\t\n')
print(dict(st), 'edits', len(out), 'lines', sum(e - s + 1 for _, s, e in out))
