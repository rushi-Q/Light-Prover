#!/usr/bin/env python3
"""evidence.py — export-level evidence for a compressed candidate.

usage: evidence.py --expdiff BIN --orig ORIG.export --new NEW.export --targets TARGETS --out DIR
                   [--edits EDITS.tsv ...] [--decls DECLS.tsv] [--threads N] [--dead-lets]

Runs `expdiff diff` (statuses, explain, optional --dead-lets) of NEW against ORIG over the targets' closure and writes
DIR/diff.out, DIR/diff.tsv, and DIR/evidence.md: a summary table (closure sizes, global DAG, per-status counts,
statement drift) and, when edit lists + a declaration->module map are given, the attribution of every changed
declaration to the owners whose edits touch its module (declaration ranges from a decls.tsv table; private and
auxiliary names are mapped to their parent declaration). Nothing here is trusted: the verdict is the trusted check's.
"""
import argparse, collections, csv, os, re, subprocess, sys

csv.field_size_limit(10**9)
ap = argparse.ArgumentParser()
ap.add_argument('--expdiff', required=True); ap.add_argument('--orig', required=True); ap.add_argument('--new', required=True)
ap.add_argument('--targets', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--edits', nargs='*', default=[]); ap.add_argument('--decls')
ap.add_argument('--threads', type=int, default=os.cpu_count()); ap.add_argument('--dead-lets', action='store_true')
ap.add_argument('--no-private-modulo', action='store_true', help='compare private names literally (default: modulo module part)')
a = ap.parse_args()
os.makedirs(a.out, exist_ok=True)
cmd = [a.expdiff, 'diff', '-j', str(a.threads), '--targets', a.targets, '--explain', '5', '--tsv',
       os.path.join(a.out, 'diff.tsv'), a.orig, a.new] + (['--dead-lets'] if a.dead_lets else []) + \
      ([] if a.no_private_modulo else ['--private-modulo'])
with open(os.path.join(a.out, 'diff.out'), 'w') as f:
    rc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT).returncode
if rc != 0:
    sys.exit(f'evidence: expdiff failed (rc {rc}), see {a.out}/diff.out')
kv = collections.OrderedDict(); status = collections.OrderedDict(); result = ''; changed_stmt = []
for ln in open(os.path.join(a.out, 'diff.out')):
    p = ln.rstrip('\n').split('\t')
    if p[0] == 'status':
        status[p[1]] = int(p[2])
    elif p[0] == 'RESULT':
        result = p[1]
    elif p[0] == 'statement_changed':
        changed_stmt.append(p[1])
    elif len(p) >= 2 and re.match(r'^(old|new)\.', p[0]):
        kv[p[0]] = p[1]
        if len(p) >= 4:
            kv[p[2]] = p[3]

def parent(n):
    m = re.sub(r'\._proof_\d+(_\d+)*$', '', n)
    m = re.sub(r'\.(match|eq|proof)_\d+$', '', m)
    m = re.sub(r'\._simp_\d+(_\d+)*$', '', m)
    if m.startswith('_private.'):
        q = m.split('.0.', 1)
        if len(q) == 2:
            m = q[1]
    return m

attrib = None
if a.edits and a.decls:
    mod_of = {}
    with open(a.decls) as f:
        r = csv.reader(f, delimiter='\t'); next(r)
        for row in r:
            mod_of[row[1]] = row[0]
    owners_of = collections.defaultdict(set)
    for e in a.edits:
        for ln in open(e, encoding='utf-8'):
            p = ln.split('\t', 5)
            if len(p) >= 5:
                owners_of[p[0]].add(p[4])
    attrib = collections.Counter()
    for row in csv.reader(open(os.path.join(a.out, 'diff.tsv')), delimiter='\t'):
        if row[0] in ('status',) or row[0] == 'identical':
            continue
        st, name = row[0], row[1]
        mod = mod_of.get(name) or mod_of.get(parent(name))
        own = ','.join(sorted(owners_of.get(mod, ()))) if mod else '(no source decl)'
        attrib[(st, own or '(module not edited)')] += 1

with open(os.path.join(a.out, 'evidence.md'), 'w') as f:
    f.write(f"### export-level evidence: `{os.path.basename(a.new)}` vs `{os.path.basename(a.orig)}`\n\n")
    f.write('| quantity | original | candidate |\n|---|---|---|\n')
    for k in ('file_bytes', 'decls', 'closure_decls', 'closure_global_dag', 'closure_sum_decl_dag'):
        f.write(f"| {k} | {kv.get('old.' + k, '?')} | {kv.get('new.' + k, '?')} |\n")
    f.write('\n| status (per declaration of the original closure) | count |\n|---|---|\n')
    for k, v in status.items():
        f.write(f'| {k} | {v} |\n')
    f.write(f'\n**{result}**' + (f" ({len(changed_stmt)}: {', '.join(changed_stmt[:10])})" if changed_stmt else '') + '\n')
    if attrib is not None:
        f.write('\n| status | owners editing the declaration\'s module | count |\n|---|---|---|\n')
        for (st, own), c in sorted(attrib.items(), key=lambda x: -x[1]):
            f.write(f'| {st} | {own} | {c} |\n')
print(open(os.path.join(a.out, 'evidence.md')).read())
