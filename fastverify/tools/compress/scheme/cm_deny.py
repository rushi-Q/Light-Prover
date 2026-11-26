#!/usr/bin/env python3
"""cm_deny.py PRE_MERGE_SRC CHAINMERGE_TSV OUT_DENY -- kept modules of a chain-merge plan whose group (members + kept
module) declares the same short name in two modules with at least one of them `private`: after the merge both live in one
module ('private declaration `X` has already been declared', 8 groups in the full-RH C1 build). Namespaces are ignored
(conservative). OUT_DENY feeds `chainmerge.py --deny`."""
import collections, os, re, sys
src, plan, out = sys.argv[1:4]
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?((?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*)"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|alias|irreducible_def)\s+([^\s:(\[{]+)")
groups = collections.defaultdict(list)
for ln in open(plan):
    x, k = ln.split()
    groups[k].append(x)
deny = []
for k, mem in groups.items():
    seen = collections.defaultdict(list)
    for m in mem + [k]:
        try: L = open(os.path.join(src, m.replace('.', '/') + '.lean'), encoding='utf-8').read().split('\n')
        except OSError: continue
        for l in L:
            mo = DECL.match(l)
            if mo:
                seen[mo.group(2).split('.')[-1]].append((m, 'private' in mo.group(1)))
    bad = [n for n, v in seen.items() if len({m for m, _ in v}) > 1 and any(p for _, p in v)]
    if bad: deny.append((k, bad[0]))
with open(out, 'w') as f:
    for k, n in deny: f.write(f'{k}\n')
print(f'groups {len(groups)} denied {len(deny)}', deny[:5])
