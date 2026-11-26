#!/usr/bin/env python3
"""liveedits.py INDEX.pkl IN.tsv OUT.tsv [DEPS.jsonl] — keep only edits that lie inside a declaration that is LIVE (in
the closure of the challenge targets) according to the pruning index rh-index.pkl (ranges per module: (name, l0, c0, l1, c1),
live = set of names), so that an edit never blocks the pruner's deletion of a dead declaration. With DEPS (apply.py's
`--edits FILE` writes FILE.deps: the new PROJECT constants each replacement proof uses that the replaced proof did not),
an edit is also dropped when such a dependency is a project declaration that is NOT live (pruning could delete it:
automated closers find @[simp]/@[grind] lemmas implicitly), or when its dependencies are unknown (older runs)
unless --unknown-deps-ok."""
import json, pickle, re, sys
idx = pickle.load(open(sys.argv[1], "rb"))
live, ranges = idx["live"], idx["ranges"]
proj = set(n for cs in idx["consts"].values() for n, t in cs)
deps = {}
if len(sys.argv) > 4 and not sys.argv[4].startswith("--"):
    for l in open(sys.argv[4]):
        r = json.loads(l)
        deps[(r["module"], r["l0"], r["l1"])] = r["deps"]
unknown_ok = "--unknown-deps-ok" in sys.argv
AUX = re.compile(r"^(_.*|eq_\d+|eq_def|match_\d+|proof_\d+|congr_simp|else_eq|sizeOf_spec|inj|injEq)$")


def base(n):
    parts = n.split(".")
    while len(parts) > 1 and AUX.match(parts[-1]):
        parts.pop()
    return ".".join(parts)


kept = dropped = nodecl = baddep = unk = 0
out = open(sys.argv[3], "w")
for line in open(sys.argv[2]):
    f = line.rstrip("\n").split("\t")
    mod = f[0][:-5].replace("/", ".") if f[0].endswith(".lean") else f[0]
    l0, l1 = int(f[1]), int(f[2])
    enc = [r for r in ranges.get(mod, []) if r[1] <= l0 and l1 <= r[3]]
    if not enc:
        nodecl += 1; continue
    name = min(enc, key=lambda r: r[3] - r[1])[0]
    if name not in live:
        dropped += 1; continue
    if deps or not unknown_ok:
        d = deps.get((f[0], l0, l1))
        if d is None:
            if not unknown_ok:
                unk += 1; continue
        elif any(base(x) in proj and base(x) not in live for x in d):
            baddep += 1; continue
    out.write(line); kept += 1
print(f"kept {kept}, dropped: dead decl {dropped}, no enclosing decl {nodecl}, non-live new dependency {baddep}, unknown deps {unk}")
