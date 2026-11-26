#!/usr/bin/env python3
"""blockdup.py SRC THMS.jsonl OUT_PREFIX — repeated proof text: (1) identical whole tactic proofs (whitespace-normalized)
across theorems, (2) repeated windows of K consecutive proof lines (dedented), as candidates for named lemmas/macros."""
import json, sys, collections, hashlib, os
src, thf, outp = sys.argv[1:4]
K = 4
whole = collections.defaultdict(list)
win = collections.Counter()
winex = {}
byfile = collections.defaultdict(list)
for l in open(thf):
    r = json.loads(l)
    if r.get("kind") == "by" and r.get("plines", 0) >= 3:
        byfile[r["file"]].append(r)
nproof = 0; nlines = 0
for f, rs in byfile.items():
    try:
        lines = open(os.path.join(src, f), encoding="utf-8").read().split("\n")
    except Exception:
        continue
    for r in rs:
        body = lines[r["al"]:r["l1"]]  # lines after the ':=' line
        body = [b for b in body if b.strip()]
        if len(body) < 2: continue
        ind = min(len(b) - len(b.lstrip()) for b in body)
        norm = [b[ind:].rstrip() for b in body]
        nproof += 1; nlines += len(norm)
        h = hashlib.md5("\n".join(norm).encode()).hexdigest()
        whole[h].append((f, r["name"], len(norm)))
        for i in range(len(norm) - K + 1):
            w = norm[i:i + K]
            i0 = min(len(x) - len(x.lstrip()) for x in w)
            key = "\n".join(x[i0:] for x in w)
            win[key] += 1
dup = [(v[0][2], len(v)) for v in whole.values() if len(v) > 1]
saved = sum(L * (n - 1) for L, n in dup)
print(f"tactic proofs >=2 body lines: {nproof}, body lines {nlines}")
print(f"identical whole proofs: {len(dup)} classes, {sum(n for _, n in dup)} proofs, removable body lines if shared: {saved}")
top = win.most_common(40)
rep = sum(c for k, c in win.items() if c >= 50)
print(f"{K}-line windows occurring >=50 times: {sum(1 for c in win.values() if c >= 50)} distinct, {rep} occurrences")
with open(outp + ".windows.txt", "w") as o:
    for k, c in win.most_common(300):
        o.write(f"=== {c}\n{k}\n")
with open(outp + ".whole.txt", "w") as o:
    for v in sorted(whole.values(), key=lambda v: -v[0][2] * (len(v) - 1))[:300]:
        if len(v) > 1: o.write(f"{len(v)} x {v[0][2]} lines: {v[0][0]} {v[0][1]} | {v[1][0]} {v[1][1]}\n")
