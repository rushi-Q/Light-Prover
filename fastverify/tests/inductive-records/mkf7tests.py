#!/usr/bin/env python3
"""crafted exports from the SegSol sol.export (SegSol: inductive MyB | t | f; def sel (b : MyB) (X Y : Type) : Type :=
MyB.rec X Y b; inductive U | mk : sel MyB.t Nat Bool -> U; theorem goal : True).
usage: mkf7tests.py SOL_EXPORT OUTDIR
  f7_selfloop.export   : sel := sel (its value is the constant `sel` itself; the def record moved to the end of the file so
                         that the expression is defined before it). sel's own kernel check fails (unknown constant `sel`);
                         U's inductive check in a snapshot holding the unchecked sel would unfold sel forever: liveness of the
                         phase-1 per-call budget and of the walk's cancel token. Official: REJECTED.
  f7_taken_rec.export  : MyB's recursor record replaced by a safe definition named `MyB.rec` (= the recursor the kernel
                         generates for MyB). Official: REJECTED ("already declared", in either walk order).
"""
import json, sys, os
src, out = sys.argv[1], sys.argv[2]
L = open(src, encoding="utf-8").read().split("\n")
os.makedirs(out, exist_ok=True)
names = {}
for ln in L[1:]:
    if ln.startswith('{"in"'):
        o = json.loads(ln)
        if "str" in o: names[o["in"]] = (o["str"]["pre"], o["str"]["str"])
        elif "num" in o: names[o["in"]] = (o["num"]["pre"], str(o["num"]["i"]))
def nm(i):
    s = []
    while i: p, c = names[i]; s.append(c); i = p
    return ".".join(reversed(s))
nid = {nm(i): i for i in names}
sel, rec, ctor = nid["sel"], nid["MyB.rec"], nid["MyB.t"]
def defline(name):
    for k, ln in enumerate(L):
        if ln.startswith('{"def"') and json.loads(ln)["def"]["name"] == name: return k
    raise SystemExit("no def %s" % name)
cexpr = None
for ln in L:
    if ln.startswith('{"const"'):
        o = json.loads(ln)
        if o["const"]["name"] == sel and o["const"]["us"] == []: cexpr = o["ie"]; break
assert cexpr is not None
def write(fn, lines):
    open(os.path.join(out, fn), "w", encoding="utf-8").write("\n".join(lines)); print(fn)
# self loop
k = defline(sel); o = json.loads(L[k]); o["def"]["value"] = cexpr
M = L[:k] + L[k+1:]
while M and M[-1] == "": M.pop()
write("f7_selfloop.export", M + [json.dumps(o, separators=(",", ":")), ""])
# taken name: MyB's recursor record removed from its block (the export parser refuses two records of one name) and a copy of
# sel's def record (type/value well-formed) added under the name `MyB.rec`
o = json.loads(L[defline(sel)]); o["def"]["name"] = rec; o["def"]["all"] = [rec]
M = list(L)
for k, ln in enumerate(M):
    if ln.startswith('{"inductive"'):
        b = json.loads(ln)
        if any(r["name"] == rec for r in b["inductive"]["recs"]):
            b["inductive"]["recs"] = [r for r in b["inductive"]["recs"] if r["name"] != rec]
            M[k] = json.dumps(b, separators=(",", ":"))
while M and M[-1] == "": M.pop()
write("f7_taken_rec.export", M + [json.dumps(o, separators=(",", ":")), ""])
