#!/usr/bin/python3 -I
"""mk_natadd_bogus.py SELFTEST_GOOD_EXPORT OUT : a SMALL snapshot export with a kernel-valid WRONG Nat.add (value := Nat.sub's
value, same type) - the input of the 'NatAddBogus' incremental cases (the original small export is gone): the closure of
Nat.add and Nat.sub in the self-test export (every index line kept; only the needed declarations, all at the end)."""
import json, sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src, encoding="utf-8").read().splitlines()
names = {0: ()}; econsts = {}; decls = {}; order = []
def ecs(i):
    return econsts.get(i, set())
for l in lines[1:]:
    o = json.loads(l)
    if "in" in o:
        names[o["in"]] = names[o["str"]["pre"]] + (o["str"]["str"],) if "str" in o else names[o["num"]["pre"]] + (str(o["num"]["i"]),)
    elif "ie" in o:
        s = set()
        for k, v in o.items():
            if k == "ie": continue
            if k == "const": s.add(v["name"])
            elif isinstance(v, dict):
                for kk in ("fn", "arg", "type", "body", "value", "struct", "expr"):
                    if kk in v and isinstance(v[kk], int): s |= ecs(v[kk])
                if k == "proj": s.add(v["typeName"])
        econsts[o["ie"]] = s
    else:
        for k in ("def", "thm", "axiom", "opaque", "quot"):
            if k in o:
                d = o[k]; refs = ecs(d["type"]) | (ecs(d["value"]) if "value" in d else set())
                decls[d["name"]] = (l, refs, [d["name"]]); order.append(d["name"])
        if "inductive" in o:
            b = o["inductive"]; refs = set(); members = []
            for t in b["types"]: refs |= ecs(t["type"]); members.append(t["name"])
            for c in b["ctors"]: refs |= ecs(c["type"]); members.append(c["name"])
            for r in b["recs"]: members.append(r["name"])
            for m in members: decls[m] = (l, refs, members)
            order.append(members[0])
byname = {".".join(v): k for k, v in names.items()}
nadd, nsub = byname["Nat.add"], byname["Nat.sub"]
need, stack = set(), [nadd, nsub]
while stack:
    n = stack.pop()
    if n in need or n not in decls: continue
    l, refs, members = decls[n]
    for m in members: need.add(m)
    stack.extend(refs)
subval = json.loads(decls[nsub][0])["def"]["value"]
out = [lines[0]] + [l for l in lines[1:] if any(k in json.loads(l) for k in ("in", "il", "ie"))]
seen = set()
for n in order:
    if n not in need: continue
    l = decls[n][0]
    if l in seen: continue
    seen.add(l)
    o = json.loads(l)
    if "def" in o and o["def"]["name"] == nadd:
        o["def"]["value"] = subval; l = json.dumps(o, separators=(",", ":"))
    out.append(l)
open(dst, "w", encoding="utf-8").write("\n".join(out) + "\n")
print(f"{len(seen)} declaration lines kept (closure of Nat.add, Nat.sub)")
