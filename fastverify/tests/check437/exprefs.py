#!/usr/bin/python3 -I
"""exprefs.py EXPORT NAME HIDEFILE [--depth N] - diagnostic: which hide-listed definitions does declaration NAME reference
(directly in its type+value, and transitively through the VALUES of hide-listed definitions, up to depth N, default 3)?
Reads a lean4export 3.x JSON-lines file (names {"in":i,"str":{"pre":p,"str":s}} / {"in":i,"num":{...}}, expressions
{"ie":i, app|lam|forallE|letE|const|proj|sort|bvar|lit|mdata}, declarations {"thm"|"def"|"opaque"|"axiom"|"inductive"|"quot": ...}).
Pure diagnostics for the encapsulated-replay availability work; no verdicts."""
import sys, json
E, NAME, HF = sys.argv[1], sys.argv[2], sys.argv[3]
depth = int(sys.argv[sys.argv.index("--depth") + 1]) if "--depth" in sys.argv else 3
hide = set(l.strip() for l in open(HF) if l.strip())
names = {0: ""}; econst = {}; echildren = {}
decl_val = {}; decl_kind = {}
with open(E, "rb") as f:
    for raw in f:
        if raw.startswith(b'{"meta"'): continue
        o = json.loads(raw)
        if "in" in o:
            i = o["in"]
            d = o.get("str") or o.get("num") or next((v for k, v in o.items() if k != "in" and isinstance(v, dict)), {})
            p = d.get("pre", 0); s = str(d.get("str", d.get("num", d.get("i", "?"))))
            names[i] = (names[p] + "." if p else "") + s
        elif "ie" in o:
            i = o["ie"]
            if "app" in o: echildren[i] = (o["app"]["fn"], o["app"]["arg"])
            elif "lam" in o: echildren[i] = (o["lam"]["type"], o["lam"]["body"])
            elif "forallE" in o: echildren[i] = (o["forallE"]["type"], o["forallE"]["body"])
            elif "letE" in o: echildren[i] = (o["letE"]["type"], o["letE"]["value"], o["letE"]["body"])
            elif "const" in o: econst[i] = o["const"]["name"]; echildren[i] = ()
            elif "proj" in o: echildren[i] = (o["proj"]["struct"],)
            elif "mdata" in o: echildren[i] = (o["mdata"]["expr"],) if isinstance(o["mdata"], dict) and "expr" in o["mdata"] else ()
            else: echildren[i] = ()
        elif "il" in o: pass
        else:
            k = next(iter(o)); d = o[k]
            if k in ("thm", "def", "opaque"):
                decl_kind[d["name"]] = k; decl_val[d["name"]] = (d["type"], d["value"])
            elif k == "axiom": decl_kind[d["name"]] = k
            elif k == "inductive":
                for t in d["types"]: decl_kind[t["name"]] = "ind"
                for c in d["ctors"]: decl_kind[c["name"]] = "ctor"
                for r in d["recs"]: decl_kind[r["name"]] = "rec"
            elif k == "quot": decl_kind[d["name"]] = k
byname = {v: k for k, v in names.items()}
def refs(eidx):
    seen = set(); out = set(); st = [eidx]
    while st:
        e = st.pop()
        if e in seen: continue
        seen.add(e)
        if e in econst: out.add(econst[e])
        st.extend(echildren.get(e, ()))
    return out
if NAME not in byname or byname[NAME] not in decl_val:
    print("declaration not found or has no value:", NAME); sys.exit(1)
n0 = byname[NAME]
print(f"{NAME}: kind {decl_kind[n0]}; export has {len(decl_kind)} declarations, {sum(1 for n in decl_kind if names.get(n) in hide)} of them hide-listed")
level = {n0}; done = {n0}
for d in range(1, depth + 1):
    nxt = set()
    for n in level:
        if n not in decl_val: continue
        r = refs(decl_val[n][1]) | (refs(decl_val[n][0]) if d == 1 else set())
        for c in r:
            if names.get(c, "?") in hide and c not in done: nxt.add(c)
    done |= nxt
    print(f"depth {d}: {len(nxt)} hide-listed definition(s) referenced" + (f" by the {len(level)} of depth {d-1}" if d > 1 else " directly (type+value)"))
    for c in sorted(nxt, key=lambda c: names[c])[:60]: print("   ", names[c], decl_kind.get(c, "?"))
    if len(nxt) > 60: print("    ...")
    level = nxt
    if not level: break
