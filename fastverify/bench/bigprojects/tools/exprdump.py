#!/usr/bin/python3 -I
"""exprdump.py EXPORT NAME : print the type of declaration NAME of a lean4export 3.x NDJSON export as a canonical
s-expression (binder names dropped, binder info kept as a tag, constants with universe levels), one subterm per line
(indented), plus the declaration's level params and kind - for diffing why compareAt rejects a statement."""
import json, sys
path, target = sys.argv[1], sys.argv[2]
names, levels, exprs = {0: ""}, {}, {}
decl = None
def nm(i):
    return names[i]
with open(path) as f:
    for ln in f:
        o = json.loads(ln)
        if "in" in o:
            s = o["str"] if "str" in o else o.get("num")
            if "str" in o:
                p = nm(o["str"]["pre"]); names[o["in"]] = (p + "." if p else "") + o["str"]["str"]
            else:
                p = nm(o["num"]["pre"]); names[o["in"]] = (p + "." if p else "") + str(o["num"]["i"])
        elif "il" in o:
            levels[o["il"]] = o
        elif "ie" in o:
            exprs[o["ie"]] = o
        else:
            for k in ("thm", "def", "axiom", "opaque"):
                if k in o and nm(o[k]["name"]) == target:
                    decl = (k, o[k])
def lv(i):
    if i == 0: return "0"
    o = levels[i]
    if "succ" in o: return "(succ %s)" % lv(o["succ"])
    if "max" in o: return "(max %s %s)" % tuple(lv(x) for x in o["max"])
    if "imax" in o: return "(imax %s %s)" % tuple(lv(x) for x in o["imax"])
    if "param" in o: return nm(o["param"])
    return str(o)
out = []
def ex(i, d=0):
    o = exprs[i]; pad = "  " * d
    if "bvar" in o: out.append(pad + "#%d" % o["bvar"]); return
    if "sort" in o: out.append(pad + "Sort " + lv(o["sort"])); return
    if "const" in o:
        c = o["const"]; out.append(pad + nm(c["name"]) + ".{" + ",".join(lv(u) for u in c["us"]) + "}"); return
    if "app" in o:
        out.append(pad + "app"); ex(o["app"]["fn"], d + 1); ex(o["app"]["arg"], d + 1); return
    for k in ("lam", "forallE"):
        if k in o:
            b = o[k]; out.append(pad + k + "[" + b.get("binderInfo", "") + "]"); ex(b["type"], d + 1); ex(b["body"], d + 1); return
    if "letE" in o:
        b = o["letE"]; out.append(pad + "let"); ex(b["type"], d + 1); ex(b["value"], d + 1); ex(b["body"], d + 1); return
    if "natVal" in o: out.append(pad + "nat " + str(o["natVal"])); return
    if "strVal" in o: out.append(pad + "str " + json.dumps(o["strVal"])); return
    if "mdata" in o: out.append(pad + "mdata " + json.dumps(o["mdata"].get("data"))[:80]); ex(o["mdata"]["expr"], d + 1); return
    if "proj" in o: out.append(pad + "proj " + nm(o["proj"]["typeName"]) + " " + str(o["proj"]["idx"])); ex(o["proj"]["struct"], d + 1); return
    out.append(pad + "?" + json.dumps(o)[:100])
if not decl:
    sys.exit("not found: " + target)
k, b = decl
print("kind", k, "levelParams", [nm(x) for x in b.get("levelParams", [])])
ex(b["type"])
print("\n".join(out))
