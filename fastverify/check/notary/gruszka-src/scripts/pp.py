# Pretty-prints the declarations of an ndjson export whose name contains ARG2.
import json, sys
names = {0: ""}; ex = {}; lv = {0: "0"}
for line in open(sys.argv[1]):
    o = json.loads(line)
    if "in" in o:
        if "str" in o: names[o["in"]] = (names[o["str"]["pre"]] + "." if o["str"]["pre"] else "") + o["str"]["str"]
        else: names[o["in"]] = names[o["num"]["pre"]] + "." + str(o["num"]["i"])
    elif "il" in o:
        k = [x for x in o if x != "il"][0]; v = o[k]
        lv[o["il"]] = {"succ": lambda: lv[v] + "+1", "max": lambda: "max(%s,%s)" % (lv[v[0]], lv[v[1]]), "imax": lambda: "imax(%s,%s)" % (lv[v[0]], lv[v[1]]), "param": lambda: names[v]}[k]()
    elif "ie" in o:
        ex[o["ie"]] = o
FUEL=[0]
def p(i, ctx):
    FUEL[0]+=1
    if FUEL[0] > 3000: return '…'
    o = ex[i]; k = [x for x in o if x != "ie"][0]; v = o[k]
    if k == "bvar": return ctx[-1 - v] if v < len(ctx) else "#%d" % v
    if k == "sort": return "Sort(%s)" % lv[v]
    if k == "const": return names[v["name"]] + (".{%s}" % ",".join(lv[u] for u in v["us"]) if v["us"] else "")
    if k == "app": return "(%s %s)" % (p(v["fn"], ctx), p(v["arg"], ctx))
    if k in ("lam", "forallE"):
        n = names[v["name"]] or "_"; n = n + "'" * ctx.count(n)
        return "(%s %s : %s, %s)" % ("fun" if k == "lam" else "Π", n, p(v["type"], ctx), p(v["body"], ctx + [n]))
    if k == "letE": n = names[v["name"]]; return "(let %s := %s; %s)" % (n, p(v["value"], ctx), p(v["body"], ctx + [n]))
    if k == "proj": return "%s.%d[%s]" % (p(v["struct"], ctx), v["idx"] + 1, names[v["typeName"]])
    if k in ("natVal", "strVal"): return repr(v)
    return str(o)
for line in open(sys.argv[1]):
    o = json.loads(line)
    for k in ("def", "thm", "axiom", "opaque"):
        if k in o and sys.argv[2] in names[o[k]["name"]]:
            FUEL[0]=0; print(k, names[o[k]["name"]], ":", p(o[k]["type"], []))
            FUEL[0]=0
            if "value" in o[k]: print("   :=", p(o[k]["value"], []))
