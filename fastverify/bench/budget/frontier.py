#!/usr/bin/python3 -I
"""frontier.py EXPORT --targets NAME... [--permitted propext,Quot.sound,Classical.choice] [--json OUT]

Sorry-frontier LEDGER of a lean4export (format 3.1.0, JSON lines) - an UNTRUSTED analysis for projects in development, never
a verdict: which declarations the targets depend on that are still proved by `sorry` (sorryAx), which of them are clean
"frontier" lemmas (a theorem whose whole proof is one sorryAx application: the statement is the only thing the lemma
contributes), which are partial proofs (sorry somewhere inside a real proof), which are NOT theorems (a sorried def /
instance / structure field: a conditional verdict must refuse those - a definition's body matters), and which axioms
other than the permitted ones occur in the targets' closure.

Output (JSON): {"targets": [...], "closure_size": N, "frontier": [{"name", "kind": "pure-sorry"|"partial"}, ...],
"sorried_non_theorems": [...], "axioms": {name: count-of-closure-decls-using-it}, "unknown_targets": [...],
"stats": {...}}  and a one-line summary on stderr.

Memory: one Python list per table; the full RH export (61.6 GB) does not fit - use it on project-size exports
(<= a few GB). Linear in the export size; a 1 GB export takes ~1-2 min."""
import json, sys, time

def main():
    a = sys.argv[1:]
    if not a or a[0] in ("-h", "--help"):
        print(__doc__); return 2
    path = a[0]; targets = []; permitted = {"propext", "Quot.sound", "Classical.choice"}; out = None
    i = 1
    while i < len(a):
        if a[i] == "--targets":
            i += 1
            while i < len(a) and not a[i].startswith("--"):
                targets.append(a[i]); i += 1
        elif a[i] == "--permitted":
            permitted = set(a[i + 1].split(",")); i += 2
        elif a[i] == "--json":
            out = a[i + 1]; i += 2
        else:
            print("unknown argument", a[i]); return 2
    t0 = time.time()
    names = [""]          # name index -> string
    exprs = [None]        # expr index -> (kind, children tuple, const name index or None)
    decls = {}            # name -> dict(kind, type, value, extra exprs)
    SORRY = None
    with open(path, "rb") as f:
        for ln in f:
            if not ln.startswith(b"{"):
                continue
            r = json.loads(ln)
            if "in" in r:
                idx = r["in"]
                if "str" in r:
                    pre = names[r["str"]["pre"]]
                    s = r["str"]["str"]
                    nm = s if not pre else pre + "." + s
                else:
                    pre = names[r["num"]["pre"]]
                    nm = (pre + "." if pre else "") + str(r["num"]["i"])
                if idx >= len(names):
                    names.extend([""] * (idx + 1 - len(names)))
                names[idx] = nm
                if nm == "sorryAx":
                    SORRY = idx
                continue
            if "ie" in r:
                idx = r["ie"]
                if idx >= len(exprs):
                    exprs.extend([None] * (idx + 1 - len(exprs)))
                if "const" in r:
                    exprs[idx] = ("const", (), r["const"]["name"])
                elif "app" in r:
                    exprs[idx] = ("app", (r["app"]["fn"], r["app"]["arg"]), None)
                elif "lam" in r:
                    exprs[idx] = ("lam", (r["lam"]["type"], r["lam"]["body"]), None)
                elif "forallE" in r:
                    exprs[idx] = ("pi", (r["forallE"]["type"], r["forallE"]["body"]), None)
                elif "letE" in r:
                    exprs[idx] = ("let", (r["letE"]["type"], r["letE"]["value"], r["letE"]["body"]), None)
                elif "proj" in r:
                    exprs[idx] = ("proj", (r["proj"]["struct"],), r["proj"]["typeName"])
                elif "mdata" in r:
                    exprs[idx] = ("mdata", (r["mdata"]["expr"],), None)
                else:
                    exprs[idx] = ("leaf", (), None)
                continue
            if "il" in r:
                continue
            if "thm" in r:
                d = r["thm"]; decls[names[d["name"]]] = {"kind": "thm", "type": d["type"], "value": d["value"]}
            elif "def" in r:
                d = r["def"]; decls[names[d["name"]]] = {"kind": "def" if d.get("hints") != "opaque" else "opaque",
                                                          "type": d["type"], "value": d["value"]}
            elif "axiom" in r:
                d = r["axiom"]; decls[names[d["name"]]] = {"kind": "axiom", "type": d["type"], "value": None}
            elif "opaque" in r:
                d = r["opaque"]; decls[names[d["name"]]] = {"kind": "opaque", "type": d["type"], "value": d.get("value")}
            elif "quot" in r:
                d = r["quot"]; decls[names[d["name"]]] = {"kind": "quot", "type": d["type"], "value": None}
            elif "inductive" in r:
                d = r["inductive"]
                for ind in d.get("types", []) or []:
                    decls[names[ind["name"]]] = {"kind": "inductive", "type": ind["type"], "value": None}
                for c in d.get("ctors", []):
                    decls[names[c["name"]]] = {"kind": "ctor", "type": c["type"], "value": None}
                for rc in d.get("recs", []):
                    rules = [ru["rhs"] for ru in rc.get("rules", [])]
                    decls[names[rc["name"]]] = {"kind": "rec", "type": rc["type"], "value": None, "extra": rules}
    t1 = time.time()
    # pass 2: per declaration, the constants it references (DFS over its expression DAG, visited stamped per decl)
    nE = len(exprs)
    stamp = [0] * nE
    def refs(roots, mark):
        res = set(); st = list(r for r in roots if r is not None)
        while st:
            e = st.pop()
            if e is None or stamp[e] == mark:
                continue
            stamp[e] = mark
            x = exprs[e]
            if x is None:
                continue
            kind, ch, c = x
            if c is not None and kind == "const":
                res.add(c)
            st.extend(ch)
        return res
    name_of = {}
    for nm in decls:
        pass
    deps = {}  # name -> set of names
    mark = 0
    for nm, d in decls.items():
        mark += 1
        rs = refs([d["type"], d["value"]] + list(d.get("extra", [])), mark)
        deps[nm] = {names[c] for c in rs}
    # direct sorry: value references sorryAx at all; pure sorry: value is `sorryAx T synthetic` = app(app(const sorryAx, T), b)
    def value_is_pure_sorry(v):
        x = exprs[v] if v is not None and v < nE else None
        while x and x[0] == "app":
            fn = x[1][0]; x = exprs[fn]
        return bool(x and x[0] == "const" and names[x[2]] == "sorryAx")
    # pass 3: closure of the targets over deps
    unknown = [t for t in targets if t not in decls]
    seen = set(); missing = set(); st = [t for t in targets if t in decls]
    while st:
        n = st.pop()
        if n in seen:
            continue
        if n not in decls:          # referenced but not declared (never in a real closure export; tolerated)
            missing.add(n); continue
        seen.add(n)
        st.extend(deps.get(n, ()))
    frontier = []; sorried_non_thm = []; axioms = {}
    for n in seen:
        d = decls[n]
        if d["kind"] == "axiom":
            axioms[n] = axioms.get(n, 0)
        if "sorryAx" in deps.get(n, ()) and n != "sorryAx":
            if d["kind"] == "thm":
                frontier.append({"name": n, "kind": "pure-sorry" if value_is_pure_sorry(d["value"]) else "partial"})
            else:
                sorried_non_thm.append({"name": n, "kind": d["kind"]})
    for n in seen:
        for dd in deps.get(n, ()):
            if dd in axioms:
                axioms[dd] += 1
    extra_axioms = {k: v for k, v in axioms.items() if k not in permitted}
    frontier.sort(key=lambda x: x["name"]); sorried_non_thm.sort(key=lambda x: x["name"])
    res = {"export": path, "targets": targets, "unknown_targets": unknown, "closure_size": len(seen),
           "missing_constants": sorted(missing),
           "frontier": frontier, "sorried_non_theorems": sorried_non_thm, "axioms": axioms, "extra_axioms": extra_axioms,
           "stats": {"declarations": len(decls), "exprs": nE, "names": len(names), "parse_s": round(t1 - t0, 1),
                     "analysis_s": round(time.time() - t1, 1),
                     "frontier_pure": sum(1 for x in frontier if x["kind"] == "pure-sorry"),
                     "frontier_partial": sum(1 for x in frontier if x["kind"] == "partial")}}
    js = json.dumps(res, indent=1)
    if out:
        open(out, "w").write(js)
    print(js)
    print(f"[frontier] closure {len(seen)} decls; frontier {len(frontier)} theorems ({res['stats']['frontier_pure']} pure "
          f"sorry, {res['stats']['frontier_partial']} partial); sorried non-theorems {len(sorried_non_thm)}; extra axioms "
          f"{sorted(extra_axioms)}; unknown targets {unknown}; {round(time.time() - t0, 1)} s", file=sys.stderr)
    return 0

if __name__ == "__main__":
    sys.exit(main())
