#!/usr/bin/python3 -I
"""mkfrontier.py EXPORT CONFIG OUT K [--seed S] [--names FILE] : make a big "development with K open lemmas" export
from a finished one (frontier scaling benchmark). K non-target theorems of the export get the canonical value
`sorryAx.{0} T Bool.false` (T = their type), exactly what `theorem L : T := sorry` elaborates to in Lean 4.33; if the
export has no `sorryAx`, the official 4.33 declaration `axiom sorryAx.{u} (α : Sort u) (synthetic : Bool) : α` is
added. Streaming, two passes; new index lines are appended after the last original index line and every declaration
line from the first changed one on is moved behind them (relative order kept).
The chosen names are written to OUT.names (one per line)."""
import json
import random
import sys


def main(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("export")
    ap.add_argument("config")
    ap.add_argument("out")
    ap.add_argument("k", type=int)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--exclude-export", help="never choose a name declared in this export (e.g. the challenge)")
    ap.add_argument("--prefix", help="only choose names starting with this prefix")
    a = ap.parse_args(argv)
    cfg = json.load(open(a.config))
    targets = set(cfg["theorem_names"]) | set(cfg.get("definition_names") or [])
    names = [None]
    nlev = 1
    nexp = 0
    lev_param = {}
    thms = []          # (line number, name idx)
    sorry_name = None
    first_decl = None
    DECL = (b'{"thm"', b'{"def"', b'{"axiom"', b'{"inductive"', b'{"opaque"', b'{"quot"')
    with open(a.export, "rb") as f:
        for ln, raw in enumerate(f):
            if ln == 0:
                continue
            if raw.startswith(b'{"in"'):
                o = json.loads(raw)
                d = o.get("str") or o.get("num")
                names.append((d["pre"], d.get("str", d.get("i"))))
                if d["pre"] == 0 and d.get("str") == "sorryAx":
                    sorry_name = o["in"]
            elif raw.startswith(b'{"il"'):
                o = json.loads(raw)
                nlev = max(nlev, o["il"] + 1)
                if "param" in o:
                    lev_param.setdefault(o["param"], o["il"])
            elif raw.startswith(DECL):
                if first_decl is None:
                    first_decl = ln
                if raw.startswith(b'{"thm"'):
                    o = json.loads(raw)["thm"]
                    thms.append((ln, o["name"]))
            else:
                nexp += 1

    def nstr(i):
        out = []
        while i:
            pre, s = names[i]
            out.append(str(s))
            i = pre
        return ".".join(reversed(out))

    def find_name(full):
        for i in range(1, len(names)):
            if nstr(i) == full:
                return i
        return None

    excl = set()
    if a.exclude_export:
        cn = {0: ""}
        for raw in open(a.exclude_export, "rb"):
            if raw.startswith(b'{"in"'):
                o = json.loads(raw); d = o.get("str") or o.get("num")
                cn[o["in"]] = (cn[d["pre"]] + "." if d["pre"] else "") + str(d.get("str", d.get("i")))
            elif raw.startswith((b'{"thm"', b'{"def"', b'{"axiom"', b'{"opaque"')):
                o = json.loads(raw); excl.add(cn[next(iter(o.values()))["name"]])
    cands = [(ln, ni) for ln, ni in thms if nstr(ni) not in targets and nstr(ni) not in excl
             and (not a.prefix or any(nstr(ni).startswith(p) for p in a.prefix.split(",")))]
    random.Random(a.seed).shuffle(cands)
    chosen = dict(cands[:a.k])        # line number -> name idx
    new = []
    nn = len(names)

    def add_name(pre, s):
        nonlocal nn
        new.append({"in": nn, "str": {"pre": pre, "str": s}})
        names.append((pre, s))
        nn += 1
        return nn - 1

    def add_expr(kind, data):
        nonlocal nexp
        new.append({kind: data, "ie": nexp})
        nexp += 1
        return nexp - 1

    bool_n = find_name("Bool")
    bfalse_n = find_name("Bool.false")
    assert bool_n and bfalse_n, "export lacks Bool / Bool.false"
    extra_decls = []
    if sorry_name is None:
        sorry_name = add_name(0, "sorryAx")
        u = find_name("u") or add_name(0, "u")
        if u in lev_param:
            lu = lev_param[u]
        else:
            new.append({"il": nlev, "param": u})
            lu = nlev
            nlev += 1
        alpha = find_name("α") or add_name(0, "α")
        syn = find_name("synthetic") or add_name(0, "synthetic")
        s_u = add_expr("sort", lu)
        boolc = add_expr("const", {"name": bool_n, "us": []})
        b1 = add_expr("bvar", 1)
        inner = add_expr("forallE", {"binderInfo": "default", "body": b1, "name": syn, "type": boolc})
        ty = add_expr("forallE", {"binderInfo": "default", "body": inner, "name": alpha, "type": s_u})
        extra_decls.append({"axiom": {"isUnsafe": False, "levelParams": [u], "name": sorry_name, "type": ty}})
    sc = add_expr("const", {"name": sorry_name, "us": [0]})
    bf = add_expr("const", {"name": bfalse_n, "us": []})
    dump = lambda o: (json.dumps(o, separators=(",", ":"), sort_keys=True, ensure_ascii=False) + "\n").encode()
    # the added sorryAx declaration goes right before the first chosen theorem (after every original declaration that
    # precedes it, e.g. Bool's): kernels that read declarations in file order (gruszka) need dependencies first
    cut = min(chosen) if chosen else None
    buf = []
    with open(a.export, "rb") as f, open(a.out, "wb") as g:
        for ln, raw in enumerate(f):
            isdecl = raw.startswith((b'{"thm"', b'{"def"', b'{"axiom"', b'{"inductive"', b'{"opaque"', b'{"quot"'))
            if cut is not None and ln >= cut and isdecl:
                if ln in chosen:
                    o = json.loads(raw)["thm"]
                    v = add_expr("app", {"fn": add_expr("app", {"fn": sc, "arg": o["type"]}), "arg": bf})
                    buf.append(dump({"thm": dict(o, value=v)}))
                else:
                    buf.append(raw)
            else:
                g.write(raw)
        for o in new:
            g.write(dump(o))
        for o in extra_decls:
            g.write(dump(o))
        for b in buf:
            g.write(b)
    with open(a.out + ".names", "w") as h:
        for ln in sorted(chosen):
            h.write(nstr(chosen[ln]) + "\n")
    print(json.dumps({"k": len(chosen), "theorems": len(thms), "sorry_added": bool(extra_decls), "new_lines": len(new)}))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
