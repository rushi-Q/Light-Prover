#!/usr/bin/python3 -I
"""stmtdiff.py CHALLENGE.export SOLUTION.export NAME [NAME...] : explain a 'statement do not match' rejection.

For each declaration NAME, compares its kind, universe parameter names and type in the two lean4export 3.x NDJSON
exports the way the comparator's compareAt does (alpha-equivalence: binder names and binder info ignored) and prints the
FIRST difference: the path from the root of the type (e.g. forallE.body > app.arg > ...), both subterms (depth-limited
s-expressions) and the head constants around it. Diagnostics only (untrusted, not part of any verdict); typical causes
found on real projects: different instance terms (imports / module system), a different universe parameter NAME, a
numeral of another type (rpow vs npow). Exit 0 = all equal, 1 = some differ, 2 = a name is missing.
"""
import json, sys


def load(path, wanted):
    names, levels, exprs, decls = {0: ""}, {}, {}, {}
    with open(path) as f:
        for ln in f:
            o = json.loads(ln)
            if "in" in o:
                if "str" in o:
                    p = names[o["str"]["pre"]]; names[o["in"]] = (p + "." if p else "") + o["str"]["str"]
                else:
                    p = names[o["num"]["pre"]]; names[o["in"]] = (p + "." if p else "") + str(o["num"]["i"])
            elif "il" in o:
                levels[o["il"]] = o
            elif "ie" in o:
                exprs[o["ie"]] = o
            else:
                for k in ("thm", "def", "axiom", "opaque"):
                    if k in o and names.get(o[k]["name"]) in wanted:
                        decls[names[o[k]["name"]]] = (k, o[k])
    return names, levels, exprs, decls


class Ex:
    def __init__(self, path, wanted):
        self.names, self.levels, self.exprs, self.decls = load(path, wanted)

    def lv(self, i):
        if i == 0:
            return "0"
        o = self.levels[i]
        for k in ("succ",):
            if k in o:
                return "(succ %s)" % self.lv(o[k])
        for k in ("max", "imax"):
            if k in o:
                return "(%s %s %s)" % (k, self.lv(o[k][0]), self.lv(o[k][1]))
        return self.names[o["param"]] if "param" in o else str(o)

    def node(self, i):
        """(tag, label, children) with binder names / info dropped (compareAt uses Expr.eqv)"""
        o = self.exprs[i]
        if "bvar" in o:
            return ("bvar", str(o["bvar"]), [])
        if "sort" in o:
            return ("sort", self.lv(o["sort"]), [])
        if "const" in o:
            c = o["const"]
            return ("const", self.names[c["name"]] + ".{" + ",".join(self.lv(u) for u in c["us"]) + "}", [])
        if "app" in o:
            return ("app", "", [("fn", o["app"]["fn"]), ("arg", o["app"]["arg"])])
        for k in ("lam", "forallE"):
            if k in o:
                return (k, "", [("type", o[k]["type"]), ("body", o[k]["body"])])
        if "letE" in o:
            b = o["letE"]
            return ("letE", "", [("type", b["type"]), ("value", b["value"]), ("body", b["body"])])
        if "natVal" in o:
            return ("nat", str(o["natVal"]), [])
        if "strVal" in o:
            return ("str", json.dumps(o["strVal"]), [])
        if "mdata" in o:
            return ("mdata", "", [("expr", o["mdata"]["expr"])])
        if "proj" in o:
            return ("proj", self.names[o["proj"]["typeName"]] + "." + str(o["proj"]["idx"]), [("struct", o["proj"]["struct"])])
        return ("?", json.dumps(o)[:60], [])

    def show(self, i, depth=4):
        tag, lab, ch = self.node(i)
        if tag in ("const", "bvar", "sort", "nat", "str"):
            return lab if tag != "bvar" else "#" + lab
        if tag == "app":   # flatten the spine
            spine, j = [], i
            while self.node(j)[0] == "app":
                o = self.exprs[j]["app"]; spine.append(o["arg"]); j = o["fn"]
            if depth <= 0:
                return "(%s ...)" % self.show(j, 0)
            return "(" + " ".join([self.show(j, depth - 1)] + [self.show(a, depth - 1) for a in reversed(spine)]) + ")"
        if depth <= 0:
            return "(%s ...)" % tag
        return "(" + tag + (" " + lab if lab else "") + " " + " ".join(self.show(c, depth - 1) for _, c in ch) + ")"


def first_diff(A, a, B, b, path):
    na, nb = A.node(a), B.node(b)
    if na[0] != nb[0] or na[1] != nb[1] or len(na[2]) != len(nb[2]):
        return path, a, b
    for (fa, ca), (_, cb) in zip(na[2], nb[2]):
        r = first_diff(A, ca, B, cb, path + ["%s.%s" % (na[0], fa)])
        if r:
            return r
    return None


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    names = sys.argv[3:]
    A, B = Ex(sys.argv[1], set(names)), Ex(sys.argv[2], set(names))
    rc = 0
    for n in names:
        if n not in A.decls or n not in B.decls:
            print("%s: missing in %s" % (n, "challenge" if n not in A.decls else "solution")); rc = 2; continue
        (ka, da), (kb, db) = A.decls[n], B.decls[n]
        ua = [A.names[x] for x in da.get("levelParams", [])]; ub = [B.names[x] for x in db.get("levelParams", [])]
        if ua != ub:
            print("%s: universe parameter names differ: challenge %s vs solution %s (compareAt compares names)" % (n, ua, ub))
            rc = max(rc, 1)
        r = first_diff(A, da["type"], B, db["type"], [])
        if r is None:
            if ua == ub:
                print("%s: types equal (alpha), %s / %s" % (n, ka, kb))
            continue
        rc = max(rc, 1)
        path, a, b = r
        print("%s: first difference at %s" % (n, " > ".join(path) or "(root)"))
        print("  challenge: %s" % A.show(a))
        print("  solution:  %s" % B.show(b))
    sys.exit(rc)


if __name__ == "__main__":
    main()
