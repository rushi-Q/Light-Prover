#!/usr/bin/python3 -I
"""primcmp.py A.export B.export [ROOT ...] -- compare the dependency closures of ROOT declarations (default: the kernel
primitives the Lean 4.36 `lake comparator` checks, `Lake/CLI/Check.lean` primitiveTargets) between two lean4export 3.x
NDJSON exports, by a canonical structural digest of every declaration (all fields: kind, name, level params, type, value,
inductive/constructor/recursor data, binder names and info, hints, safety). Index numbering is irrelevant.

Purpose (A04, cross-version checking): the trusted check uses the Lean 4.36 kernel, whose built-in extensions (Nat
literals + GMP-accelerated Nat.add/sub/mul/div/mod/gcd/beq/ble/land/lor/xor/shiftLeft/shiftRight/pow, string literals ->
String.ofList [Char.ofNat ..], Quot) assume the standard definitions of these constants. If the closure of the primitives
in an export of release X is digest-identical to the closure in an export of 4.36.0, the 4.36 kernel's assumptions hold
for X exactly as for 4.36.

exit 0 = every declaration of the closure identical (and present in both), 1 = differences (listed), 2 = usage/parse error.
"""
import hashlib, json, sys

PRIMS = ["Nat", "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.gcd", "Nat.beq",
         "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "Nat.pow", "Nat.log2",
         "String", "String.mk", "String.ofList", "Char", "Char.ofNat", "List", "Bool", "Eq", "Quot", "Quot.mk",
         "Quot.lift", "Quot.ind", "eagerReduce", "optParam", "autoParam", "semiOutParam", "outParam"]


class Export:
    def __init__(self, path):
        self.names, self.levels, self.exprs, self.decls = {0: ()}, {0: ("zero",)}, {}, {}
        with open(path, "rb") as f:
            for ln in f:
                o = json.loads(ln)
                if "in" in o:
                    if "str" in o:
                        self.names[o["in"]] = self.names[o["str"]["pre"]] + (o["str"]["str"],)
                    else:
                        self.names[o["in"]] = self.names[o["num"]["pre"]] + (o["num"]["i"],)
                elif "il" in o:
                    self.levels[o["il"]] = o
                elif "ie" in o:
                    self.exprs[o["ie"]] = o
                elif "meta" in o:
                    self.meta = o["meta"]
                else:
                    for k, v in o.items():
                        if isinstance(v, dict) and "name" in v:
                            self.decls[self.n(v["name"])] = (k, v)
                        elif k in ("inductive",) and isinstance(v, dict):
                            for t in v.get("types", []):
                                self.decls[self.n(t["name"])] = ("inductive.type", t, v)
                            for c in v.get("ctors", []):
                                self.decls[self.n(c["name"])] = ("inductive.ctor", c, v)
                            for r in v.get("recs", []):
                                self.decls[self.n(r["name"])] = ("inductive.rec", r, v)
        self.ecache, self.lcache, self.dcache = {}, {}, {}

    def n(self, i):
        return ".".join(str(x) for x in self.names[i])

    def lv(self, i):
        if i in self.lcache:
            return self.lcache[i]
        o = self.levels[i]
        if i == 0:
            r = "0"
        elif "succ" in o:
            r = "(s %s)" % self.lv(o["succ"])
        elif "max" in o:
            r = "(max %s %s)" % tuple(self.lv(x) for x in o["max"])
        elif "imax" in o:
            r = "(imax %s %s)" % tuple(self.lv(x) for x in o["imax"])
        elif "param" in o:
            r = "(p %s)" % self.n(o["param"])
        else:
            r = json.dumps(o, sort_keys=True)
        self.lcache[i] = r
        return r

    def ex(self, i, consts):
        """digest of expression i; collects referenced constants"""
        if i in self.ecache:
            d, cs = self.ecache[i]
            consts |= cs
            return d
        o = self.exprs[i]
        cs = set()
        h = hashlib.sha256()
        if "bvar" in o:
            h.update(b"bvar%d" % o["bvar"])
        elif "sort" in o:
            h.update(b"sort" + self.lv(o["sort"]).encode())
        elif "const" in o:
            nm = self.n(o["const"]["name"])
            cs.add(nm)
            h.update(("const " + nm + " " + ",".join(self.lv(u) for u in o["const"]["us"])).encode())
        elif "app" in o:
            h.update(b"app" + self.ex(o["app"]["fn"], cs) + self.ex(o["app"]["arg"], cs))
        elif "lam" in o or "forallE" in o:
            k = "lam" if "lam" in o else "forallE"
            b = o[k]
            h.update((k + " " + self.n(b["name"]) + " " + b.get("binderInfo", "")).encode()
                     + self.ex(b["type"], cs) + self.ex(b["body"], cs))
        elif "letE" in o:
            b = o["letE"]
            h.update(("let " + self.n(b["name"]) + " " + str(b.get("nondep"))).encode() + self.ex(b["type"], cs)
                     + self.ex(b["value"], cs) + self.ex(b["body"], cs))
        elif "natVal" in o:
            h.update(b"nat" + str(o["natVal"]).encode())
        elif "strVal" in o:
            h.update(b"str" + json.dumps(o["strVal"]).encode())
        elif "mdata" in o:
            h.update(b"mdata" + json.dumps(o["mdata"].get("data"), sort_keys=True).encode()
                     + self.ex(o["mdata"]["expr"], cs))
        elif "proj" in o:
            p = o["proj"]
            cs.add(self.n(p["typeName"]))
            h.update(("proj " + self.n(p["typeName"]) + " " + str(p["idx"])).encode() + self.ex(p["struct"], cs))
        else:
            h.update(json.dumps(o, sort_keys=True).encode())
        d = h.digest()
        self.ecache[i] = (d, frozenset(cs))
        consts |= cs
        return d

    def canon_val(self, v, consts, key=""):
        """canonical text of a declaration record: name fields resolved, expression fields digested"""
        if isinstance(v, dict):
            out = []
            for k in sorted(v):
                x = v[k]
                if k in ("type", "value") and isinstance(x, int):
                    out.append(k + "=" + self.ex(x, consts).hex())
                elif k == "rhs" and isinstance(x, int):
                    out.append(k + "=" + self.ex(x, consts).hex())
                elif k in ("name", "induct", "ctor") and isinstance(x, int):
                    out.append(k + "=" + self.n(x))
                elif k in ("levelParams",):
                    out.append(k + "=" + ",".join(self.n(y) for y in x))
                elif k in ("all", "ctors") and isinstance(x, list) and all(isinstance(y, int) for y in x):
                    out.append(k + "=" + ",".join(self.n(y) for y in x))
                    consts |= {self.n(y) for y in x}
                else:
                    out.append(k + "=" + self.canon_val(x, consts, k))
            return "{" + ";".join(out) + "}"
        if isinstance(v, list):
            return "[" + ",".join(self.canon_val(x, consts, key) for x in v) + "]"
        return json.dumps(v)

    def decl(self, name):
        if name in self.dcache:
            return self.dcache[name]
        e = self.decls.get(name)
        if e is None:
            self.dcache[name] = (None, set())
            return self.dcache[name]
        consts = set()
        if e[0].startswith("inductive."):   # the whole block is one kernel declaration
            txt = e[0] + " " + self.canon_val(e[2], consts)
        else:
            txt = e[0] + " " + self.canon_val(e[1], consts)
        r = (hashlib.sha256(txt.encode()).hexdigest(), consts)
        self.dcache[name] = r
        return r

    def closure(self, roots):
        seen, todo = set(), [r for r in roots if r in self.decls]
        while todo:
            x = todo.pop()
            if x in seen:
                continue
            seen.add(x)
            todo += [c for c in self.decl(x)[1] if c not in seen and c in self.decls]
        return seen


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    A, B = Export(sys.argv[1]), Export(sys.argv[2])
    roots = sys.argv[3:] or PRIMS
    ca, cb = A.closure(roots), B.closure(roots)
    va = (A.meta.get("lean", {}) if hasattr(A, "meta") else {}).get("version")
    vb = (B.meta.get("lean", {}) if hasattr(B, "meta") else {}).get("version")
    diff = []
    for x in sorted(ca | cb):
        da, db = A.decl(x)[0], B.decl(x)[0]
        if da != db:
            diff.append((x, "missing in A" if da is None else "missing in B" if db is None else "DIFFERENT"))
    missing_roots = [r for r in roots if r not in A.decls or r not in B.decls]
    print(json.dumps({"A": sys.argv[1], "A_lean": va, "B": sys.argv[2], "B_lean": vb, "roots": len(roots),
                      "roots_missing": missing_roots, "closure_A": len(ca), "closure_B": len(cb),
                      "different": len(diff)}))
    for x, why in diff:
        print("  %s: %s" % (x, why))
    return 0 if not diff else 1


if __name__ == "__main__":
    sys.exit(main())
