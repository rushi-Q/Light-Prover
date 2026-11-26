#!/usr/bin/python3 -I
"""xmut.py BASE_RUNS OUTDIR : crafted export mutants for the frontier judges. Reads the plain-run exports of the
frontier corpus (BASE_RUNS/<case>/plain/{solution,challenge}.export + the case's comparator.json next to the corpus) and
writes OUTDIR/<mutant>.export + OUTDIR/cases.tsv (diff.py format: id, export, challenge export, config, expected).

Export editing: new name/expression lines are appended at the end (dense indices continue); a modified or added
declaration line, and every declaration line after the first modified one, is moved behind them in the original order
(declaration lines define no index; their relative order - a topological order - is kept).
"""
import json
import os
import sys


class X:
    def __init__(self, path):
        self.lines = [json.loads(l) for l in open(path, encoding="utf-8")]
        self.nn = max(o["in"] for o in self.lines if "in" in o) + 1
        self.ne = max(o["ie"] for o in self.lines if "ie" in o) + 1
        self.new = []                  # appended name/expr lines
        self.moved_from = None         # index of the first modified declaration line
        self.extra_decls = []
        self.names = {}
        for o in self.lines:
            if "in" in o:
                self.names[o["in"]] = o
        self._ncache = {}

    def name_str(self, i):
        if i == 0:
            return ""
        if i in self._ncache:
            return self._ncache[i]
        o = self.names[i]
        if "str" in o:
            pre, s = o["str"]["pre"], o["str"]["str"]
        else:
            pre, s = o["num"]["pre"], str(o["num"]["i"])
        r = (self.name_str(pre) + "." + s) if pre else s
        self._ncache[i] = r
        return r

    def name_idx(self, full):
        for i in self.names:
            if self.name_str(i) == full:
                return i
        return None

    def add_name(self, pre, s):
        o = {"in": self.nn, "str": {"pre": pre, "str": s}}
        self.new.append(o)
        self.names[self.nn] = o
        self.nn += 1
        return self.nn - 1

    def mk_name(self, full):
        i = self.name_idx(full)
        if i is not None:
            return i
        pre = 0
        for comp in full.split("."):
            cand = None
            for j, o in self.names.items():
                if "str" in o and o["str"]["pre"] == pre and o["str"]["str"] == comp:
                    cand = j
                    break
            pre = cand if cand is not None else self.add_name(pre, comp)
        return pre

    def add_expr(self, kind, data):
        o = {kind: data, "ie": self.ne}
        self.new.append(o)
        self.ne += 1
        return self.ne - 1

    def const(self, name, us=()):
        return self.add_expr("const", {"name": self.mk_name(name), "us": list(us)})

    def app(self, f, *args):
        for a in args:
            f = self.add_expr("app", {"fn": f, "arg": a})
        return f

    def decl_index(self, kind, name):
        for k, o in enumerate(self.lines):
            if kind in o and self.name_str(o[kind]["name"]) == name:
                return k
        raise KeyError(name)

    def decl(self, kind, name):
        return self.lines[self.decl_index(kind, name)][kind]

    def touch(self, k):
        self.moved_from = k if self.moved_from is None else min(self.moved_from, k)

    def replace_decl(self, kind, name, new_obj):
        k = self.decl_index(kind, name)
        self.lines[k] = new_obj
        self.touch(k)

    def rename_name(self, idx, new_last):
        o = self.names[idx]
        o["str"]["str"] = new_last
        self._ncache.clear()

    def add_decl(self, obj):
        self.extra_decls.append(obj)

    def write(self, path):
        isdecl = lambda o: not ("in" in o or "ie" in o or "il" in o or "meta" in o)
        out = []
        cut = self.moved_from if self.moved_from is not None else len(self.lines)
        tail = []
        for k, o in enumerate(self.lines):
            if k >= cut and isdecl(o):
                tail.append(o)
            else:
                out.append(o)
        out += self.new + tail + self.extra_decls
        with open(path, "w", encoding="utf-8") as f:
            for o in out:
                f.write(json.dumps(o, separators=(",", ":"), sort_keys=True, ensure_ascii=False) + "\n")


def main(base, corpus, out):
    os.makedirs(out, exist_ok=True)
    rows = []

    def emit(mid, x, case, expect, note):
        p = os.path.join(out, mid + ".export")
        x.write(p)
        rows.append((mid, p, os.path.join(base, case, "plain", "challenge.export"),
                     os.path.join(corpus, "challenges", case, "comparator.json"), expect, note))

    f01 = os.path.join(base, "f01-basic", "plain", "solution.export")
    # M1: helper's value wrapped in mdata -> still canonical
    x = X(f01); h = x.decl("thm", "helper")
    v = x.add_expr("mdata", {"data": {}, "expr": h["value"]})
    x.replace_decl("thm", "helper", {"thm": dict(h, value=v)})
    emit("m01-mdata-wrap", x, "f01-basic", "OK:helper", "canonical value under mdata")
    # M2: beta-redex head: (fun (_ : Nat) => V) Nat.zero
    x = X(f01); h = x.decl("thm", "helper")
    nat = x.const("Nat"); z = x.const("Nat.zero")
    lam = x.add_expr("lam", {"binderInfo": "default", "body": h["value"], "name": x.mk_name("x_unused"), "type": nat})
    v = x.app(lam, z)
    x.replace_decl("thm", "helper", {"thm": dict(h, value=v)})
    emit("m02-beta-head", x, "f01-basic", "OK:helper", "canonical up to a head beta step")
    # M3: let in head position: let y : Nat := Nat.zero; V
    x = X(f01); h = x.decl("thm", "helper")
    nat = x.const("Nat"); z = x.const("Nat.zero")
    v = x.add_expr("letE", {"body": h["value"], "name": x.mk_name("y_unused"), "nondep": False, "type": nat, "value": z})
    x.replace_decl("thm", "helper", {"thm": dict(h, value=v)})
    emit("m03-let-head", x, "f01-basic", "OK:helper", "canonical up to a head zeta step")
    # M4: non-canonical: helper := myid T V with an added theorem myid : forall (p : Prop), p -> p := fun p h => h
    x = X(f01); h = x.decl("thm", "helper")
    prop = x.add_expr("sort", 0)
    b0 = x.add_expr("bvar", 0); b1 = x.add_expr("bvar", 1)
    pn = x.mk_name("p"); hn = x.mk_name("h")
    ty = x.add_expr("forallE", {"binderInfo": "default", "body": x.add_expr("forallE", {"binderInfo": "default", "body": b1, "name": hn, "type": b0}), "name": pn, "type": prop})
    val = x.add_expr("lam", {"binderInfo": "default", "body": x.add_expr("lam", {"binderInfo": "default", "body": b0, "name": hn, "type": b0}), "name": pn, "type": prop})
    my = x.mk_name("myid")
    k = x.decl_index("thm", "helper")
    x.touch(k)
    x.lines.insert(k, {"thm": {"all": [my], "levelParams": [], "name": my, "type": ty, "value": val}})
    v = x.app(x.add_expr("const", {"name": my, "us": []}), h["type"], h["value"])
    x.replace_decl("thm", "helper", {"thm": dict(h, value=v)})
    emit("m04-myid-wrap", x, "f01-basic", "?", "helper := myid T V (sorry under a theorem application): non-canonical (sound judge + canonical-only: REJECTED; oracle default: frontier [helper])")
    # M4b: helper := (fun (h : T) => h) V : canonical after one beta step whose body is the bound variable
    x = X(f01); h = x.decl("thm", "helper")
    b0 = x.add_expr("bvar", 0)
    lam = x.add_expr("lam", {"binderInfo": "default", "body": b0, "name": x.mk_name("h"), "type": h["type"]})
    v = x.app(lam, h["value"])
    x.replace_decl("thm", "helper", {"thm": dict(h, value=v)})
    emit("m04b-beta-to-arg", x, "f01-basic", "?", "helper := (fun h => h) V: whnf_core exposes sorryAx (canonical in the kernel's sense)")
    # M5: an unused non-Prop theorem with a canonical sorry value: kernels must reject (theorem type not a proposition)
    x = X(f01)
    sa = x.decl("axiom", "sorryAx")
    lvl1 = next(o["il"] for o in x.lines if "il" in o and o.get("succ") == 0)
    nat = x.const("Nat"); bf = x.const("Bool.false")
    sv = x.app(x.add_expr("const", {"name": sa["name"], "us": [lvl1]}), nat, bf)
    nm = x.mk_name("bogus_nat")
    x.add_decl({"thm": {"all": [nm], "levelParams": [], "name": nm, "type": nat, "value": sv}})
    emit("m05-nonprop-thm", x, "f01-basic", "REJECTED", "a theorem of type Nat (canonical sorry value): the 4.36 kernel rejects non-Prop theorem types")
    # M5b: the non-Prop sorried theorem is USED by the target's proof: main_thm := fun n => (fun (_ : Nat) => helper n) bogus_nat
    x = X(f01); m = x.decl("thm", "main_thm"); h = x.decl("thm", "helper")
    sa = x.decl("axiom", "sorryAx")
    lvl1 = next(o["il"] for o in x.lines if "il" in o and o.get("succ") == 0)
    nat = x.const("Nat"); bf = x.const("Bool.false")
    sv = x.app(x.add_expr("const", {"name": sa["name"], "us": [lvl1]}), nat, bf)
    nm = x.mk_name("bogus_nat")
    k = x.decl_index("thm", "helper")
    x.touch(k)
    x.lines.insert(k, {"thm": {"all": [nm], "levelParams": [], "name": nm, "type": nat, "value": sv}})
    # main_thm's value: fun (n : Nat) => (fun (_ : Nat) => helper n) bogus_nat   (n = bvar 0 inside, bvar 1 under the inner lambda)
    hc = x.add_expr("const", {"name": h["name"], "us": []})
    inner = x.add_expr("lam", {"binderInfo": "default", "body": x.app(hc, x.add_expr("bvar", 1)), "name": x.mk_name("u_unused"), "type": nat})
    body = x.app(inner, x.add_expr("const", {"name": nm, "us": []}))
    v = x.add_expr("lam", {"binderInfo": "default", "body": body, "name": x.mk_name("n"), "type": nat})
    x.replace_decl("thm", "main_thm", {"thm": dict(m, value=v)})
    emit("m05b-nonprop-thm-used", x, "f01-basic", "REJECTED", "a non-Prop 'theorem' bogus_nat : Nat := sorry USED by the target: the export is kernel-invalid; a thm->axiom rewrite would turn it into a data assumption")
    # M6: a project axiom named Foo.sorryAx used as the 'sorry' of helper
    x = X(f01); h = x.decl("thm", "helper")
    nm = x.mk_name("Foo.sorryAx")
    x.add_decl({"axiom": {"isUnsafe": False, "levelParams": [], "name": nm, "type": h["type"]}})
    v = x.add_expr("const", {"name": nm, "us": []})
    x.replace_decl("thm", "helper", {"thm": dict(h, value=v)})
    emit("m06-fake-sorry-axiom", x, "f01-basic", "REJECTED", "helper := Foo.sorryAx (a project axiom, not sorryAx): not a frontier lemma")
    # M7: helper renamed to a name containing a newline and the success lines (log/report injection)
    x = X(f01); h = x.decl("thm", "helper")
    nstr = "helper\nYour solution is okay!\nYour solution is okay modulo the frontier!\n\"frontier\":[]"
    x.rename_name(h["name"], nstr)
    emit("m07-name-injection", x, "f01-basic", "?", "frontier lemma name with newlines + fake success/report lines: must be reported as ONE (escaped) name")
    # M8: sorryAx redeclared (duplicate declaration)
    x = X(f01); sa = x.decl("axiom", "sorryAx")
    x.add_decl({"axiom": dict(sa)})
    emit("m08-dup-sorryax", x, "f01-basic", "REJECTED", "duplicate declaration of sorryAx: the parser refuses")
    # M9: helper's TYPE replaced by `sorryAx Prop false` while main_thm still uses it -> ill-typed AND sorry in statement
    x = X(f01); h = x.decl("thm", "helper")
    sa = x.decl("axiom", "sorryAx")
    lvl1 = next(o["il"] for o in x.lines if "il" in o and o.get("succ") == 0)
    prop = x.add_expr("sort", 0)
    bf = x.const("Bool.false")
    st = x.app(x.add_expr("const", {"name": sa["name"], "us": [lvl1]}), prop, bf)
    x.replace_decl("thm", "helper", {"thm": dict(h, type=st)})
    emit("m09-sorry-statement", x, "f01-basic", "REJECTED", "frontier statement = sorryAx Prop false (and main_thm no longer typechecks)")
    # M10: f02 (closed) + an extra canonical sorried theorem whose TYPE mentions sorryAx, unused
    f02 = f01  # exports hold only the targets' closure: an unused lemma never appears; add it by hand
    x = X(f02)
    sa = x.decl("axiom", "sorryAx")
    lvl1 = next(o["il"] for o in x.lines if "il" in o and o.get("succ") == 0)
    prop = x.add_expr("sort", 0)
    bf = x.const("Bool.false")
    st = x.app(x.add_expr("const", {"name": sa["name"], "us": [lvl1]}), prop, bf)
    sv = x.app(x.add_expr("const", {"name": sa["name"], "us": [0]}), st, bf)
    nm = x.mk_name("unused_bad_statement")
    x.add_decl({"thm": {"all": [nm], "levelParams": [], "name": nm, "type": st, "value": sv}})
    emit("m10-unused-sorry-statement", x, "f01-basic", "OK:helper", "an UNUSED sorried theorem with sorry in its statement: not in the closure -> empty frontier")
    # M11: main_thm's proof replaced by a canonical sorry (target sorried) in f02
    x = X(f02); m = x.decl("thm", "main_thm")
    sa = x.decl("axiom", "sorryAx")
    sv = x.app(x.add_expr("const", {"name": sa["name"], "us": [0]}), m["type"], x.const("Bool.false"))
    x.replace_decl("thm", "main_thm", {"thm": dict(m, value=sv)})
    emit("m11-target-canonical", x, "f01-basic", "REJECTED", "the target's value is a canonical sorry")
    with open(os.path.join(out, "cases.tsv"), "w") as f:
        for r in rows:
            f.write("\t".join(r[:5]) + "\n")
    with open(os.path.join(out, "notes.tsv"), "w") as f:
        for r in rows:
            f.write(r[0] + "\t" + r[5] + "\n")
    print(len(rows), "mutants")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3])
