#!/usr/bin/python3 -I
"""warmdiff.py BASE_EXPORT CHALLENGE_EXPORT CONFIG WORK [--n N] [--seed S] [--jobs J] [--fvcheckd PATH] [--bins DIR]

Randomized differential of the warm delta check against the COLD sound check.

For a base export B (verified once by `fvcheckd serve`), every mutant is a delta D (a self-contained lean4export file
with changed / re-supplied / new declarations) together with the EFFECTIVE environment it denotes, materialized
independently here:
    E_eff = (B minus dirty) + D,   O = names of D also in B with different content,
    dirty = reverse-transitive closure of O in B under the reference relation (consts of type / value / recursor
            rules, inductive `all` / ctors, ctor `induct`, rule ctors; + optionally proj typeNames), closed under
            inductive blocks
(E_eff as a full export: every index line of B, the new index lines, the clean declarations of B in B's order, then
D's declarations). Oracle = the unchanged `check/sound/check-sound.sh` on E_eff. Classes per mutant:
    CRITICAL  warm ACCEPTED, cold not ACCEPTED (a delta accept the full check does not give)
    VETO-WEAK the cold second kernel (gruszka) rejects E_eff while gruszka-warm said ok on the delta (an incomplete
              dirty set in the veto leg, the gruszka-warm Ref::Main class; the verdict may still be right because the Lean leg rejects)
    AVAIL     warm REJECTED/no verdict, cold ACCEPTED
    AGREE     same class; FALLBACK = warm asked for the cold path (never an accept)
Operators (on project declarations, with and without re-supplying the dirty dependents): noop, thm value swap,
def value swap (same type), thm type+value swap, axiom injection, new theorem using an overridden def, inductive
constructor-type edit, level-param edit, target statement swap, kernel-implicit override.
"""
import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

_here = os.path.dirname(os.path.realpath(__file__))
_pkg = os.path.dirname(os.path.dirname(_here))
LL = os.environ.get("LIGHT_LEAN", "$LIGHT_LEAN")
PKGROOT = _pkg if os.path.isfile(os.path.join(_pkg, "check", "sound", "check-sound.sh")) else os.path.join(LL, "fastverify")
DECL_KINDS = ("thm", "def", "axiom", "opaque", "quot", "inductive")
IMPLICIT = {"Nat", "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.gcd", "Nat.beq",
            "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "Nat.pow", "Nat.log2",
            "String", "String.mk", "String.ofList", "Char", "Char.ofNat", "List", "List.nil", "List.cons", "Quot",
            "Quot.mk", "Quot.lift", "Quot.ind", "Eq", "Eq.refl", "eagerReduce", "Bool", "Bool.true", "Bool.false"}


class Exp:
    def __init__(self, path):
        self.meta = None
        self.idx_lines = []          # raw index lines of B, in order
        self.names = [(0, "str", "")]  # idx -> (pre, kind, val)
        self.levels = {}
        self.exprs = []
        self.decls = []              # (kind, obj) in file order
        self.nlev = 1
        with open(path, encoding="utf-8") as f:
            for i, raw in enumerate(f):
                if i == 0:
                    self.meta = raw
                    continue
                o = json.loads(raw)
                if "in" in o:
                    k = "str" if "str" in o else "num"
                    self.names.append((o[k]["pre"], k, o[k].get("str", o[k].get("i"))))
                    self.idx_lines.append(raw)
                elif "il" in o:
                    self.levels[o["il"]] = o
                    self.nlev = max(self.nlev, o["il"] + 1)
                    self.idx_lines.append(raw)
                elif "ie" in o:
                    assert o["ie"] == len(self.exprs)
                    self.exprs.append(o)
                    self.idx_lines.append(raw)
                else:
                    self.decls.append((next(iter(o)), o[next(iter(o))]))
        self.base_nn, self.base_ne, self.base_nl = len(self.names), len(self.exprs), self.nlev
        self._ns = {}
        self.members = {}            # member name idx -> decl index
        for di, (k, d) in enumerate(self.decls):
            for m in self.member_ids(k, d):
                self.members[m] = di
        self._cmemo = {}

    def nstr(self, i):
        if i in self._ns:
            return self._ns[i]
        parts = []
        j = i
        while j:
            pre, k, v = self.names[j]
            parts.append(str(v))
            j = pre
        s = ".".join(reversed(parts))
        self._ns[i] = s
        return s

    @staticmethod
    def member_ids(k, d):
        if k == "inductive":
            return [t["name"] for t in d["types"] + d["ctors"] + d["recs"]]
        return [d["name"]]

    def econsts(self, eid, with_proj):
        key = (eid, with_proj)
        if key in self._cmemo:
            return self._cmemo[key]
        out = set()
        stack = [eid]
        seen = set()
        while stack:
            i = stack.pop()
            if i in seen:
                continue
            seen.add(i)
            if (i, with_proj) in self._cmemo and i != eid:
                out |= self._cmemo[(i, with_proj)]
                continue
            o = self.exprs[i]
            kk = next(x for x in o if x != "ie")
            d = o[kk]
            if kk == "const":
                out.add(d["name"])
            elif kk == "app":
                stack += [d["fn"], d["arg"]]
            elif kk in ("lam", "forallE"):
                stack += [d["type"], d["body"]]
            elif kk == "letE":
                stack += [d["type"], d["value"], d["body"]]
            elif kk == "proj":
                stack.append(d["struct"])
                if with_proj:
                    out.add(d["typeName"])
            elif kk == "mdata":
                stack.append(d["expr"])
        fo = frozenset(out)
        self._cmemo[key] = fo
        return fo

    def refs(self, k, d, with_proj=False):
        out = set()
        tops = [d] if k != "inductive" else d["types"] + d["ctors"] + d["recs"]
        for t in tops:
            out |= self.econsts(t["type"], with_proj)
            if "value" in t:
                out |= self.econsts(t["value"], with_proj)
            for r in t.get("rules", []):
                out |= self.econsts(r["rhs"], with_proj)
                out.add(r["ctor"])
            for key in ("all", "ctors"):
                out |= set(t.get(key, []))
            if "induct" in t:
                out.add(t["induct"])
        if k == "quot":
            pass
        return out


def canon(d):
    return json.dumps(d, sort_keys=True)


class Mutant:
    """New index lines are appended to B's tables (ids continue densely after B); D holds decls in B-space ids."""

    def __init__(self, ex):
        self.ex = ex
        self.new_names = []
        self.new_levels = []
        self.new_exprs = []
        self.decls = []          # D declarations (kind, obj) in order
        self.note = ""

    def name(self, pre, s):
        for i in range(len(self.ex.names)):
            if self.ex.names[i][0] == pre and self.ex.names[i][2] == s and self.ex.names[i][1] == "str":
                return i
        idx = len(self.ex.names)
        self.ex.names.append((pre, "str", s))
        self.new_names.append({"in": idx, "str": {"pre": pre, "str": s}})
        return idx

    def expr(self, kind, data):
        idx = len(self.ex.exprs)
        o = {kind: data, "ie": idx}
        self.ex.exprs.append(o)
        self.new_exprs.append(o)
        return idx

    def rollback(self):
        del self.ex.names[self.ex.base_nn:]
        del self.ex.exprs[self.ex.base_ne:]
        self.ex._ns = {k: v for k, v in self.ex._ns.items() if k < self.ex.base_nn}
        self.ex._cmemo = {k: v for k, v in self.ex._cmemo.items() if k[0] < self.ex.base_ne}


def dirty_set(ex, mut, with_proj=False):
    bdecl = {}
    for (k, d) in mut.decls:
        for m in Exp.member_ids(k, d):
            bdecl[m] = (k, d)
    O = set()
    for m, (k, d) in bdecl.items():
        di = ex.members.get(m)
        if di is None:
            continue
        bk, bd = ex.decls[di]
        if bk != k or canon(bd) != canon(d):
            O |= set(Exp.member_ids(bk, bd))
    # reverse closure in B
    rev = {}
    for di, (k, d) in enumerate(ex.decls):
        for r in ex.refs(k, d, with_proj):
            rev.setdefault(r, set()).add(di)
    dirty_di = set()
    stack = [ex.members[m] for m in O if m in ex.members]
    while stack:
        di = stack.pop()
        if di in dirty_di:
            continue
        dirty_di.add(di)
        for m in Exp.member_ids(*ex.decls[di]):
            for u in rev.get(m, ()):
                if u not in dirty_di:
                    stack.append(u)
    return O, dirty_di


def write_eff(ex, mut, dirty_di, path):
    dump = lambda o: json.dumps(o, separators=(",", ":"), sort_keys=True, ensure_ascii=False) + "\n"
    # D declarations equal to B's and outside the dirty set stay at B's position (file order matters for gruszka);
    # overridden / dirty / new ones go after the clean prefix, in D's order
    tail = []
    dnames = set()
    for (k, d) in mut.decls:
        ms = set(Exp.member_ids(k, d))
        di = ex.members.get(next(iter(ms)))
        if di is not None and di not in dirty_di and ex.decls[di][0] == k and canon(ex.decls[di][1]) == canon(d):
            continue
        tail.append((k, d))
        dnames |= ms
    with open(path, "w", encoding="utf-8") as f:
        f.write(ex.meta)
        for raw in ex.idx_lines:
            f.write(raw)
        for o in mut.new_names + mut.new_levels + mut.new_exprs:
            f.write(dump(o))
        for di, (k, d) in enumerate(ex.decls):
            if di in dirty_di:
                continue
            ms = set(Exp.member_ids(k, d))
            if ms & dnames:      # supplied by D (equal content: not dirty) -> written with D's decls below
                continue
            f.write(dump({k: d}))
        for (k, d) in tail:
            f.write(dump({k: d}))


def write_delta(ex, mut, path):
    """self-contained export of D's declarations: needed names/levels/exprs renumbered densely"""
    nmap, lmap, emap = {0: 0}, {0: 0}, {}
    out = []
    dump = lambda o: json.dumps(o, separators=(",", ":"), sort_keys=True, ensure_ascii=False) + "\n"

    def N(i):
        if i in nmap:
            return nmap[i]
        pre, k, v = ex.names[i]
        p = N(pre)
        j = len(nmap)
        nmap[i] = j
        out.append({"in": j, k: ({"pre": p, "str": v} if k == "str" else {"pre": p, "i": v})})
        return j

    def L(i):
        if i in lmap:
            return lmap[i]
        o = ex.levels[i] if i in ex.levels else next(x for x in mut.new_levels if x["il"] == i)
        kk = next(x for x in o if x != "il")
        v = o[kk]
        if kk == "succ":
            nv = L(v)
        elif kk in ("max", "imax"):
            nv = [L(v[0]), L(v[1])]
        else:
            nv = N(v)
        j = len(lmap)
        lmap[i] = j
        out.append({"il": j, kk: nv})
        return j

    def E(i):
        if i in emap:
            return emap[i]
        stack = [(i, False)]
        while stack:
            x, done = stack.pop()
            if x in emap:
                continue
            o = ex.exprs[x]
            kk = next(y for y in o if y != "ie")
            d = o[kk]
            kids = {"app": ["fn", "arg"], "lam": ["type", "body"], "forallE": ["type", "body"],
                    "letE": ["type", "value", "body"], "proj": ["struct"], "mdata": ["expr"]}.get(kk, [])
            if not done:
                stack.append((x, True))
                for c in kids:
                    if d[c] not in emap:
                        stack.append((d[c], False))
                continue
            nd = dict(d) if isinstance(d, dict) else d
            if isinstance(d, dict):
                for c in kids:
                    nd[c] = emap[d[c]]
                if kk == "const":
                    nd = {"name": N(d["name"]), "us": [L(u) for u in d["us"]]}
                elif kk in ("lam", "forallE", "letE"):
                    nd["name"] = N(d["name"])
                elif kk == "proj":
                    nd["typeName"] = N(d["typeName"])
            elif kk == "sort":
                nd = L(d)
            j = len(emap)
            emap[x] = j
            out.append({kk: nd, "ie": j})
        return emap[i]

    def fixdecl(k, d):
        d = json.loads(json.dumps(d))
        tops = [d] if k != "inductive" else d["types"] + d["ctors"] + d["recs"]
        for t in tops:
            t["name"] = N(t["name"])
            t["levelParams"] = [N(x) for x in t["levelParams"]]
            t["type"] = E(t["type"])
            if "value" in t:
                t["value"] = E(t["value"])
            for key in ("all", "ctors"):
                if key in t:
                    t[key] = [N(x) for x in t[key]]
            if "induct" in t:
                t["induct"] = N(t["induct"])
            for r in t.get("rules", []):
                r["ctor"] = N(r["ctor"])
                r["rhs"] = E(r["rhs"])
        return {k: d}

    decls = [fixdecl(k, d) for (k, d) in mut.decls]
    with open(path, "w", encoding="utf-8") as f:
        f.write(ex.meta)
        for o in out:
            f.write(dump(o))
        for o in decls:
            f.write(dump(o))


def gen_mutant(ex, rng, targets, opname):
    m = Mutant(ex)
    proj = [di for di, (k, d) in enumerate(ex.decls) if k in ("thm", "def")
            and not ex.nstr(d["name"]).startswith(("Lean.", "Nat.", "List.", "String.", "Char.", "Quot", "Eq", "Bool"))
            and ex.nstr(d["name"]) not in IMPLICIT]
    # prefer the project's own declarations (an edit loop edits those): 70 % of the picks when a project namespace exists
    top = {}
    for di in proj:
        t = ex.nstr(ex.decls[di][1]["name"]).split(".")[0]
        top[t] = top.get(t, 0) + 1
    projns = [di for di in proj if ex.nstr(ex.decls[di][1]["name"]).split(".")[0] in PROJECT_NS]
    if projns and rng.random() < 0.7:
        proj = sorted(set(projns + [di for di in proj if ex.decls[di][0] == "def" and rng.random() < 0.02]))
    thms = [di for di in proj if ex.decls[di][0] == "thm"]
    defs = [di for di in proj if ex.decls[di][0] == "def"]
    resupply = rng.choice(["all", "none", "half"])

    def finish_with_dependents(changed_dis):
        O, dirty = dirty_set(ex, m, True)
        sup = sorted(dirty - set(changed_dis))
        if resupply == "none":
            sup = []
        elif resupply == "half":
            sup = [x for x in sup if rng.random() < 0.5]
        have = set()
        for (k, d) in m.decls:
            have |= set(Exp.member_ids(k, d))
        for di in sup:
            k, d = ex.decls[di]
            if not (set(Exp.member_ids(k, d)) & have):
                m.decls.append((k, d))
        # keep D in B's order (new decls first)
        order = {}
        for di, (k, d) in enumerate(ex.decls):
            for x in Exp.member_ids(k, d):
                order[x] = di
        m.decls.sort(key=lambda kd: order.get(Exp.member_ids(*kd)[0], -1))
        m.note += f" resupply={resupply}"

    if opname == "noop":
        di = rng.choice(proj)
        m.decls.append(ex.decls[di])
        m.note = f"noop {ex.nstr(ex.decls[di][1]['name'])}"
    elif opname == "thm_value_swap" and len(thms) >= 2:
        a, b = rng.sample(thms, 2)
        k, d = ex.decls[a]
        nd = dict(d, value=ex.decls[b][1]["value"])
        m.decls.append((k, nd))
        m.note = f"thm_value_swap {ex.nstr(d['name'])} <- value of {ex.nstr(ex.decls[b][1]['name'])}"
        finish_with_dependents([a])
    elif opname == "def_value_swap":
        bytype = {}
        for di in defs:
            bytype.setdefault((ex.decls[di][1]["type"], tuple(ex.decls[di][1]["levelParams"])), []).append(di)
        pairs = [v for v in bytype.values() if len(v) >= 2]
        if not pairs:
            return None
        a, b = rng.sample(rng.choice(pairs), 2)
        k, d = ex.decls[a]
        nd = dict(d, value=ex.decls[b][1]["value"])
        m.decls.append((k, nd))
        m.note = f"def_value_swap {ex.nstr(d['name'])} <- value of {ex.nstr(ex.decls[b][1]['name'])}"
        finish_with_dependents([a])
    elif opname == "def_swap_distinct" and defs:
        alldefs = [di for di, (k, d) in enumerate(ex.decls) if k == "def"]
        bytype = {}
        for di in alldefs:
            d = ex.decls[di][1]
            bytype.setdefault((d["type"], tuple(d["levelParams"])), []).append(di)
        cands = [di for di in defs if any(ex.decls[x][1]["value"] != ex.decls[di][1]["value"]
                                          for x in bytype[(ex.decls[di][1]["type"], tuple(ex.decls[di][1]["levelParams"]))])]
        if not cands:
            return None
        a = rng.choice(cands)
        k, d = ex.decls[a]
        b = rng.choice([x for x in bytype[(d["type"], tuple(d["levelParams"]))] if ex.decls[x][1]["value"] != d["value"]])
        m.decls.append((k, dict(d, value=ex.decls[b][1]["value"])))
        m.note = f"def_swap_distinct {ex.nstr(d['name'])} <- value of {ex.nstr(ex.decls[b][1]['name'])}"
        finish_with_dependents([a])
    elif opname == "def_nat_succ":
        natc = [i for i, o in enumerate(ex.exprs[:ex.base_ne]) if "const" in o and ex.nstr(o["const"]["name"]) == "Nat"]
        succ = [i for i, o in enumerate(ex.exprs[:ex.base_ne]) if "const" in o and ex.nstr(o["const"]["name"]) == "Nat.succ"]
        if not natc or not succ:
            return None
        cands = [di for di in defs if ex.decls[di][1]["type"] in natc]
        if not cands:
            cands = [di for di, (k, d) in enumerate(ex.decls) if k == "def" and d["type"] in natc
                     and ex.nstr(d["name"]) not in IMPLICIT]
        if not cands:
            return None
        a = rng.choice(cands)
        k, d = ex.decls[a]
        v = m.expr("app", {"fn": succ[0], "arg": d["value"]})
        m.decls.append((k, dict(d, value=v)))
        m.note = f"def_nat_succ {ex.nstr(d['name'])} := Nat.succ (old value)"
        finish_with_dependents([a])
    elif opname == "thm_eta_wrap" and thms:
        a = rng.choice(thms)
        k, d = ex.decls[a]
        hb = m.expr("bvar", 0)
        lam = m.expr("lam", {"binderInfo": "default", "body": hb, "name": m.name(0, "h_fz"), "type": d["type"]})
        v = m.expr("app", {"fn": lam, "arg": d["value"]})
        m.decls.append((k, dict(d, value=v)))
        m.note = f"thm_eta_wrap {ex.nstr(d['name'])} := (fun h => h) old proof"
        finish_with_dependents([a])
    elif opname == "def_type_change" and defs:
        # give a def ANOTHER def's type and value (different type), keep its dependents stale (re-supplied unchanged
        # or not at all): every dependent that uses it is now ill-typed, and both kernels must re-check them - the
        # gruszka-warm Ref::Main class (gruszka-warm missed dependents reached only through shared subterms of theorem proofs)
        alldefs = [di for di, (k, d) in enumerate(ex.decls) if k == "def" and ex.nstr(d["name"]) not in IMPLICIT]
        a = rng.choice(defs)
        k, d = ex.decls[a]
        others = [x for x in alldefs if x != a and ex.decls[x][1]["type"] != d["type"]
                  and ex.decls[x][1]["levelParams"] == d["levelParams"]]
        if not others:
            return None
        b = rng.choice(others)
        m.decls.append((k, dict(d, type=ex.decls[b][1]["type"], value=ex.decls[b][1]["value"])))
        m.note = f"def_type_change {ex.nstr(d['name'])} := (type, value) of {ex.nstr(ex.decls[b][1]['name'])}"
        finish_with_dependents([a])
    elif opname == "thm_tv_swap" and len(thms) >= 2:
        a, b = rng.sample(thms, 2)
        (ka, da), (kb, db) = ex.decls[a], ex.decls[b]
        if da["levelParams"] != db["levelParams"]:
            return None
        m.decls.append((ka, dict(da, type=db["type"], value=db["value"])))
        m.decls.append((kb, dict(db, type=da["type"], value=da["value"])))
        m.note = f"thm_tv_swap {ex.nstr(da['name'])} <-> {ex.nstr(db['name'])}"
        finish_with_dependents([a, b])
    elif opname == "axiom_inject" and thms:
        a = rng.choice(thms)
        k, d = ex.decls[a]
        axn = m.name(0, f"fz_ax_{rng.randrange(10**6)}")
        m.decls.append(("axiom", {"isUnsafe": False, "levelParams": d["levelParams"], "name": axn, "type": d["type"]}))
        us = []
        for p in d["levelParams"]:
            li = next((i for i, o in ex.levels.items() if o.get("param") == p), None)
            if li is None:
                return None
            us.append(li)
        c = m.expr("const", {"name": axn, "us": us})
        m.decls.append((k, dict(d, value=c)))
        m.note = f"axiom_inject {ex.nstr(d['name'])} := new axiom"
        finish_with_dependents([a])
    elif opname == "def_override_new_user" and defs:
        # override a def with another def's value of the same type (if any) and add a NEW theorem that re-proves a
        # dependent's statement with the dependent's old proof (stale proof against the new def)
        users = {}
        for di, (k, d) in enumerate(ex.decls):
            if k == "thm":
                for r in ex.refs(k, d):
                    if r in ex.members and ex.members[r] in defs:
                        users.setdefault(ex.members[r], []).append(di)
        bytype = {}
        for di in defs:
            bytype.setdefault((ex.decls[di][1]["type"], tuple(ex.decls[di][1]["levelParams"])), []).append(di)
        cands = [di for di in users if len(bytype[(ex.decls[di][1]["type"], tuple(ex.decls[di][1]["levelParams"]))]) >= 2]
        if not cands:
            return None
        a = rng.choice(cands)
        b = rng.choice([x for x in bytype[(ex.decls[a][1]["type"], tuple(ex.decls[a][1]["levelParams"]))] if x != a])
        k, d = ex.decls[a]
        m.decls.append((k, dict(d, value=ex.decls[b][1]["value"])))
        u = rng.choice(users[a])
        ku, du = ex.decls[u]
        nn = m.name(0, f"fz_copy_{rng.randrange(10**6)}")
        m.decls.append(("thm", dict(du, name=nn, all=[nn])))
        m.note = f"def_override_new_user {ex.nstr(d['name'])} + new thm = old proof of {ex.nstr(du['name'])}"
        finish_with_dependents([a])
        # the new theorem must come after the overridden def: move it last
        newt = [x for x in m.decls if x[1].get("name") == nn]
        m.decls = [x for x in m.decls if x[1].get("name") != nn] + newt
    elif opname == "lparams_edit" and thms:
        a = rng.choice(thms)
        k, d = ex.decls[a]
        if d["levelParams"]:
            nd = dict(d, levelParams=d["levelParams"][1:])
        else:
            nd = dict(d, levelParams=[m.name(0, "u_fz")])
        m.decls.append((k, nd))
        m.note = f"lparams_edit {ex.nstr(d['name'])}"
        finish_with_dependents([a])
    elif opname == "target_stmt_swap":
        tg = [di for di, (k, d) in enumerate(ex.decls) if k == "thm" and ex.nstr(d["name"]) in targets]
        if len(tg) < 2:
            return None
        a, b = rng.sample(tg, 2)
        (ka, da), (kb, db) = ex.decls[a], ex.decls[b]
        if da["levelParams"] != db["levelParams"]:
            return None
        m.decls.append((ka, dict(da, type=db["type"], value=db["value"])))
        m.note = f"target_stmt_swap {ex.nstr(da['name'])} <- {ex.nstr(db['name'])}"
        finish_with_dependents([a])
    elif opname == "ind_ctor_edit":
        inds = [di for di, (k, d) in enumerate(ex.decls) if k == "inductive" and d["ctors"]
                and not ex.nstr(d["types"][0]["name"]).startswith(("Lean.", "Nat", "List", "String", "Char", "Quot", "Eq", "Bool"))]
        if not inds:
            return None
        a = rng.choice(inds)
        k, d = ex.decls[a]
        nd = json.loads(json.dumps(d))
        ci = rng.randrange(len(nd["ctors"]))
        other = rng.choice([t["type"] for t in nd["ctors"]] + [t["type"] for t in nd["types"]])
        if rng.random() < 0.5:
            nd["ctors"][ci]["numFields"] = max(0, nd["ctors"][ci]["numFields"] + rng.choice([-1, 1]))
            m.note = f"ind_ctor_edit numFields {ex.nstr(nd['ctors'][ci]['name'])}"
        else:
            nd["ctors"][ci]["type"] = other
            m.note = f"ind_ctor_edit type {ex.nstr(nd['ctors'][ci]['name'])}"
        m.decls.append((k, nd))
        finish_with_dependents([a])
    elif opname == "implicit_override":
        imp = [di for di, (k, d) in enumerate(ex.decls) if k == "def" and ex.nstr(d["name"]) in IMPLICIT]
        if not imp:
            return None
        a = rng.choice(imp)
        k, d = ex.decls[a]
        nd = dict(d, hints="opaque" if d.get("hints") != "opaque" else "abbrev")
        m.decls.append((k, nd))
        m.note = f"implicit_override {ex.nstr(d['name'])} hints"
        finish_with_dependents([a])
    else:
        return None
    return m


PROJECT_NS = {"V06", "Formalism", "GlobalTheory", "GroundTheory", "Main", "helper", "main_thm"}
OPS = ["noop", "thm_value_swap", "def_value_swap", "thm_tv_swap", "axiom_inject", "def_override_new_user",
       "lparams_edit", "target_stmt_swap", "ind_ctor_edit", "implicit_override", "def_swap_distinct", "def_nat_succ",
       "thm_eta_wrap", "def_type_change"]


def main(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("challenge")
    ap.add_argument("config")
    ap.add_argument("work")
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--fvcheckd", default=os.path.join(os.environ.get("FV_WARM_DIR", os.path.join(PKGROOT, "check", "warm")), "fvcheckd.py"))
    ap.add_argument("--bins", default=os.environ.get("FV_WARM_BINS", os.path.join(PKGROOT, "check", "warm", "bin")))
    ap.add_argument("--no-proj", action="store_true", help="dirty closure does NOT follow proj typeNames (Lean's getUsedConstants does)")
    ap.add_argument("--ops", help="comma list of operators (default: all)")
    ap.add_argument("--concurrent", type=int, default=0, help="also query every delta twice with N concurrent clients")
    ap.add_argument("--cleanup", action="store_true", help="delete each effective export after its cold check (big bases)")
    a = ap.parse_args(argv)
    os.makedirs(a.work, exist_ok=True)
    cfg = json.load(open(a.config))
    targets = set(cfg["theorem_names"])
    ex = Exp(a.base)
    rng = random.Random(a.seed)
    global OPS
    if a.ops:
        OPS = a.ops.split(",")
    # 1. generate mutants
    muts = []
    tries = 0
    while len(muts) < a.n and tries < a.n * 20:
        tries += 1
        op = OPS[len(muts) % len(OPS)] if tries <= a.n else rng.choice(OPS)
        m = gen_mutant(ex, rng, targets, op)
        if m is None or not m.decls:
            if m is not None:
                m.rollback()
            continue
        O, dirty = dirty_set(ex, m, not a.no_proj)
        if a.ops and not O and m.note.split()[0] != "noop":
            m.rollback()
            continue
        mid = f"w{len(muts):04d}"
        write_delta(ex, m, os.path.join(a.work, mid + ".delta"))
        write_eff(ex, m, dirty, os.path.join(a.work, mid + ".eff"))
        muts.append({"id": mid, "op": m.note.split()[0], "note": m.note, "overridden": len(O), "dirty": len(dirty),
                     "delta_decls": len(m.decls)})
        m.rollback()
    json.dump(muts, open(os.path.join(a.work, "mutants.json"), "w"), indent=1)
    # 2. warm daemon
    st = os.path.join(a.work, "state")
    shutil.rmtree(st, ignore_errors=True)
    chash = hashlib.sha256(open(a.challenge, "rb").read()).hexdigest()
    srv = subprocess.Popen(["python3", "-I", a.fvcheckd, "serve", "--state", st, "--challenge", a.challenge,
                            "--challenge-sha256", chash, "--config", a.config, "--base", a.base, "--threads", str(a.threads),
                            "--bins-dir", a.bins], stdout=open(os.path.join(a.work, "serve.log"), "w"),
                           stderr=subprocess.STDOUT)
    t0 = time.time()
    while not os.path.exists(os.path.join(st, "ready.json")):
        if srv.poll() is not None:
            print("fvcheckd serve died:", open(os.path.join(a.work, "serve.log")).read()[-2000:])
            return 2
        time.sleep(0.5)
        if time.time() - t0 > 900:
            print("fvcheckd not ready after 900 s")
            srv.kill()
            return 2
    print(f"fvcheckd ready after {time.time() - t0:.1f} s; {len(muts)} mutants")

    def warm(mu):
        t = time.time()
        p = subprocess.run(["python3", "-I", a.fvcheckd, "check-delta", "--state", st, "--delta",
                            os.path.join(a.work, mu["id"] + ".delta")],
                           capture_output=True, text=True)
        try:
            j = json.loads(p.stdout.strip().splitlines()[-1])
        except Exception:
            j = {"verdict": "ERROR", "reason": (p.stdout + p.stderr)[-300:]}
        mu["warm"] = j.get("verdict")
        mu["warm_reason"] = str(j.get("reason"))[:300]
        mu["warm_s"] = round(time.time() - t, 3)
        lg = j.get("legs") if isinstance(j.get("legs"), dict) else {}
        if "warm_g" not in mu:      # first (forward) pass: the second kernel's own status on this delta
            mu["warm_g"] = (lg.get("gruszka") or {}).get("status") if isinstance(lg.get("gruszka"), dict) else None

    def cold(mu):
        t = time.time()
        jf = os.path.join(a.work, mu["id"] + ".cold.json")
        p = subprocess.run([os.path.join(PKGROOT, "check/sound/check-sound.sh"),
                            os.path.join(a.work, mu["id"] + ".eff"), a.challenge, a.config,
                            "--threads", str(a.threads), "--json", jf], capture_output=True, text=True)
        try:
            j = json.load(open(jf))
        except Exception:
            j = {"verdict": "ERROR"}
        mu["cold"] = j.get("verdict")
        mu["cold_reason"] = str(j.get("reason"))[:300]
        lg = j.get("legs") if isinstance(j.get("legs"), dict) else {}
        mu["cold_k2"] = (lg.get("k2") or {}).get("rc") if isinstance(lg.get("k2"), dict) else None
        mu["cold_s"] = round(time.time() - t, 3)
        if a.cleanup:
            for ext in (".eff",):
                try:
                    os.unlink(os.path.join(a.work, mu["id"] + ext))
                except OSError:
                    pass

    for mu in muts:            # warm queries one at a time (the daemon is the system under test)
        warm(mu)
    # second pass in REVERSED order on the same daemon: a different verdict = cross-query state contamination
    first = {mu["id"]: mu["warm"] for mu in muts}
    order_dep = []
    for mu in reversed(muts):
        warm(mu)
        if mu["warm"] != first[mu["id"]]:
            order_dep.append((mu["id"], first[mu["id"]], mu["warm"]))
        mu["warm"] = first[mu["id"]] if mu["warm"] == first[mu["id"]] else f"{first[mu['id']]}|{mu['warm']}"
    for x in order_dep:
        print("ORDER-DEPENDENT", *x)
    # third pass: all deltas CONCURRENTLY (many agents on one daemon); a different verdict = a concurrency defect
    if a.concurrent:
        conc = {}

        def warm_c(mu):
            t = time.time()
            p = subprocess.run(["python3", "-I", a.fvcheckd, "check-delta", "--state", st, "--delta",
                                os.path.join(a.work, mu["id"] + ".delta")],
                               capture_output=True, text=True)
            try:
                v = json.loads(p.stdout.strip().splitlines()[-1]).get("verdict")
            except Exception:
                v = "ERROR"
            conc[mu["id"]] = (v, round(time.time() - t, 3))
        t = time.time()
        with ThreadPoolExecutor(a.concurrent) as pool:
            list(pool.map(warm_c, muts * 2))
        wall = time.time() - t
        diffs = [(mu["id"], first[mu["id"]], conc[mu["id"]][0]) for mu in muts if conc[mu["id"]][0] != first[mu["id"]]]
        for x in diffs:
            print("CONCURRENCY-DEPENDENT", *x)
        print(f"CONCURRENT pass: {2 * len(muts)} queries, {a.concurrent} clients, {wall:.1f} s wall, "
              f"{len(diffs)} verdict differences")
        order_dep += diffs
    with ThreadPoolExecutor(a.jobs) as pool:
        list(pool.map(cold, muts))
    subprocess.run(["python3", "-I", a.fvcheckd, "stop", "--state", st], capture_output=True)
    try:
        srv.wait(30)
    except Exception:
        srv.kill()
    counts = {}
    for mu in muts:
        w, c = mu["warm"], mu["cold"]
        if "ACCEPTED" in w.split("|") and c != "ACCEPTED":
            cl = "CRITICAL"
        elif w in ("FALLBACK_REQUIRED",):
            cl = "FALLBACK"
        elif w != "ACCEPTED" and c == "ACCEPTED":
            cl = "AVAIL"
        elif (w == "ACCEPTED") == (c == "ACCEPTED"):
            cl = "AGREE"
        else:
            cl = "OTHER"
        mu["class"] = cl
        counts[cl] = counts.get(cl, 0) + 1
        if cl != "AGREE":
            print(f"{cl}\t{mu['id']}\t{mu['note']}\tO={mu['overridden']} dirty={mu['dirty']} D={mu['delta_decls']}\t"
                  f"warm={w} ({mu['warm_reason'][:160]})\tcold={c} ({mu['cold_reason'][:160]})")
    # per-leg veto check (gruszka-warm Ref::Main class): the cold second kernel rejects E_eff but the warm second kernel said ok on the
    # delta -> its dirty set missed something. The verdict can still be right (the Lean leg rejects), so only a
    # per-leg comparison sees a weakened veto.
    weak = [mu for mu in muts if mu.get("cold_k2") == 1 and mu.get("warm_g") == "ok"]
    for mu in weak:
        print(f"VETO-WEAK\t{mu['id']}\t{mu['note']}\twarm={mu['warm']} gruszka-warm=ok\tcold k2 rc=1 ({mu['cold_reason'][:120]})")
    if weak:
        counts["VETO-WEAK"] = len(weak)
    json.dump(muts, open(os.path.join(a.work, "results.json"), "w"), indent=1)
    byop = {}
    for mu in muts:
        byop.setdefault(mu["op"], {}).setdefault(f"{mu['warm']}/{mu['cold']}", 0)
        byop[mu["op"]][f"{mu['warm']}/{mu['cold']}"] += 1
    for op, d in sorted(byop.items()):
        print(f"OP {op}: {d}")
    print("RESULT", json.dumps(counts), f"warm median {sorted(m['warm_s'] for m in muts)[len(muts)//2]} s,"
          f" cold median {sorted(m['cold_s'] for m in muts)[len(muts)//2]} s")
    return 1 if counts.get("CRITICAL") or counts.get("VETO-WEAK") or order_dep else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
