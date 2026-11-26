#!/usr/bin/python3 -I
"""test_warm_record_checks.py BIN [SELFTEST_DIR] : crafted record-check cases for the 4.36 warm delta Lean leg
(`pleanchecker-warm --base B [--base-layer1 L1]`, protocol CHECK_DELTA / CHECK_FULL), the leg ALONE.

Base B = selftest good.export + `def AtkX : Type := Prop` + per-case extras; deltas are self-contained NDJSON exports.
  W1a            B has safe inductive T (recs not exported, T.rec generated in baseEnv); D overrides AtkX (Case 2) and adds
                 `unsafe axiom T.rec : Prop`                                     -> must be REJECTED
  W1b            same with a SAFE `def T.rec : Prop -> Prop`                       -> REJECTED
  W2             B has `def Foo.rec : Prop -> Prop` (clean, unreferenced); D overrides AtkX (Case 2) and adds a fresh inductive
                 Foo (recs not exported): its generated Foo.rec collides with B's def -> REJECTED
  W3             B has `unsafe axiom Foo.rec : Prop`; D adds a fresh inductive Foo (Case 1, pure extension)   -> REJECTED
  W4   (C1)      D adds a fresh inductive whose UNSAFE constructor type has a loose bvar (Case 1)            -> REJECTED
  W5   (C1)      same in Case 2 (with the AtkX override)                                                    -> REJECTED
  W6   (C2)      D adds a fresh safe inductive + `unsafe axiom <it>.mk` as its constructor record (Case 1)   -> REJECTED
  W7   (C2/full) CHECK_FULL of B + `unsafe axiom T.rec` + inductive T                                       -> REJECTED
  S1   (startup) --base-layer1 L1 with L1 = good + `unsafe axiom T.rec`, B = L1 + inductive T               -> refuses to start
  S2   (startup) --base B (same B, no layer1)                                                               -> refuses to start
  C1..C4 controls: fresh valid inductive (Case 1), AtkX override + fresh valid inductive (Case 2), AtkX override only,
                 CHECK_FULL of a valid export                                                               -> ok
Prints TSV rows and 'RESULT pass=N fail=M'."""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "kernel-cves"))
from craft_cves import ExportBuilder, load_export  # noqa: E402

ENV = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1", "LEAN_STACK_SIZE_KB": "917376"}


def add_atkx(b, value_p2p=False):
    s0 = b.sort(b.lvl_zero())
    s1 = b.sort(b.lvl_succ(b.lvl_zero()))
    val = b.forallE(b.name("_"), s0, s0) if value_p2p else s0
    n = b.name("AtkX")
    b.items.append({"def": {"name": n, "levelParams": [], "type": s1, "value": val, "hints": "abbrev", "safety": "safe",
                            "all": [n]}})


def add_prop_ind(b, name, ctor_unsafe_loose=False, recs=False):
    """inductive NAME : Prop | NAME.mk : NAME  (recs not exported unless recs=True is impossible here: always [])"""
    nT, nmk = b.name(name), b.name(name + ".mk")
    s0 = b.sort(b.lvl_zero())
    eT = b.const(nT, [])
    ctor_ty = eT
    if ctor_unsafe_loose:
        # mk : (a : Prop) -> #1  (loose bound variable #1 under one binder) - Lean #16489 shape
        ctor_ty = b.forallE(b.name("a"), s0, b.bvar(1))
    b.items.append({"inductive": {
        "types": [{"name": nT, "levelParams": [], "type": s0, "numParams": 0, "numIndices": 0, "all": [nT],
                   "ctors": [nmk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
        "ctors": [{"name": nmk, "levelParams": [], "type": ctor_ty, "induct": nT, "cidx": 0, "numParams": 0,
                   "numFields": 1 if ctor_unsafe_loose else 0, "isUnsafe": bool(ctor_unsafe_loose)}],
        "recs": []}})


def add_prop_ind_axiom_ctor(b, name):
    """safe inductive NAME : Prop whose constructor record NAME.mk is an UNSAFE AXIOM (Lean #15100 shape)"""
    nT, nmk = b.name(name), b.name(name + ".mk")
    s0 = b.sort(b.lvl_zero())
    b.items.append({"inductive": {
        "types": [{"name": nT, "levelParams": [], "type": s0, "numParams": 0, "numIndices": 0, "all": [nT],
                   "ctors": [nmk], "numNested": 0, "isRec": False, "isUnsafe": False, "isReflexive": False}],
        "ctors": [], "recs": []}})
    b.items.append({"axiom": {"name": nmk, "levelParams": [], "type": b.const(nT, []), "isUnsafe": True}})


def add_unsafe_axiom(b, name):
    b.items.append({"axiom": {"name": b.name(name), "levelParams": [], "type": b.sort(b.lvl_zero()), "isUnsafe": True}})


def add_id_def(b, name):
    s0 = b.sort(b.lvl_zero())
    n = b.name(name)
    b.items.append({"def": {"name": n, "levelParams": [], "type": b.forallE(b.name("p"), s0, s0),
                            "value": b.lam(b.name("p"), s0, b.bvar(0)), "hints": "opaque", "safety": "safe", "all": [n]}})


class Leg:
    def __init__(self, binp, base, layer1=None):
        args = [binp, "--base", str(base), "-j4"] + (["--base-layer1", str(layer1)] if layer1 else [])
        self.p = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                  text=True, env=ENV)
        line = self.p.stdout.readline()
        try:
            self.ready = json.loads(line)
        except Exception:
            self.ready = {"ready": False, "error": f"no ready line ({line!r}, rc={self.p.poll()})"}

    def query(self, cmd, nonce, path):
        self.p.stdin.write(f"{cmd}\t{nonce}\t{path}\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        try:
            return json.loads(line)
        except Exception:
            return {"status": "DIED", "msg": f"{line!r} rc={self.p.poll()}"}

    def close(self):
        try:
            self.p.stdin.write("QUIT\n")
            self.p.stdin.flush()
            self.p.wait(30)
        except Exception:
            self.p.kill()


def main():
    binp = sys.argv[1]
    st = Path(sys.argv[2] if len(sys.argv) > 2 else "/scratch/fastverify-next/selftest")
    hdr, items = load_export(st / "good.export")
    npass = nfail = 0

    def row(ok, cid, want, got, msg):
        nonlocal npass, nfail
        npass += int(ok)
        nfail += int(not ok)
        print(f"{'PASS' if ok else 'FAIL'}\t{cid}\t{want}\t{got}\t{str(msg)[:170]}")

    with tempfile.TemporaryDirectory(prefix="leanleg-warm.") as td:
        td = Path(td)

        def mk(fn, *steps, prefix=True):
            b = ExportBuilder(hdr, items if prefix else [])
            for s in steps:
                s(b)
            p = td / fn
            b.write(p)
            return p

        # ---- bases
        baseA = mk("baseA.export", add_atkx, lambda b: add_prop_ind(b, "T"))                 # W1, W5, C2, C3
        baseB = mk("baseB.export", add_atkx, lambda b: add_id_def(b, "Foo.rec"))             # W2
        baseC = mk("baseC.export", add_atkx, lambda b: add_unsafe_axiom(b, "Foo.rec"))       # W3
        # ---- deltas (self-contained: header + only the delta's names/exprs/declarations)
        dW1a = mk("W1a.export", lambda b: add_atkx(b, True), lambda b: add_unsafe_axiom(b, "T.rec"), prefix=False)
        dW1b = mk("W1b.export", lambda b: add_atkx(b, True), lambda b: add_id_def(b, "T.rec"), prefix=False)
        dW2 = mk("W2.export", lambda b: add_atkx(b, True), lambda b: add_prop_ind(b, "Foo"), prefix=False)
        dW3 = mk("W3.export", lambda b: add_prop_ind(b, "Foo"), prefix=False)
        dW4 = mk("W4.export", lambda b: add_prop_ind(b, "Loose4", ctor_unsafe_loose=True), prefix=False)
        dW5 = mk("W5.export", lambda b: add_atkx(b, True), lambda b: add_prop_ind(b, "Loose5", ctor_unsafe_loose=True),
                 prefix=False)
        dW6 = mk("W6.export", lambda b: add_prop_ind_axiom_ctor(b, "Ax6"), prefix=False)
        dC1 = mk("C1.export", lambda b: add_prop_ind(b, "Good1"), prefix=False)
        dC2 = mk("C2.export", lambda b: add_atkx(b, True), lambda b: add_prop_ind(b, "Good2"), prefix=False)
        dC3 = mk("C3.export", lambda b: add_atkx(b, True), prefix=False)
        fW7 = mk("W7full.export", lambda b: add_unsafe_axiom(b, "T.rec"), lambda b: add_prop_ind(b, "T"))
        fC4 = mk("C4full.export", lambda b: add_prop_ind(b, "Good4"))
        l1S = mk("S1-l1.export", lambda b: add_unsafe_axiom(b, "T.rec"))
        bS = mk("S1-base.export", lambda b: add_unsafe_axiom(b, "T.rec"), lambda b: add_prop_ind(b, "T"))

        def delta_cases(base, cases):
            leg = Leg(binp, base)
            if not leg.ready.get("ready"):
                for cid, want, _ in cases:
                    row(False, cid, want, "base-not-ready", leg.ready)
                leg.close()
                return
            for i, (cid, want, path) in enumerate(cases):
                cmd = "CHECK_FULL" if "full" in path.name else "CHECK_DELTA"
                r = leg.query(cmd, f"n{i}", path)
                got = r.get("status")
                ok = (got == "ok") if want == "ok" else (got in ("reject",))
                row(ok, cid, want, got, f"dirty={r.get('dirty')} {r.get('msg')}")
            leg.close()

        delta_cases(baseA, [("W1a-unsafe-axiom-T.rec-case2", "reject", dW1a), ("W1b-safe-def-T.rec-case2", "reject", dW1b),
                            ("W4-loose-unsafe-ctor-case1", "reject", dW4), ("W5-loose-unsafe-ctor-case2", "reject", dW5),
                            ("W6-unsafe-axiom-as-ctor-case1", "reject", dW6), ("W7-full-unsafe-T.rec", "reject", fW7),
                            ("C1-fresh-ind-case1", "ok", dC1), ("C2-override+fresh-ind-case2", "ok", dC2),
                            ("C3-override-only", "ok", dC3), ("C4-full-valid", "ok", fC4)])
        delta_cases(baseB, [("W2-fresh-ind-vs-clean-def-Foo.rec-case2", "reject", dW2)])
        delta_cases(baseC, [("W3-fresh-ind-vs-unsafe-Foo.rec-case1", "reject", dW3)])
        for cid, kw in (("S1-startup-layer1-unsafe-T.rec", {"layer1": l1S}), ("S2-startup-unsafe-T.rec", {})):
            leg = Leg(binp, bS, **kw)
            ok = not leg.ready.get("ready")
            row(ok, cid, "refuse", "ready" if leg.ready.get("ready") else "refused", leg.ready.get("error", ""))
            leg.close()
        for cid, base in (("C5-startup-valid-baseA", baseA), ("C6-startup-valid-baseC", baseC)):
            leg = Leg(binp, base)
            row(bool(leg.ready.get("ready")), cid, "ready", "ready" if leg.ready.get("ready") else "refused",
                leg.ready.get("error", ""))
            leg.close()
    print(f"binary {binp}")
    print(f"RESULT pass={npass} fail={nfail}")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
