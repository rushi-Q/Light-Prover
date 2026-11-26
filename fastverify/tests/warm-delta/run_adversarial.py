#!/usr/bin/python3 -I
"""Comprehensive 31-test Adversarial Delta Soundness & Soak Suite for fvcheckd (persistent warm delta judge).

Tests the invariants of the warm delta judge:
  - Honest minimal & full deltas, check-full
  - Axiom / sorryAx / kernel type-mismatch / unsafe / duplicate / cyclic / unclosed attacks
  - Dirty-closure & stale-dependent attacks (1-hop, 2-hop, consistent multi-override, axiom-override, chal-def drift)
  - Atomic inductive block attacks (partial ctor override, k-flag flip, isRec flip, fake ctor on base ind)
  - Kernel-implicit & Quotient fallback invariants (NEVER ACCEPTED!)
  - Protocol/JSON/newline-name injection, malformed JSON, bad config JSON, 40-iter TOCTOU race
  - Cross-query poisoning recovery
  - Conditional mode (NEVER exit 0 / ACCEPTED; returns exit 3 / CONDITIONAL)
  - 500-query memory-leak soak test (RSS tracking of all 3 legs + daemon)
"""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, threading, time


def sha256_file(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for ch in iter(lambda: f.read(1 << 20), b""):
            h.update(ch)
    return h.hexdigest()


class ExportBuilder:
    """Minimal self-contained lean4export 3.1.0 NDJSON builder (optionally extending an existing export)."""
    def __init__(self, prefix_export: str = None):
        self.lines = []
        self.names = {(): 0}
        self.levels = {("zero",): 0}
        self.exprs = {}
        self.n_next = 1
        self.l_next = 1
        self.e_next = 0
        if prefix_export:
            id_to_parts = {0: ()}
            with open(prefix_export, "r", encoding="utf-8") as f:
                for raw in f:
                    ln = raw.rstrip("\r\n")
                    if not ln:
                        continue
                    self.lines.append(ln)
                    obj = json.loads(ln)
                    if "in" in obj:
                        idx = obj["in"]
                        self.n_next = max(self.n_next, idx + 1)
                        if "str" in obj:
                            parts = id_to_parts[obj["str"]["pre"]] + (obj["str"]["str"],)
                            id_to_parts[idx] = parts
                            self.names[parts] = idx
                        elif "num" in obj:
                            parts = id_to_parts[obj["num"]["pre"]] + (obj["num"]["i"],)
                            id_to_parts[idx] = parts
                            self.names[parts] = idx
                    elif "il" in obj:
                        self.l_next = max(self.l_next, obj["il"] + 1)
                    elif "ie" in obj:
                        self.e_next = max(self.e_next, obj["ie"] + 1)
        else:
            self.lines.append('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.36.0"}}}')

    def name(self, dotted: str) -> int:
        parts = tuple(dotted.split(".")) if dotted else ()
        return self._name_parts(parts)

    def name_raw(self, raw_single: str) -> int:
        key = (raw_single,)
        if key in self.names:
            return self.names[key]
        idx = self.n_next
        self.n_next += 1
        self.names[key] = idx
        self.lines.append(json.dumps({"in": idx, "str": {"pre": 0, "str": raw_single}}, separators=(",", ":")))
        return idx

    def _name_parts(self, parts: tuple) -> int:
        if parts in self.names:
            return self.names[parts]
        pre = self._name_parts(parts[:-1])
        idx = self.n_next
        self.n_next += 1
        self.names[parts] = idx
        p = parts[-1]
        self.lines.append(json.dumps({"in": idx, "str": {"pre": pre, "str": p}}, separators=(",", ":")))
        return idx

    def lvl_zero(self) -> int:
        return 0

    def lvl_succ(self, a: int) -> int:
        key = ("succ", a)
        if key in self.levels:
            return self.levels[key]
        idx = self.l_next
        self.l_next += 1
        self.levels[key] = idx
        self.lines.append(json.dumps({"il": idx, "succ": a}, separators=(",", ":")))
        return idx

    def lvl_param(self, nm: str) -> int:
        ni = self.name(nm)
        key = ("param", ni)
        if key in self.levels:
            return self.levels[key]
        idx = self.l_next
        self.l_next += 1
        self.levels[key] = idx
        self.lines.append(json.dumps({"il": idx, "param": ni}, separators=(",", ":")))
        return idx

    def _expr(self, key, rec_body: dict) -> int:
        if key in self.exprs:
            return self.exprs[key]
        idx = self.e_next
        self.e_next += 1
        self.exprs[key] = idx
        obj = {"ie": idx}
        obj.update(rec_body)
        self.lines.append(json.dumps(obj, separators=(",", ":")))
        return idx

    def sort(self, l: int) -> int:
        return self._expr(("sort", l), {"sort": l})

    def bvar(self, i: int) -> int:
        return self._expr(("bvar", i), {"bvar": i})

    def const(self, nm: str, us=()) -> int:
        ni = self.name(nm)
        return self._expr(("const", ni, tuple(us)), {"const": {"name": ni, "us": list(us)}})

    def const_id(self, ni: int, us=()) -> int:
        return self._expr(("const", ni, tuple(us)), {"const": {"name": ni, "us": list(us)}})

    def app(self, fn: int, arg: int) -> int:
        return self._expr(("app", fn, arg), {"app": {"fn": fn, "arg": arg}})

    def lam(self, nm: str, ty: int, body: int, bi: str = "default") -> int:
        ni = self.name(nm)
        return self._expr(("lam", ni, ty, body, bi), {"lam": {"name": ni, "type": ty, "body": body, "binderInfo": bi}})

    def forall(self, nm: str, ty: int, body: int, bi: str = "default") -> int:
        ni = self.name(nm)
        return self._expr(("forallE", ni, ty, body, bi), {"forallE": {"name": ni, "type": ty, "body": body, "binderInfo": bi}})

    def add_axiom(self, nm: str, ty: int, lparams=(), is_unsafe: bool = False):
        ni = self.name(nm)
        lps = [self.name(u) for u in lparams]
        self.lines.append(json.dumps({"axiom": {"name": ni, "levelParams": lps, "type": ty, "isUnsafe": is_unsafe}}, separators=(",", ":")))

    def add_def(self, nm: str, ty: int, val: int, lparams=(), hints="abbrev", safety="safe", raw_name=False):
        ni = self.name_raw(nm) if raw_name else self.name(nm)
        lps = [self.name(u) for u in lparams]
        self.lines.append(json.dumps({"def": {"name": ni, "levelParams": lps, "type": ty, "value": val, "hints": hints, "safety": safety, "all": [ni]}}, separators=(",", ":")))

    def add_thm(self, nm: str, ty: int, val: int, lparams=(), raw_name=False):
        ni = self.name_raw(nm) if raw_name else self.name(nm)
        lps = [self.name(u) for u in lparams]
        self.lines.append(json.dumps({"thm": {"name": ni, "levelParams": lps, "type": ty, "value": val, "all": [ni]}}, separators=(",", ":")))

    def add_inductive_raw(self, ind_obj: dict):
        self.lines.append(json.dumps({"inductive": ind_obj}, separators=(",", ":")))

    def write(self, path: str):
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(self.lines) + "\n")


def add_eq_and_true(b: ExportBuilder):
    """Add valid minimal Eq (with Eq.refl, Eq.rec) and True (with True.intro, True.rec) and MyBool."""
    # Eq.{u} : {α : Sort u} -> α -> α -> Prop
    u = b.lvl_param("u")
    u_nm = b.name("u")
    su = b.sort(u)
    prop = b.sort(b.lvl_zero())
    t1 = b.forall("b", b.bvar(1), prop)
    t2 = b.forall("a", b.bvar(0), t1)
    eq_ty = b.forall("α", su, t2, "implicit")
    eq_c = b.const("Eq", [u])
    # Eq.refl.{u} : {α : Sort u} -> (a : α) -> Eq a a
    refl_ret = b.app(b.app(b.app(eq_c, b.bvar(1)), b.bvar(0)), b.bvar(0))
    refl_ty = b.forall("α", su, b.forall("a", b.bvar(0), refl_ret), "implicit")
    # Eq.rec.{u_1, u} : {α : Sort u} -> {a : α} -> {motive : (x : α) -> Eq a x -> Sort u_1} ->
    #                   motive a (Eq.refl a) -> {x : α} -> (t : Eq a x) -> motive x t
    u1 = b.lvl_param("u_1")
    u1_nm = b.name("u_1")
    su1 = b.sort(u1)
    # Under α(5), a(4), motive(3), refl_case(2), x(1), t(0)
    rec_ret = b.app(b.app(b.bvar(3), b.bvar(1)), b.bvar(0))
    t_ty = b.app(b.app(b.app(eq_c, b.bvar(4)), b.bvar(3)), b.bvar(0))
    # motive : (x : α) -> Eq a x -> Sort u_1 (under α(1), a(0))
    mot_ty = b.forall("x", b.bvar(1), b.forall("h", b.app(b.app(b.app(eq_c, b.bvar(2)), b.bvar(1)), b.bvar(0)), su1))
    # refl_case : motive a (Eq.refl a) (under α(2), a(1), motive(0))
    refl_app = b.app(b.app(b.const("Eq.refl", [u]), b.bvar(2)), b.bvar(1))
    rc_ty = b.app(b.app(b.bvar(0), b.bvar(1)), refl_app)
    rec_ty = b.forall("α", su,
             b.forall("a", b.bvar(0),
             b.forall("motive", mot_ty,
             b.forall("refl", rc_ty,
             b.forall("x", b.bvar(3),
             b.forall("t", t_ty, rec_ret), "implicit")), "implicit"), "implicit"), "implicit")
    # rule rhs: fun α a motive refl_case => refl_case
    rule_rhs = b.lam("α", su,
               b.lam("a", b.bvar(0),
               b.lam("motive", mot_ty,
               b.lam("refl", rc_ty, b.bvar(0)))))
    b.add_inductive_raw({
        "types": [{"name": b.name("Eq"), "levelParams": [u_nm], "type": eq_ty,
                   "numParams": 2, "numIndices": 1, "all": [b.name("Eq")],
                   "ctors": [b.name("Eq.refl")], "numNested": 0, "isRec": False, "isReflexive": False, "isUnsafe": False}],
        "ctors": [{"name": b.name("Eq.refl"), "levelParams": [u_nm], "type": refl_ty,
                   "induct": b.name("Eq"), "cidx": 0, "numParams": 2, "numFields": 0, "isUnsafe": False}],
        "recs":  [{"name": b.name("Eq.rec"), "levelParams": [u1_nm, u_nm], "type": rec_ty,
                   "all": [b.name("Eq")], "numParams": 2, "numIndices": 1, "numMotives": 1, "numMinors": 1,
                   "rules": [{"ctor": b.name("Eq.refl"), "nfields": 0, "rhs": rule_rhs}],
                   "k": True, "isUnsafe": False}],
    })

    # MyBool : Type 0 with MyBool.ff, MyBool.tt, MyBool.rec
    type0 = b.sort(b.lvl_succ(b.lvl_zero()))
    mb_c = b.const("MyBool")
    # MyBool.rec.{u} : {motive : MyBool -> Sort u} -> motive ff -> motive tt -> (t : MyBool) -> motive t
    mb_mot_ty = b.forall("x", mb_c, su)
    mb_ff_ty = b.app(b.bvar(0), b.const("MyBool.ff"))
    mb_tt_ty = b.app(b.bvar(1), b.const("MyBool.tt"))
    mb_rec_ty = b.forall("motive", mb_mot_ty,
                b.forall("ff", mb_ff_ty,
                b.forall("tt", mb_tt_ty,
                b.forall("t", mb_c, b.app(b.bvar(3), b.bvar(0))))), "implicit")
    mb_rhs_ff = b.lam("motive", mb_mot_ty, b.lam("ff", mb_ff_ty, b.lam("tt", mb_tt_ty, b.bvar(1))))
    mb_rhs_tt = b.lam("motive", mb_mot_ty, b.lam("ff", mb_ff_ty, b.lam("tt", mb_tt_ty, b.bvar(0))))
    b.add_inductive_raw({
        "types": [{"name": b.name("MyBool"), "levelParams": [], "type": type0,
                   "numParams": 0, "numIndices": 0, "all": [b.name("MyBool")],
                   "ctors": [b.name("MyBool.ff"), b.name("MyBool.tt")],
                   "numNested": 0, "isRec": False, "isReflexive": False, "isUnsafe": False}],
        "ctors": [
            {"name": b.name("MyBool.ff"), "levelParams": [], "type": mb_c,
             "induct": b.name("MyBool"), "cidx": 0, "numParams": 0, "numFields": 0, "isUnsafe": False},
            {"name": b.name("MyBool.tt"), "levelParams": [], "type": mb_c,
             "induct": b.name("MyBool"), "cidx": 1, "numParams": 0, "numFields": 0, "isUnsafe": False},
        ],
        "recs": [{"name": b.name("MyBool.rec"), "levelParams": [u_nm], "type": mb_rec_ty,
                  "all": [b.name("MyBool")], "numParams": 0, "numIndices": 0, "numMotives": 1, "numMinors": 2,
                  "rules": [
                      {"ctor": b.name("MyBool.ff"), "nfields": 0, "rhs": mb_rhs_ff},
                      {"ctor": b.name("MyBool.tt"), "nfields": 0, "rhs": mb_rhs_tt},
                  ],
                  "k": False, "isUnsafe": False}],
    })


def add_mybool(b: ExportBuilder):
    """Add valid minimal MyBool inductive (assuming Init's Eq/Nat/String/Bool/outParam/etc. already present)."""
    u = b.lvl_param("u")
    u_nm = b.name("u")
    su = b.sort(u)
    type0 = b.sort(b.lvl_succ(b.lvl_zero()))
    mb_c = b.const("MyBool")
    mb_mot_ty = b.forall("x", mb_c, su)
    mb_ff_ty = b.app(b.bvar(0), b.const("MyBool.ff"))
    mb_tt_ty = b.app(b.bvar(1), b.const("MyBool.tt"))
    mb_rec_ty = b.forall("motive", mb_mot_ty,
                b.forall("ff", mb_ff_ty,
                b.forall("tt", mb_tt_ty,
                b.forall("t", mb_c, b.app(b.bvar(3), b.bvar(0))))), "implicit")
    mb_rhs_ff = b.lam("motive", mb_mot_ty, b.lam("ff", mb_ff_ty, b.lam("tt", mb_tt_ty, b.bvar(1))))
    mb_rhs_tt = b.lam("motive", mb_mot_ty, b.lam("ff", mb_ff_ty, b.lam("tt", mb_tt_ty, b.bvar(0))))
    b.add_inductive_raw({
        "types": [{"name": b.name("MyBool"), "levelParams": [], "type": type0,
                   "numParams": 0, "numIndices": 0, "all": [b.name("MyBool")],
                   "ctors": [b.name("MyBool.ff"), b.name("MyBool.tt")],
                   "numNested": 0, "isRec": False, "isReflexive": False, "isUnsafe": False}],
        "ctors": [
            {"name": b.name("MyBool.ff"), "levelParams": [], "type": mb_c,
             "induct": b.name("MyBool"), "cidx": 0, "numParams": 0, "numFields": 0, "isUnsafe": False},
            {"name": b.name("MyBool.tt"), "levelParams": [], "type": mb_c,
             "induct": b.name("MyBool"), "cidx": 1, "numParams": 0, "numFields": 0, "isUnsafe": False},
        ],
        "recs": [{"name": b.name("MyBool.rec"), "levelParams": [u_nm], "type": mb_rec_ty,
                  "all": [b.name("MyBool")], "numParams": 0, "numIndices": 0, "numMotives": 1, "numMinors": 2,
                  "rules": [
                      {"ctor": b.name("MyBool.ff"), "nfields": 0, "rhs": mb_rhs_ff},
                      {"ctor": b.name("MyBool.tt"), "nfields": 0, "rhs": mb_rhs_tt},
                  ],
                  "k": False, "isUnsafe": False}],
    })


INIT_PREFIX = "/scratch/fastverify-next/selftest/good.export"


def build_base_and_challenge(work: str):
    """Build synthetic clean repo base B and challenge C extending real Init primitives (from selftest/good.export)
    with MyBool, chalConst, helper1 -> helper2 -> target."""
    init_prefix = INIT_PREFIX
    def make_common(b: ExportBuilder):
        add_mybool(b)
        mb = b.const("MyBool")
        ff = b.const("MyBool.ff")
        tt = b.const("MyBool.tt")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        # def chalConst : MyBool := MyBool.ff (part of challenge statement!)
        b.add_def("chalConst", mb, ff, hints="abbrev")
        # def helper1 : MyBool := MyBool.ff
        b.add_def("helper1", mb, ff, hints="abbrev")
        # def helper2 : MyBool := helper1
        b.add_def("helper2", mb, b.const("helper1"), hints="abbrev")
        # thm lem1 : Eq MyBool helper1 chalConst := Eq.refl MyBool MyBool.ff
        lem1_ty = b.app(b.app(b.app(eq1, mb), b.const("helper1")), b.const("chalConst"))
        lem1_val = b.app(b.app(refl1, mb), ff)
        b.add_thm("lem1", lem1_ty, lem1_val)
        # target statement: Eq MyBool helper2 chalConst
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        return mb, ff, tt, eq1, refl1, tgt_ty

    # Challenge C: target is a `thm` proved by `sorryAx` (official Lean comparator format!)
    bc = ExportBuilder(init_prefix)
    _, _, _, _, _, tgt_ty = make_common(bc)
    u = bc.lvl_param("u")
    sorry_ty = bc.forall("α", bc.sort(u), bc.forall("synthetic", bc.const("Bool"), bc.bvar(1)))
    bc.add_axiom("sorryAx", sorry_ty, lparams=["u"])
    bc.add_thm("target", tgt_ty, bc.app(bc.app(bc.const("sorryAx", [bc.lvl_zero()]), tgt_ty), bc.const("Bool.false")))
    chal_path = os.path.join(work, "synth_challenge.export")
    bc.write(chal_path)

    # Base B: includes a valid proof of target (`target := lem1`) so we can test stale-dependent & override attacks!
    bb = ExportBuilder(init_prefix)
    mb, ff, tt, eq1, refl1, tgt_ty = make_common(bb)
    bb.add_thm("target", tgt_ty, bb.const("lem1"))
    base_path = os.path.join(work, "synth_base.export")
    bb.write(base_path)

    cfg_path = os.path.join(work, "synth_cfg.json")
    with open(cfg_path, "w") as f:
        json.dump({"challenge_module": "Challenge", "solution_module": "Solution",
                   "theorem_names": ["target"], "definition_names": [], "permitted_axioms": []}, f)
    return chal_path, base_path, cfg_path


def run_fv(fvcheckd: str, args: list):
    p = subprocess.run(["/usr/bin/python3", "-I", fvcheckd] + args,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        j = json.loads(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else {}
    except Exception:
        j = {"raw_stdout": p.stdout, "raw_stderr": p.stderr}
    return p.returncode, j


def get_rss_kb(pid: int) -> int:
    try:
        with open(f"/proc/{pid}/status") as f:
            for ln in f:
                if ln.startswith("VmRSS:"):
                    return int(ln.split()[1])
    except Exception:
        pass
    return -1


def get_tree_rss_kb(root_pid: int) -> dict:
    """Read RSS of root_pid and all descendant processes via /proc."""
    children = {}
    comms = {}
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        pid = int(entry)
        try:
            with open(f"/proc/{pid}/status") as f:
                ppid = None
                name = ""
                rss = 0
                for ln in f:
                    if ln.startswith("Name:"):
                        name = ln.split(":", 1)[1].strip()
                    elif ln.startswith("PPid:"):
                        ppid = int(ln.split(":", 1)[1].strip())
                    elif ln.startswith("VmRSS:"):
                        rss = int(ln.split()[1])
                if ppid is not None:
                    children.setdefault(ppid, []).append(pid)
                    comms[pid] = (name, rss)
        except Exception:
            pass
    out = {}
    stack = [root_pid]
    while stack:
        p = stack.pop()
        if p in comms:
            nm, rss = comms[p]
            out[f"{nm}({p})"] = rss
        stack.extend(children.get(p, []))
    return out


def start_daemon(fvcheckd, state_dir, chal, base, cfg, bins_dir, pkgroot, threads=4,
                 conditional=False, official_chal=None, frontier=None, allow_subset=False):
    shutil.rmtree(state_dir, ignore_errors=True)
    chal_sha = sha256_file(chal)
    cmd = [
        "/usr/bin/python3", "-I", fvcheckd, "serve",
        "--state", state_dir, "--challenge", chal, "--challenge-sha256", chal_sha,
        "--config", cfg,
        "--base", base, "--threads", str(threads), "--bins-dir", bins_dir, "--pkgroot", pkgroot,
    ]
    if allow_subset:
        cmd.append("--allow-theorem-subset")
    if conditional:
        cmd.append("--conditional-mode")
        if official_chal:
            cmd += ["--official-challenge", official_chal, "--official-challenge-sha256", sha256_file(official_chal)]
        if frontier:
            cmd += ["--frontier", frontier]
    log_path = state_dir + ".log"
    lf = open(log_path, "w")
    proc = subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(state_dir, "sock")
    for _ in range(300):
        if os.path.exists(sock):
            return proc, lf, log_path
        if proc.poll() is not None:
            lf.close()
            raise RuntimeError(f"daemon died rc={proc.returncode}:\n{open(log_path).read()}")
        time.sleep(0.05)
    proc.kill()
    lf.close()
    raise RuntimeError(f"daemon timeout:\n{open(log_path).read()}")


def stop_daemon(fvcheckd, state_dir, proc, lf):
    try:
        run_fv(fvcheckd, ["stop", "--state", state_dir])
        proc.wait(timeout=5)
    except Exception:
        proc.kill()
        proc.wait()
    lf.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fvcheckd", required=True)
    ap.add_argument("--bins-dir", required=True)
    ap.add_argument("--pkgroot", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--soak-n", type=int, default=500)
    args = ap.parse_args()

    os.makedirs(args.work, exist_ok=True)
    passed = 0
    failed = 0

    def check(tid: str, desc: str, rc: int, resp: dict, expect_verdict: str, expect_rc: int):
        nonlocal passed, failed
        got_v = resp.get("verdict")
        ok = (got_v == expect_verdict and rc == expect_rc)
        # Also allow expected list
        tag = "PASS" if ok else "FAIL"
        if ok:
            passed += 1
        else:
            failed += 1
        print(f"[{tag}] {tid}: {desc} -> verdict={got_v} (exp {expect_verdict}), rc={rc} (exp {expect_rc}), ms={resp.get('wall_ms')}, reason={str(resp.get('reason',''))[:90]}")
        if not ok:
            print(f"       FULL RESP: {json.dumps(resp)[:400]}")

    def check_not_accepted(tid: str, desc: str, rc: int, resp: dict, allowed_verdicts=("REJECTED", "DECLINED", "FALLBACK_REQUIRED")):
        nonlocal passed, failed
        got_v = resp.get("verdict")
        ok = (got_v in allowed_verdicts and rc != 0)
        tag = "PASS" if ok else "FAIL"
        if ok:
            passed += 1
        else:
            failed += 1
        print(f"[{tag}] {tid}: {desc} -> verdict={got_v} (allowed {allowed_verdicts}), rc={rc}, ms={resp.get('wall_ms')}, reason={str(resp.get('reason',''))[:90]}")
        if not ok:
            print(f"       FULL RESP: {json.dumps(resp)[:400]}")

    # =========================================================================
    # PART A: Synthetic Base B + Challenge C (tests all 26 delta & attack classes)
    # =========================================================================
    chal, base, cfg = build_base_and_challenge(args.work)
    sdir = os.path.join(args.work, "d_synth")
    proc, lf, _ = start_daemon(args.fvcheckd, sdir, chal, base, cfg, args.bins_dir, args.pkgroot)
    try:
        # T01: Empty delta (base already proves target!)
        d = os.path.join(args.work, "t01_empty.ndjson")
        ExportBuilder().write(d)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d, "--config", cfg])
        check("T01", "Empty delta against valid base", rc, j, "ACCEPTED", 0)

        # T02: Minimal delta adding fresh helper + re-proving target directly via Eq.refl
        d02 = os.path.join(args.work, "t02_good_min.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        b.add_def("freshHelper", mb, b.const("MyBool.ff"))
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_thm("target", tgt_ty, b.app(b.app(refl1, mb), b.const("freshHelper")))
        b.write(d02)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02, "--config", cfg])
        check("T02", "Minimal honest delta (fresh def + target override)", rc, j, "ACCEPTED", 0)

        # T03: check-full on valid base
        rc, j = run_fv(args.fvcheckd, ["check-full", "--state", sdir, "--export", base, "--config", cfg])
        check("T03", "check-full on honest export", rc, j, "ACCEPTED", 0)

        # T04: Illegal custom axiom in delta
        d04 = os.path.join(args.work, "t04_cheat_ax.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_axiom("fvCheatAx", tgt_ty)
        b.add_thm("target", tgt_ty, b.const("fvCheatAx"))
        b.write(d04)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d04, "--config", cfg])
        check("T04", "Illegal custom axiom in delta", rc, j, "REJECTED", 1)

        # T05: sorryAx cheat in delta
        d05 = os.path.join(args.work, "t05_sorry.ndjson")
        b = ExportBuilder()
        u = b.lvl_param("u")
        su = b.sort(u)
        sorry_ty = b.forall("α", su, b.forall("synthetic", b.const("MyBool"), b.bvar(1)))
        b.add_axiom("sorryAx", sorry_ty, lparams=["u"])
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_thm("target", tgt_ty, b.app(b.app(b.const("sorryAx", [b.lvl_zero()]), tgt_ty), b.const("MyBool.ff")))
        b.write(d05)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d05, "--config", cfg])
        check("T05", "sorryAx cheat in delta", rc, j, "REJECTED", 1)

        # T06: Ill-typed proof term in delta (kernel rejection)
        d06 = os.path.join(args.work, "t06_illtyped.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_thm("target", tgt_ty, b.const("MyBool.ff"))
        b.write(d06)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d06, "--config", cfg])
        check("T06", "Ill-typed proof term (MyBool.ff as Eq proof)", rc, j, "REJECTED", 1)

        # T07: Altered target theorem statement (Eq ff ff instead of Eq helper2 chalConst)
        d07 = os.path.join(args.work, "t07_wrong_stmt.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        bad_ty = b.app(b.app(b.app(eq1, mb), b.const("MyBool.ff")), b.const("MyBool.ff"))
        b.add_thm("target", bad_ty, b.app(b.app(refl1, mb), b.const("MyBool.ff")))
        b.write(d07)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d07, "--config", cfg])
        check("T07", "Altered target statement (compareAt mismatch)", rc, j, "REJECTED", 1)

        # T08: Unsafe definition used by safe target theorem
        d08 = os.path.join(args.work, "t08_unsafe_def.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        b.add_def("evilUnsafe", mb, b.const("MyBool.ff"), safety="unsafe")
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_thm("target", tgt_ty, b.app(b.app(refl1, mb), b.const("evilUnsafe")))
        b.write(d08)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d08, "--config", cfg])
        check("T08", "Unsafe def referenced by safe target theorem", rc, j, "REJECTED", 1)

        # T09: Duplicate declaration in delta
        d09 = os.path.join(args.work, "t09_dup.ndjson")
        b = ExportBuilder()
        b.add_def("dupD", b.const("MyBool"), b.const("MyBool.ff"))
        b.add_def("dupD", b.const("MyBool"), b.const("MyBool.tt"))
        b.write(d09)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d09, "--config", cfg])
        check_not_accepted("T09", "Duplicate declaration in delta", rc, j, ("REJECTED", "DECLINED"))

        # T10: Duplicate universe parameter in delta
        d10 = os.path.join(args.work, "t10_dup_lp.ndjson")
        b = ExportBuilder()
        b.add_def("dupLP", b.const("MyBool"), b.const("MyBool.ff"), lparams=["u", "u"])
        b.write(d10)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d10, "--config", cfg])
        check("T10", "Duplicate universe param in delta", rc, j, "REJECTED", 1)

        # T11: Cyclic definition in delta (cycA -> cycB -> cycA)
        d11 = os.path.join(args.work, "t11_cycle.ndjson")
        b = ExportBuilder()
        b.add_def("cycA", b.const("MyBool"), b.const("cycB"))
        b.add_def("cycB", b.const("MyBool"), b.const("cycA"))
        b.write(d11)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d11, "--config", cfg])
        check("T11", "Cyclic definitions in delta", rc, j, "REJECTED", 1)

        # T12: Unclosed delta referencing missing constant
        d12 = os.path.join(args.work, "t12_unclosed.ndjson")
        b = ExportBuilder()
        b.add_def("danglingDef", b.const("MyBool"), b.const("GhostConst"))
        b.write(d12)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d12, "--config", cfg])
        check("T12", "Unclosed delta referencing GhostConst", rc, j, "REJECTED", 1)

        # T13: STALE-DEPENDENT ATTACK (override helper1 := MyBool.tt without updating target!)
        d13 = os.path.join(args.work, "t13_stale_dep.ndjson")
        b = ExportBuilder()
        b.add_def("helper1", b.const("MyBool"), b.const("MyBool.tt"))
        b.write(d13)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d13, "--config", cfg])
        check("T13", "Stale-dependent attack: override helper1 without updating target", rc, j, "REJECTED", 1)

        # T14: 2-HOP STALE-DEPENDENT ATTACK (override helper1 + resupply target referencing dirtied helper2 without resupplying helper2)
        d14 = os.path.join(args.work, "t14_stale_2hop.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        b.add_def("helper1", mb, b.const("MyBool.tt"))
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_thm("target", tgt_ty, b.app(b.app(refl1, mb), b.const("MyBool.ff")))
        b.write(d14)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d14, "--config", cfg])
        check("T14", "2-hop stale-dependent attack: helper2 dirtied & omitted", rc, j, "REJECTED", 1)

        # T15: Consistent multi-constant override (change helper1 to opaque/regular def equal to ff, resupply helper2 + target!)
        # Wait: helper1 is referenced by challenge's helper2, which IS in challenge's compareAt slice!
        # Let's test overriding lem1 (NOT in challenge slice!) with a new valid proof + resupplying target := lem1!
        d15 = os.path.join(args.work, "t15_consistent_override.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        b.add_def("newMid", mb, b.const("MyBool.ff"))
        lem1_ty = b.app(b.app(b.app(eq1, mb), b.const("helper1")), b.const("chalConst"))
        b.add_thm("lem1", lem1_ty, b.app(b.app(refl1, mb), b.const("newMid")))
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_thm("target", tgt_ty, b.const("lem1"))
        b.write(d15)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d15, "--config", cfg])
        check("T15", "Consistent multi-constant override (lem1 + dependent target)", rc, j, "ACCEPTED", 0)

        # T16a: Override base lem1 with illegal axiom WITHOUT resupplying target (target dirtied!)
        d16a = os.path.join(args.work, "t16a_ax_override.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        lem1_ty = b.app(b.app(b.app(eq1, mb), b.const("helper1")), b.const("chalConst"))
        b.add_axiom("hiddenAx", lem1_ty)
        b.add_thm("lem1", lem1_ty, b.const("hiddenAx"))
        b.write(d16a)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d16a, "--config", cfg])
        check("T16a", "Override base lem1 with illegal axiom (target dirtied)", rc, j, "REJECTED", 1)

        # T16b: Override base lem1 with illegal axiom AND resupply target := lem1 (checkAxiomsDelta catches hiddenAx!)
        d16b = os.path.join(args.work, "t16b_ax_override_resup.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        lem1_ty = b.app(b.app(b.app(eq1, mb), b.const("helper1")), b.const("chalConst"))
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        b.add_axiom("hiddenAx", lem1_ty)
        b.add_thm("lem1", lem1_ty, b.const("hiddenAx"))
        b.add_thm("target", tgt_ty, b.const("lem1"))
        b.write(d16b)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d16b, "--config", cfg])
        check("T16b", "Override base lem1 with illegal axiom + resupply target", rc, j, "REJECTED", 1)

        # T17: Challenge-definition drift attack (override chalConst from abbrev to regular 1)
        d17 = os.path.join(args.work, "t17_chal_drift.ndjson")
        b = ExportBuilder()
        b.add_def("chalConst", b.const("MyBool"), b.const("MyBool.ff"), hints={"regular": 1})
        b.write(d17)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d17, "--config", cfg])
        check("T17", "Challenge-definition drift (chalConst hints changed)", rc, j, "REJECTED", 1)

        # T18: Partial inductive block override (mutate MyBool.ff ctor only, omit MyBool type & rec)
        d18 = os.path.join(args.work, "t18_partial_ind.ndjson")
        b = ExportBuilder()
        b.add_inductive_raw({
            "types": [],
            "ctors": [{"name": b.name("MyBool.ff"), "levelParams": [], "type": b.const("MyBool"),
                       "induct": b.name("MyBool"), "cidx": 9, "numParams": 0, "numFields": 0, "isUnsafe": False}],
            "recs": [],
        })
        b.write(d18)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d18, "--config", cfg])
        check("T18", "Partial inductive override (mutated MyBool.ff cidx=9)", rc, j, "REJECTED", 1)

        # T19: Mutated inductive block in delta (new inductive BadInd with bogus k=true)
        d19 = os.path.join(args.work, "t19_bad_kflag.ndjson")
        b = ExportBuilder()
        type0 = b.sort(b.lvl_succ(b.lvl_zero()))
        u = b.lvl_param("u")
        u_nm = b.name("u")
        su = b.sort(u)
        bi_c = b.const("BadInd")
        mot_ty = b.forall("x", bi_c, su)
        c0_ty = b.app(b.bvar(0), b.const("BadInd.c0"))
        c1_ty = b.app(b.bvar(1), b.const("BadInd.c1"))
        rec_ty = b.forall("motive", mot_ty, b.forall("c0", c0_ty, b.forall("c1", c1_ty, b.forall("t", bi_c, b.app(b.bvar(3), b.bvar(0))))), "implicit")
        r0 = b.lam("motive", mot_ty, b.lam("c0", c0_ty, b.lam("c1", c1_ty, b.bvar(1))))
        r1 = b.lam("motive", mot_ty, b.lam("c0", c0_ty, b.lam("c1", c1_ty, b.bvar(0))))
        b.add_inductive_raw({
            "types": [{"name": b.name("BadInd"), "levelParams": [], "type": type0,
                       "numParams": 0, "numIndices": 0, "all": [b.name("BadInd")],
                       "ctors": [b.name("BadInd.c0"), b.name("BadInd.c1")],
                       "numNested": 0, "isRec": False, "isReflexive": False, "isUnsafe": False}],
            "ctors": [
                {"name": b.name("BadInd.c0"), "levelParams": [], "type": bi_c, "induct": b.name("BadInd"), "cidx": 0, "numParams": 0, "numFields": 0, "isUnsafe": False},
                {"name": b.name("BadInd.c1"), "levelParams": [], "type": bi_c, "induct": b.name("BadInd"), "cidx": 1, "numParams": 0, "numFields": 0, "isUnsafe": False},
            ],
            "recs": [{"name": b.name("BadInd.rec"), "levelParams": [u_nm], "type": rec_ty,
                      "all": [b.name("BadInd")], "numParams": 0, "numIndices": 0, "numMotives": 1, "numMinors": 2,
                      "rules": [{"ctor": b.name("BadInd.c0"), "nfields": 0, "rhs": r0}, {"ctor": b.name("BadInd.c1"), "nfields": 0, "rhs": r1}],
                      "k": True, "isUnsafe": False}],
        })
        b.write(d19)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d19, "--config", cfg])
        check("T19", "Bogus k=true on Type-level 2-ctor inductive", rc, j, "REJECTED", 1)

        # T20: Bogus isRec=true on non-recursive inductive
        d20 = os.path.join(args.work, "t20_bad_isrec.ndjson")
        with open(d19) as f:
            txt = f.read().replace('"k":true', '"k":false').replace('"isRec":false', '"isRec":true')
        with open(d20, "w") as f:
            f.write(txt)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d20, "--config", cfg])
        check("T20", "Bogus isRec=true on non-recursive inductive", rc, j, "REJECTED", 1)

        # T21: Fake ctor injected for clean base inductive MyBool
        d21 = os.path.join(args.work, "t21_fake_ctor.ndjson")
        b = ExportBuilder()
        b.add_inductive_raw({
            "types": [],
            "ctors": [{"name": b.name("MyBool.fake"), "levelParams": [], "type": b.const("MyBool"),
                       "induct": b.name("MyBool"), "cidx": 2, "numParams": 0, "numFields": 0, "isUnsafe": False}],
            "recs": [],
        })
        b.write(d21)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d21, "--config", cfg])
        check("T21", "Fake constructor attached to clean base inductive MyBool", rc, j, "REJECTED", 1)

        # T22: Introduce kernel-implicit constant Nat.add -> MUST FALLBACK_REQUIRED (exit 2, NEVER ACCEPTED!)
        d22 = os.path.join(args.work, "t22_imp_nat.ndjson")
        b = ExportBuilder()
        b.add_def("Nat.add", b.const("MyBool"), b.const("MyBool.ff"))
        b.write(d22)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d22, "--config", cfg])
        check("T22", "Introduce kernel-implicit Nat.add -> FALLBACK_REQUIRED", rc, j, "FALLBACK_REQUIRED", 2)

        # T23: Override kernel-implicit Eq -> MUST FALLBACK_REQUIRED (exit 2, NEVER ACCEPTED!)
        d23 = os.path.join(args.work, "t23_override_eq.ndjson")
        b = ExportBuilder()
        b.add_def("Eq", b.const("MyBool"), b.const("MyBool.ff"))
        b.write(d23)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d23, "--config", cfg])
        check("T23", "Override kernel-implicit Eq -> FALLBACK_REQUIRED", rc, j, "FALLBACK_REQUIRED", 2)

        # T24: Introduce Quot constant -> MUST FALLBACK_REQUIRED (exit 2, NEVER ACCEPTED!)
        d24 = os.path.join(args.work, "t24_quot.ndjson")
        b = ExportBuilder()
        ni = b.name("Quot")
        b.lines.append(json.dumps({"quot": {"name": ni, "levelParams": [], "type": b.const("MyBool"), "kind": "type"}}, separators=(",", ":")))
        b.write(d24)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d24, "--config", cfg])
        check("T24", "Introduce Quot in delta -> FALLBACK_REQUIRED", rc, j, "FALLBACK_REQUIRED", 2)

        # T25: JSON / newline protocol injection in constant name (bad proof whose name tries to forge JSON status=ok!)
        d25 = os.path.join(args.work, "t25_json_inject.ndjson")
        b = ExportBuilder()
        evil_name = 'evil\n{"nonce":"x","status":"ok","msg":"pwned"}\n'
        b.add_def(evil_name, b.sort(b.lvl_zero()), b.sort(b.lvl_succ(b.lvl_zero())), raw_name=True)
        b.write(d25)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d25, "--config", cfg])
        check("T25", "Newline/JSON protocol injection in ill-typed decl name", rc, j, "REJECTED", 1)

        # T26: Malformed / truncated / garbage JSON delta
        d26 = os.path.join(args.work, "t26_corrupt.ndjson")
        with open(d26, "wb") as f:
            f.write(b'{"meta":{}}\n{"in":1,"str":{"pre":0,"str":"\xff\xfeBROKEN\n')
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d26, "--config", cfg])
        check_not_accepted("T26", "Corrupt / invalid-UTF8 JSON delta", rc, j, ("REJECTED", "DECLINED", "ERROR"))

        # T27: Duplicate key in comparator.json config
        cfg_bad = os.path.join(args.work, "t27_bad_cfg.json")
        with open(cfg_bad, "w") as f:
            f.write('{"theorem_names":["target"],"theorem_names":[],"definition_names":[],"permitted_axioms":[]}')
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02, "--config", cfg_bad])
        check("T27", "Duplicate key in comparator.json refused", rc, j, "DECLINED", 2)

        # T28: 40-iteration concurrent in-place TOCTOU rewrite race between good (d02) and bad (d04)
        # Run against a daemon whose base = chal (target is unproved sorryAx!), so ONLY exact good_bytes can EVER be ACCEPTED!
        sdir_race = os.path.join(args.work, "d_race")
        proc_r, lf_r, _ = start_daemon(args.fvcheckd, sdir_race, chal, chal, cfg, args.bins_dir, args.pkgroot)
        try:
            toctou_path = os.path.join(args.work, "t28_race.ndjson")
            good_bytes = open(d02, "rb").read()
            bad_bytes = open(d04, "rb").read()
            good_sha = hashlib.sha256(good_bytes).hexdigest()
            shutil.copyfile(d02, toctou_path)
            stop_flip = threading.Event()
            def flipper():
                i = 0
                while not stop_flip.is_set():
                    try:
                        with open(toctou_path, "wb") as f:
                            f.write(good_bytes if (i % 2 == 0) else bad_bytes)
                    except Exception:
                        pass
                    i += 1
            ft = threading.Thread(target=flipper, daemon=True)
            ft.start()
            bad_accepts = 0
            good_accepts = 0
            rej_or_dec = 0
            for _ in range(40):
                rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir_race, "--delta", toctou_path, "--config", cfg])
                if j.get("verdict") == "ACCEPTED":
                    if j.get("input_sha256") != good_sha:
                        bad_accepts += 1
                    else:
                        good_accepts += 1
                else:
                    rej_or_dec += 1
            stop_flip.set()
            ft.join()
        finally:
            stop_daemon(args.fvcheckd, sdir_race, proc_r, lf_r)
        ok28 = (bad_accepts == 0)
        if ok28:
            passed += 1
        else:
            failed += 1
        print(f"[{'PASS' if ok28 else 'FAIL'}] T28: 40-iter TOCTOU race -> bad_accepts={bad_accepts} (must be 0), good_accepts={good_accepts}, rej/dec={rej_or_dec}")

        # T29: Cross-query poisoning recovery — honest delta MUST STILL BE ACCEPTED after 24 attacks!
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02, "--config", cfg])
        check("T29", "Cross-query poisoning recovery: honest delta still ACCEPTED", rc, j, "ACCEPTED", 0)

        # T31: Memory-leak soak test (N queries alternating good/override/reject)
        rss_samples = {}
        t_soak0 = time.time()
        soak_ok = True
        for qi in range(1, args.soak_n + 1):
            if qi % 3 == 0:
                rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d04, "--config", cfg])
                if j.get("verdict") != "REJECTED":
                    soak_ok = False
            elif qi % 3 == 1:
                rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02, "--config", cfg])
                if j.get("verdict") != "ACCEPTED":
                    soak_ok = False
            else:
                rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d15, "--config", cfg])
                if j.get("verdict") != "ACCEPTED":
                    soak_ok = False
            if qi in (10, 100, args.soak_n // 2, args.soak_n):
                rss_samples[qi] = get_tree_rss_kb(proc.pid)
        soak_s = round(time.time() - t_soak0, 2)
        tot10 = sum(rss_samples.get(10, {}).values())
        totN = sum(rss_samples.get(args.soak_n, {}).values())
        delta_kb = totN - tot10
        # Allow <= 32 MB jitter over 500 queries (GC/allocator pages); true leak would be >>100 MB
        ok31 = soak_ok and delta_kb < 32768
        if ok31:
            passed += 1
        else:
            failed += 1
        print(f"[{'PASS' if ok31 else 'FAIL'}] T31: {args.soak_n}-query soak ({soak_s}s, {soak_s*1000/args.soak_n:.1f} ms/q) -> rss@10={tot10}KB, rss@{args.soak_n}={totN}KB (delta={delta_kb:+d}KB)")
        for qi, mp in sorted(rss_samples.items()):
            print(f"       q={qi:4d}: {mp}")
        # T32 (regression, critical): Per-query config trying to inject sorryAx into permitted_axioms MUST be DECLINED!
        cfg_sorry_req = os.path.join(args.work, "t32_cfg_sorry.json")
        with open(cfg_sorry_req, "w") as f:
            json.dump({"theorem_names": ["target"], "definition_names": [], "permitted_axioms": ["sorryAx"]}, f)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d05, "--config", cfg_sorry_req])
        check("T32", "per-query sorryAx config injection refused", rc, j, "DECLINED", 2)

        # T33 (config pin): Per-query config altering theorem_names MUST be DECLINED!
        cfg_swap_req = os.path.join(args.work, "t33_cfg_swap.json")
        with open(cfg_swap_req, "w") as f:
            json.dump({"theorem_names": ["lem1"], "definition_names": [], "permitted_axioms": []}, f)
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02, "--config", cfg_swap_req])
        check("T33", "Per-query theorem_names substitution refused", rc, j, "DECLINED", 2)

        # T33b: Omitting --config on check-delta uses startup-pinned 0400 config cleanly -> ACCEPTED
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02])
        check("T33b", "Query omitting config uses startup-pinned config", rc, j, "ACCEPTED", 0)

        # T36 (regression): Tiny client timeouts (1e-3, 1e-5, 1e-7 s) MUST NOT desync or DoS the daemon!
        t36_ok = True
        for tmo in ("0.001", "1e-5", "1e-7"):
            rc_t, j_t = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02, "--timeout", tmo])
            if rc_t != 0 or j_t.get("verdict") != "ACCEPTED":
                t36_ok = False
        rc_post, j_post = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d])
        t36_ok = t36_ok and (rc_post == 0 and j_post.get("verdict") == "ACCEPTED")
        if t36_ok:
            passed += 1
        else:
            failed += 1
        print(f"[{'PASS' if t36_ok else 'FAIL'}] T36: tiny client timeout (1e-3..1e-7s) clamped & subsequent honest query ACCEPTED")

        # T37 (Lean issue #15100 leg-crash/respawn regression): Kill pleanchecker-warm mid-service -> next honest query auto-respawns leg -> ACCEPTED!
        t37_ok = False
        # Find pleanchecker-warm child PID of proc and SIGKILL it to simulate an abort/panic crash
        killed_plc = False
        for k_nm in get_tree_rss_kb(proc.pid):
            if k_nm.startswith("pleanchecker-wa("):
                plc_pid = int(k_nm.split("(")[1].rstrip(")"))
                try:
                    os.kill(plc_pid, 9)
                    killed_plc = True
                except OSError:
                    pass
        time.sleep(0.2)
        rc_r1, j_r1 = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d02])
        rc_r2, j_r2 = run_fv(args.fvcheckd, ["check-delta", "--state", sdir, "--delta", d])
        t37_ok = killed_plc and (rc_r1 == 0 and j_r1.get("verdict") == "ACCEPTED") and (rc_r2 == 0 and j_r2.get("verdict") == "ACCEPTED")
        if t37_ok:
            passed += 1
        else:
            failed += 1
        print(f"[{'PASS' if t37_ok else 'FAIL'}] T37: leg-crash auto-respawn (SIGKILL pleanchecker-warm -> honest queries ACCEPTED: r1={j_r1.get('verdict')} r2={j_r2.get('verdict')})")
    finally:
        stop_daemon(args.fvcheckd, sdir, proc, lf)

    # T34: Startup refuses --config containing sorryAx in sound mode!
    sdir_badcfg = os.path.join(args.work, "d_badcfg")
    t34_ok = False
    try:
        p_bc, lf_bc, _ = start_daemon(args.fvcheckd, sdir_badcfg, chal, base, cfg_sorry_req, args.bins_dir, args.pkgroot)
        stop_daemon(args.fvcheckd, sdir_badcfg, p_bc, lf_bc)
    except RuntimeError as e:
        t34_ok = "sorryAx" in str(e)
    if t34_ok:
        passed += 1
    else:
        failed += 1
    print(f"[{'PASS' if t34_ok else 'FAIL'}] T34: Startup refuses --config permitting sorryAx in sound mode")

    # =========================================================================
    # PART B: Conditional Mode Invariant (T30 + T35: Check A at startup, validated F, NEVER exit 0)
    # =========================================================================
    def _build_cond_exports(work_d, corrupt_target=False):
        out_cp = os.path.join(work_d, "c_prime_bad.export" if corrupt_target else "c_prime.export")
        out_bp = os.path.join(work_d, "b_prime.export")
        # Build C' from exact INIT_PREFIX + MyBool + chalConst + helper1 + helper2 + sorryAx + openHelper + target
        b = ExportBuilder(INIT_PREFIX)
        add_mybool(b)
        mb = b.const("MyBool")
        u0 = b.lvl_zero(); u1 = b.lvl_succ(u0)
        eq1 = b.const("Eq", [u1])
        lu = b.lvl_param("u")
        sorry_ty = b.forall("α", b.sort(lu), b.forall("synthetic", b.const("Bool"), b.bvar(1)))
        b.add_axiom("sorryAx", sorry_ty, lparams=["u"])
        b.add_def("chalConst", mb, b.const("MyBool.ff"), hints="abbrev")
        b.add_def("helper1", mb, b.const("MyBool.ff"), hints="abbrev")
        b.add_def("helper2", mb, b.const("helper1"), hints="abbrev")
        tgt_ty = b.app(b.app(b.app(eq1, mb), b.const("helper2")), b.const("chalConst"))
        bad_ty = b.app(b.app(b.app(eq1, mb), b.const("MyBool.ff")), b.const("MyBool.ff"))
        b.add_axiom("openHelper", tgt_ty)
        use_ty = bad_ty if corrupt_target else tgt_ty
        b.add_thm("target", use_ty, b.app(b.app(b.const("sorryAx", [u0]), use_ty), b.const("Bool.false")))
        b.write(out_cp)
        if not corrupt_target:
            b2 = ExportBuilder(INIT_PREFIX)
            add_mybool(b2)
            mb2 = b2.const("MyBool")
            u0_2 = b2.lvl_zero(); u1_2 = b2.lvl_succ(u0_2)
            eq1_2 = b2.const("Eq", [u1_2])
            b2.add_def("chalConst", mb2, b2.const("MyBool.ff"), hints="abbrev")
            b2.add_def("helper1", mb2, b2.const("MyBool.ff"), hints="abbrev")
            b2.add_def("helper2", mb2, b2.const("helper1"), hints="abbrev")
            tgt_ty2 = b2.app(b2.app(b2.app(eq1_2, mb2), b2.const("helper2")), b2.const("chalConst"))
            b2.add_axiom("openHelper", tgt_ty2)
            b2.add_thm("target", tgt_ty2, b2.const("openHelper"))
            b2.write(out_bp)
        return out_cp, out_bp

    # Use chal directly as official C if it matches; note chal in build_base_and_challenge has exact same Bool/MyBool/Eq/chalConst/helper1/helper2/target!
    # Wait: verify C' against chal (Check A checks target & its deps in C' match chal!).
    c_prime_ok, b_prime_ok = _build_cond_exports(args.work, corrupt_target=False)
    c_prime_bad, _ = _build_cond_exports(args.work, corrupt_target=True)
    fr_ok = os.path.join(args.work, "t30_frontier.txt")
    open(fr_ok, "w").write("openHelper\n")
    fr_bad = os.path.join(args.work, "t35_frontier_bad.txt")
    open(fr_bad, "w").write("Lean.ofReduceBool\n")

    # T35a: Forged C' (altered target statement) MUST fail Check A (REJECTED!) at startup in --conditional-mode!
    t35a_ok = False
    try:
        p_fa, lf_fa, _ = start_daemon(args.fvcheckd, os.path.join(args.work, "d_cond_badcp"),
                                      c_prime_bad, b_prime_ok, cfg, args.bins_dir, args.pkgroot,
                                      conditional=True, official_chal=chal, frontier=fr_ok)
        stop_daemon(args.fvcheckd, os.path.join(args.work, "d_cond_badcp"), p_fa, lf_fa)
    except RuntimeError as e:
        t35a_ok = ("Check A" in str(e) and "verdict=REJECTED" in str(e))
    if t35a_ok:
        passed += 1
    else:
        failed += 1
    print(f"[{'PASS' if t35a_ok else 'FAIL'}] T35a: Forged C' (goalpost drift) fails startup Check A in --conditional-mode")

    # T35b: Forbidden compiler trust axiom in --frontier MUST fail closed at startup!
    t35b_ok = False
    try:
        p_fb, lf_fb, _ = start_daemon(args.fvcheckd, os.path.join(args.work, "d_cond_badf"),
                                      c_prime_ok, b_prime_ok, cfg, args.bins_dir, args.pkgroot,
                                      conditional=True, official_chal=chal, frontier=fr_bad)
        stop_daemon(args.fvcheckd, os.path.join(args.work, "d_cond_badf"), p_fb, lf_fb)
    except RuntimeError as e:
        t35b_ok = "trust axiom" in str(e) or "forbidden" in str(e)
    if t35b_ok:
        passed += 1
    else:
        failed += 1
    print(f"[{'PASS' if t35b_ok else 'FAIL'}] T35b: Forbidden trust axiom (Lean.ofReduceBool) in --frontier refused at startup")

    # T30a/b: Valid C' passing Check A at startup -> CONDITIONAL exit 3 (NEVER exit 0); cheat REJECTED; config injection DECLINED!
    sdir_c = os.path.join(args.work, "d_cond")
    proc_c, lf_c, _ = start_daemon(args.fvcheckd, sdir_c, c_prime_ok, b_prime_ok, cfg, args.bins_dir, args.pkgroot,
                                   conditional=True, official_chal=chal, frontier=fr_ok)
    try:
        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir_c, "--delta", d])
        ok30a = (j.get("verdict") == "CONDITIONAL" and rc == 3 and j.get("trust") == "sound-conditional" and j.get("frontier") == ["openHelper"])
        if ok30a:
            passed += 1
        else:
            failed += 1
        print(f"[{'PASS' if ok30a else 'FAIL'}] T30a: Conditional mode honest delta (Check A verified) -> verdict={j.get('verdict')} rc={rc} trust={j.get('trust')} frontier={j.get('frontier')}")

        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir_c, "--delta", d04])
        check("T30b", "Conditional mode axiom cheat still REJECTED", rc, j, "REJECTED", 1)

        rc, j = run_fv(args.fvcheckd, ["check-delta", "--state", sdir_c, "--delta", d05, "--config", cfg_sorry_req])
        check("T30c", "Conditional mode per-query sorryAx config injection refused", rc, j, "DECLINED", 2)
    finally:
        stop_daemon(args.fvcheckd, sdir_c, proc_c, lf_c)

    # =========================================================================
    # PART C: T38 (regression: gruszka-warm ThmVal::Block Ref::Main edge)
    # =========================================================================
    b38 = ExportBuilder(INIT_PREFIX)
    add_mybool(b38)
    mb38 = b38.const("MyBool")
    ff38 = b38.const("MyBool.ff")
    u0_38 = b38.lvl_zero(); u1_38 = b38.lvl_succ(u0_38)
    eq1_38 = b38.const("Eq", [u1_38]); eqr1_38 = b38.const("Eq.refl", [u1_38])
    b38.add_def("helper", mb38, ff38, hints="abbrev")
    h_const38 = b38.const("helper")
    b38.add_def("pinHelper", mb38, h_const38, hints="abbrev")
    eq_ff_ff38 = b38.app(b38.app(b38.app(eq1_38, mb38), ff38), ff38)
    refl_ff38 = b38.app(b38.app(eqr1_38, mb38), ff38)
    mid_proof38 = b38.app(b38.lam("x", mb38, refl_ff38), h_const38)
    b38.add_thm("midThm", eq_ff_ff38, mid_proof38)
    b38.add_thm("target", eq_ff_ff38, b38.const("midThm"))
    t38_base = os.path.join(args.work, "t38_base.export")
    b38.write(t38_base)
    t38_cfg = os.path.join(args.work, "t38_cfg.json")
    with open(t38_cfg, "w") as f:
        json.dump({"theorem_names": ["target"], "definition_names": [], "permitted_axioms": []}, f)
    d38_b = ExportBuilder()
    mb38d = d38_b.const("MyBool"); ff38d = d38_b.const("MyBool.ff")
    u0_38d = d38_b.lvl_zero(); u1_38d = d38_b.lvl_succ(u0_38d)
    eq1_38d = d38_b.const("Eq", [u1_38d]); eqr1_38d = d38_b.const("Eq.refl", [u1_38d])
    d38_b.add_def("helper", d38_b.forall("_", mb38d, mb38d), d38_b.lam("x", mb38d, d38_b.bvar(0)), hints="abbrev")
    eq_ff_ff38d = d38_b.app(d38_b.app(d38_b.app(eq1_38d, mb38d), ff38d), ff38d)
    refl_ff38d = d38_b.app(d38_b.app(eqr1_38d, mb38d), ff38d)
    d38_b.add_thm("midThm", eq_ff_ff38d, d38_b.app(d38_b.lam("x", mb38d, refl_ff38d), d38_b.const("helper")))
    t38_delta = os.path.join(args.work, "t38_delta.ndjson")
    d38_b.write(t38_delta)
    sdir_38 = os.path.join(args.work, "d_t38")
    proc_38, lf_38, _ = start_daemon(args.fvcheckd, sdir_38, t38_base, t38_base, t38_cfg, args.bins_dir, args.pkgroot)
    try:
        rc38, j38 = run_fv(args.fvcheckd, ["check-delta", "--state", sdir_38, "--delta", t38_delta])
        l4_st = j38.get("legs", {}).get("lean4", {}).get("status")
        gz_st = j38.get("legs", {}).get("gruszka", {}).get("status")
        ok38 = (rc38 == 1 and j38.get("verdict") == "REJECTED" and l4_st == "reject" and gz_st == "reject")
        if ok38:
            passed += 1
        else:
            failed += 1
        print(f"[{'PASS' if ok38 else 'FAIL'}] T38: gruszka-warm ThmVal::Block Ref::Main dirty edge -> verdict={j38.get('verdict')} rc={rc38} lean4={l4_st} gruszka={gz_st}")
    finally:
        stop_daemon(args.fvcheckd, sdir_38, proc_38, lf_38)

    print(f"\n=== SUMMARY: {passed} PASS, {failed} FAIL (total {passed+failed}) ===")
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
