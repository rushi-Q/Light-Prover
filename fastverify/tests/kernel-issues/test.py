#!/usr/bin/python3 -I
"""tests/kernel-issues/test.py [WORK] [--warm]

Regression test for upstream Lean kernel / replay issues fixed AFTER v4.36.0 (our deciding kernel is v4.36.0):
  #16489  add_inductive accepts a constructor type with a loose bound variable and stores a different type
  #15100  constructor record whose name differs from the name listed by its inductive type
  #15101  arbitrary quotInfo records treated as canonical (incl. a quot record smuggling an axiom)
  + Replay's unsafe-constructor paths (L8-L10: unsafe ctor with a loose bvar / wrong induct, ctor given as an unsafe
    AXIOM record; each also "-unused" = not in main_thm's closure, so only the kernels can catch it) + a control C0
Builds `inductive T (a : Type) | mk : a -> T a` + a target using T.mk with the OFFICIAL Lean 4.33.1 + official
lean4export (bwrap, no network), crafts 7 exports (mkloose.py) and judges each by every trusted path present:
check/sound/check-sound.sh, check/lowmem/check-sound-lowmem.sh (+ check-sound-ultralowmem.sh when installed),
check/notary/check-notary.sh, check/frontier/check-frontier.sh, and with --warm the warm daemon (check/warm/fvcheckd.py
or $FV_WARM_DIR): check-delta and check-full, plus the daemon-poisoning probe (an honest query after the #15100
check-full must still be ACCEPTED).  FAIL CRITICAL = any ACCEPTED (or CONDITIONAL) of a crafted export; FAIL = the
honest base not accepted, or the warm daemon poisoned.  ~2-4 min on a test host."""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.realpath(__file__))
PKG = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(HERE, "..", "frontier-adversarial"))
import test as FA   # noqa: E402  (build_export, comps_cfg)
sys.path.append(HERE)
import mkloose      # noqa: E402

SOL = """inductive T (a : Type) : Type where
  | mk : a → T a

theorem main_thm (n : Nat) : n + 0 = n := (fun (_ : T Nat) => rfl) (T.mk n)
"""
CHAL = "theorem main_thm (n : Nat) : n + 0 = n := by sorry\n"
CFG = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["main_thm"],
       "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}


def verdict(cmd, jf):
    p = subprocess.run(cmd, capture_output=True, text=True)
    try:
        j = json.load(open(jf))
    except Exception:
        try:
            j = json.loads(p.stdout.strip().splitlines()[-1])
        except Exception:
            j = {}
    return j.get("verdict"), p.returncode, str(j.get("reason"))[:160].replace("\n", " ")


def main(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("work", nargs="?")
    ap.add_argument("--warm", action="store_true")
    ap.add_argument("--threads", type=int, default=4)
    a = ap.parse_args(argv)
    work = a.work or os.path.join((os.environ.get("SCRATCH") or os.environ.get("TMPDIR") or "/tmp"), os.environ.get("USER", "u") + "-kernel-issues")
    shutil.rmtree(work, ignore_errors=True)
    for d in ("ch", "so"):
        os.makedirs(os.path.join(work, d))
    open(os.path.join(work, "ch", "Challenge.lean"), "w").write(CHAL)
    open(os.path.join(work, "so", "Solution.lean"), "w").write(SOL)
    cfgp = os.path.join(work, "comparator.json")
    json.dump(CFG, open(cfgp, "w"))
    comps = json.load(open(os.path.join(PKG, "config", "components.json")))
    lt = comps["lean_toolchains"]["leanprover/lean4:v4.33.1"]
    env = {"T33": lt["prefix"], "EXP": lt["official_lean4export"]["path"]}
    tg = FA.comps_cfg(CFG)
    ce = FA.build_export(os.path.join(work, "ch"), "Challenge", tg, env)
    se = FA.build_export(os.path.join(work, "so"), "Solution", tg, env)
    if not (ce and se):
        print("FAIL setup: official build/export failed")
        print("RESULT FAIL")
        return 1
    cdir = os.path.join(work, "crafted")
    mkloose.main(se, cdir)
    inputs = [("base", se)] + [(r.split("\t")[0], os.path.join(cdir, r.split("\t")[0] + ".export"))
                               for r in open(os.path.join(cdir, "notes.tsv")).read().splitlines() if r]
    paths = [("check-sound", os.path.join(PKG, "check/sound/check-sound.sh")),
             ("check-sound-lowmem", os.path.join(PKG, "check/lowmem/check-sound-lowmem.sh")),
             ("check-sound-ultralowmem", os.path.join(PKG, "check/lowmem/check-sound-ultralowmem.sh")),
             ("check-notary", os.path.join(PKG, "check/notary/check-notary.sh")),
             ("check-frontier", os.path.join(PKG, "check/frontier/check-frontier.sh"))]
    paths = [(n, p) for n, p in paths if os.path.isfile(p)]
    npass = nfail = 0
    rows = []
    for mid, ex in inputs:
        for n, p in paths:
            jf = os.path.join(work, f"{mid}.{n}.json")
            v, rc, why = verdict([p, ex, ce, cfgp, "--threads", str(a.threads), "--json", jf], jf)
            if mid == "base" or mid.startswith("C"):      # honest base and controls must be ACCEPTED
                ok = rc == 0 and v == "ACCEPTED"
                tag = "PASS" if ok else "FAIL"
            else:
                ok = v not in ("ACCEPTED", "CONDITIONAL") and rc not in (0, 3)
                tag = "PASS" if ok else "FAIL CRITICAL"
            npass, nfail = (npass + 1, nfail) if ok else (npass, nfail + 1)
            rows.append(f"{tag} {mid} {n}: rc={rc} {v} {why}")
            if n == "check-sound" and mid != "base" and not mid.startswith("C"):
                try:
                    lg = json.load(open(jf)).get("legs", {})
                except Exception:
                    lg = {}
                if isinstance(lg.get("lean"), dict) and lg["lean"].get("rc") == 0:   # documents the 2nd-kernel reliance
                    rows.append(f"INFO {mid} single-kernel: the official-kernel leg ACCEPTED it alone; "
                                f"second kernel rc={lg.get('k2', {}).get('rc')} (the judge needs both)")
    # warm daemon
    wd = os.environ.get("FV_WARM_DIR") or os.path.join(PKG, "check", "warm")
    fvd = next((c for c in (os.path.join(wd, "fvcheckd.py"), os.path.join(wd, "src", "fvcheckd.py")) if os.path.isfile(c)), None)
    if a.warm and fvd:
        bins = os.environ.get("FV_WARM_BINS") or (wd if os.path.isfile(os.path.join(wd, "ccmp-warm")) else os.path.join(wd, "bin"))
        if not os.path.isfile(os.path.join(bins, "ccmp-warm")) and os.path.isfile(os.path.join(wd, "pins.env")):
            for ln in open(os.path.join(wd, "pins.env")):   # published layout: binaries where pins.env says
                f = ln.split()
                if len(f) >= 4 and f[0] == "PIN" and f[1] == "ccmp_warm":
                    bins = os.path.dirname(f[3])
        st = os.path.join(work, "wst")
        h = hashlib.sha256(open(ce, "rb").read()).hexdigest()

        def serve():
            shutil.rmtree(st, ignore_errors=True)
            pr = subprocess.Popen(["python3", "-I", fvd, "serve", "--state", st, "--challenge", ce, "--challenge-sha256", h,
                                   "--config", cfgp, "--base", se, "--threads", str(a.threads), "--bins-dir", bins],
                                  stdout=open(os.path.join(work, "wserve.log"), "a"), stderr=subprocess.STDOUT)
            for _ in range(300):
                if os.path.exists(os.path.join(st, "ready.json")) or pr.poll() is not None:
                    break
                time.sleep(1)
            return pr

        def q(op, flag, path):
            p = subprocess.run(["python3", "-I", fvd, op, "--state", st, flag, path], capture_output=True, text=True)
            try:
                j = json.loads(p.stdout.strip().splitlines()[-1])
            except Exception:
                j = {}
            return j.get("verdict"), str(j.get("reason"))[:140].replace("\n", " ")

        pr = serve()
        if pr.poll() is not None:
            rows.append("FAIL warm: daemon did not start")
            nfail += 1
        else:
            for mid, ex in inputs[1:]:
                v, why = q("check-full", "--export", ex)
                if mid.startswith("C"):                    # control: must be ACCEPTED
                    ok = v == "ACCEPTED"
                    npass, nfail = (npass + 1, nfail) if ok else (npass, nfail + 1)
                    rows.append(f"{'PASS' if ok else 'FAIL'} {mid} warm-check-full: {v} {why}")
                    continue
                ok = v not in ("ACCEPTED", "CONDITIONAL")
                npass, nfail = (npass + 1, nfail) if ok else (npass, nfail + 1)
                rows.append(f"{'PASS' if ok else 'FAIL CRITICAL'} {mid} warm-check-full: {v} {why}")
                hv, hwhy = q("check-full", "--export", se)   # poisoning probe: an honest query right after
                ok = hv == "ACCEPTED"
                npass, nfail = (npass + 1, nfail) if ok else (npass, nfail + 1)
                rows.append(f"{'PASS' if ok else 'FAIL'} {mid} warm-honest-after: {hv} {hwhy}")
                if not ok:      # restart so the remaining probes are independent
                    subprocess.run(["python3", "-I", fvd, "stop", "--state", st], capture_output=True)
                    pr.wait(30)
                    pr = serve()
            subprocess.run(["python3", "-I", fvd, "stop", "--state", st], capture_output=True)
    elif a.warm:
        rows.append("SKIP warm: no check/warm (FV_WARM_DIR / FV_WARM_BINS)")
    for r in rows:
        print(r)
    print(f"RESULT pass={npass} fail={nfail}")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
