#!/usr/bin/python3 -I
"""Proof-cheating single-module check on fvserve --warm-check (warm delta judge).

Generates the Mathlib-free proof-cheating corpus (`fastverify/tests/cheat-bench/gen.py`),
starts ONE persistent `fvserve --warm-check` server on CHF (false targets: ANY ACCEPT = UNSOUND!)
and CHT (true targets + cheat variants + honest control), and submits ALL single-file cases!

Asserts:
  - 0 cheats ACCEPTED across ALL CHF & CHT cheat cases (sorry, macros, admit, silent sorry,
    custom axiom, homoglyph axiom, native_decide/implemented_by, decide +native, skipKernelTC,
    addDeclCore doCheck:=false, theorem-as-axiom, notation/OfNat/macro_rules statement tricks,
    redefined fixed def).
  - Honest CHT control (T00) ACCEPTED!
"""
import argparse, json, os, shutil, subprocess, sys, time

LL = "$LIGHT_LEAN"
HERE = os.path.dirname(os.path.realpath(__file__))
SRC_DIR = os.path.realpath(os.path.join(HERE, "..", "..", "check", "warm"))
FVSERVE_WARM = os.path.join(SRC_DIR, "fvserve_warm.py")
GEN_PY = LL + "/fastverify/tests/cheat-bench/gen.py"
TC433 = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1")
WS = LL + "/verify/challenge"


def sha256_file(p):
    import hashlib
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--bins-dir", default="/scratch/fastverify-next/warm/v1")
    ap.add_argument("--threads", type=int, default=8)
    args = ap.parse_args()

    os.makedirs(args.work, exist_ok=True)
    os.makedirs(args.out, exist_ok=True)

    corpus = os.path.join(args.work, "corpus")
    shutil.rmtree(corpus, ignore_errors=True)
    subprocess.run(["/usr/bin/python3", "-I", GEN_PY, corpus], check=True)
    cases = json.load(open(os.path.join(corpus, "cases.json")))

    # Build official challenge exports for CHF and CHT via bin/fastverify --preset reference (100% official B0+E0)
    ch_specs = []
    seed_case = {"CHF": "F01-sorry", "CHT": "T00-honest"}
    for ch in ("CHF", "CHT"):
        cdir = os.path.join(corpus, "challenges", ch)
        cexp = os.path.join(cdir, "challenge.export")
        if not os.path.isfile(cexp):
            ref_out = os.path.join(args.work, f"ref_{ch}")
            shutil.rmtree(ref_out, ignore_errors=True)
            subprocess.run([
                LL + "/fastverify/bin/fastverify",
                os.path.join(corpus, "cases", seed_case[ch]), cdir, ref_out,
                "--preset", "reference", "--threads", str(args.threads),
            ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
            shutil.copy2(os.path.join(ref_out, "challenge.export"), cexp)
        csha = sha256_file(cexp)
        ch_specs.append(f"{ch}={cdir}:{csha}")

    # Pick ALL single-file CHF and CHT cases (non-Mathlib, single Solution.lean, excluding infinite-loop F24/F32)
    selected = []
    for cid, info in sorted(cases.items()):
        ch = info["challenge"]
        if ch not in ("CHF", "CHT"):
            continue
        if info.get("mathlib") or cid.startswith(("F24", "F32", "B", "P")):
            continue
        cpath = os.path.join(corpus, "cases", cid, "Solution.lean")
        if not os.path.isfile(cpath):
            continue
        # Only pure single-module cases (fvserve takes a single .lean file; skip multi-file or custom lakefile cases)
        cdir_case = os.path.join(corpus, "cases", cid)
        lean_files = [f for f in os.listdir(cdir_case) if f.endswith(".lean")]
        if len(lean_files) != 1 or any(os.path.isdir(os.path.join(cdir_case, f)) for f in os.listdir(cdir_case) if f != ".lake"):
            continue
        if cid in ("T18-lakefile-lean", "T21-flaky-first-build"):
            continue
        lpath = os.path.join(cdir_case, "lakefile.toml")
        if os.path.isfile(lpath) and "moreLeanArgs" in open(lpath).read():
            continue
        selected.append((cid, ch, info["expected_official"], cpath))

    print(f"=== Selected {len(selected)} single-module cheat-bench cases (CHF + CHT) ===", flush=True)

    sdir = os.path.join(args.work, "fvserve_cheat")
    shutil.rmtree(sdir, ignore_errors=True)
    cmd = [
        "/usr/bin/python3", "-I", FVSERVE_WARM, "serve",
        "--state", sdir,
        "--threads", str(args.threads), "--max-inflight", "2", "--max-batch", "1",
        "--fv", LL + "/fastverify", "--svc-check",
        "--snapshot-header", "",
        "--warm-check", "--warm-bins", args.bins_dir, "--warm-src", SRC_DIR,
        "--attempt-timeout", "45",
    ]
    for sp in ch_specs:
        cmd += ["--pset", sp]

    lf = open(sdir + ".log", "w")
    proc = subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(sdir, "sock")
    for _ in range(1800):
        if os.path.exists(sock):
            time.sleep(0.2)
            break
        if proc.poll() is not None:
            lf.close()
            raise RuntimeError("fvserve died:\n" + open(sdir + ".log").read()[-1200:])
        time.sleep(0.1)

    sys.path.insert(0, SRC_DIR)
    import fvserve_warm as fw

    # Load per-challenge theorem_names so multi-theorem challenges (CHF=3, CHT=5) check EVERY target!
    ch_thms = {}
    for ch in ("CHF", "CHT"):
        cfg = json.load(open(os.path.join(corpus, "challenges", ch, "comparator.json")))
        ch_thms[ch] = list(cfg.get("theorem_names", []))

    rows = []
    crit_fails = 0
    honest_fails = 0
    try:
        for cid, ch, exp, cpath in selected:
            src = open(cpath, encoding="utf-8", errors="replace").read()
            thms = ch_thms[ch]
            t0 = time.time()
            # A multi-theorem solution is ACCEPTED iff EVERY challenge theorem is ACCEPTED.
            v = "ACCEPTED"
            why = ""
            for thm in thms:
                r = fw.request(sdir, {"op": "verify", "pset": ch, "theorem": thm, "source": src}, 90.0)
                rv = r.get("verdict", "NO-VERDICT")
                rwhy = str(r.get("why", ""))
                if rv != "ACCEPTED":
                    v = rv
                    why = f"[{thm}] {rwhy}"
                    break
                why = f"all {len(thms)} targets ACCEPTED"
            dt = round(time.time() - t0, 3)
            if ch == "CHF" or exp == "REJECTED":
                ok = (v != "ACCEPTED")
                if not ok:
                    crit_fails += 1
            else:
                ok = (v == "ACCEPTED")
                if not ok:
                    honest_fails += 1
            rows.append({"case": cid, "challenge": ch, "expected": exp, "verdict": v, "s": dt,
                         "why": why[:120], "pass": ok})
            print(f"  [{'PASS' if ok else 'FAIL'}] {cid:32s} ({ch}) exp={exp:8s} got={v:10s} ({dt}s) :: {why[:70]}", flush=True)
    finally:
        try:
            fw.request(sdir, {"op": "stop"}, 15.0)
            proc.wait(timeout=15)
        except Exception:
            proc.kill(); proc.wait()
        lf.close()

    summary = {
        "total": len(rows), "pass": sum(1 for r in rows if r["pass"]),
        "critical_cheat_accepts": crit_fails, "honest_fails": honest_fails,
        "status": "PASS" if (crit_fails == 0 and honest_fails == 0) else "FAIL",
        "rows": rows,
    }
    out_p = os.path.join(args.out, "cheat-fvserve-warm.json")
    json.dump(summary, open(out_p, "w"), indent=2)
    print(f"\n=== CHEAT-BENCH ON fvserve --warm-check: {summary['pass']}/{summary['total']} PASS (cheat_accepts={crit_fails}) ===", flush=True)
    sys.exit(0 if summary["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
