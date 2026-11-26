#!/usr/bin/python3 -I
"""Mathlib differential corpus (19 cases: 18 exports + P1-f-builderror) for fvcheckd (warm delta judge).

Runs every case of the Mathlib differential corpus (CASES_JSON below) through fvcheckd in BOTH:
  - check_delta (with base = challenge.export, plus automatic check_full fallback on FALLBACK_REQUIRED)
  - check_full  (standalone full check)
Verifies 100% agreement with `cases.json` `expected_official`!
"""
import argparse, json, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
SRC_DIR = os.path.realpath(os.path.join(HERE, "..", "..", "check", "warm"))
sys.path.insert(0, SRC_DIR)
import fvcheckd  # noqa: E402

LL = "$LIGHT_LEAN"
CASES_JSON = LL + "/publish/Light-Prover/docs/validation/mathlib-differential/cases.json"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="OUTROOT/corpus from mk_mathlib_corpus.sh")
    ap.add_argument("--out", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--bins-dir", default="/scratch/fastverify-next/warm/v1")
    ap.add_argument("--pkgroot", default=LL + "/fastverify")
    ap.add_argument("--threads", type=int, default=16)
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    os.makedirs(args.work, exist_ok=True)
    cases = json.load(open(CASES_JSON))
    fvcheckd_py = os.path.join(SRC_DIR, "fvcheckd.py")

    # Group cases by challenge sha256 so we only start ONE persistent fvcheckd per distinct challenge (P1, P2, P3 = 3 daemons!)
    by_chal = {}
    missing = []
    for name, info in sorted(cases.items()):
        cdir = os.path.join(args.corpus, name)
        sol = os.path.join(cdir, "solution.export")
        chal = os.path.join(cdir, "challenge.export")
        cfg = os.path.join(cdir, "comparator.json")
        if not os.path.isfile(sol):
            missing.append(name)
            continue
        csha = fvcheckd.sha256_file(chal)
        by_chal.setdefault(csha, (chal, []))[1].append((name, sol, cfg, info["expected_official"]))

    rows = []
    fails = 0
    for csha, (chal_path, items) in sorted(by_chal.items()):
        tag = csha[:12]
        sdir = os.path.join(args.work, f"ml_{tag}")
        shutil.rmtree(sdir, ignore_errors=True)
        print(f"=== Starting fvcheckd for challenge {tag} ({len(items)} cases) ===", flush=True)
        lf = open(sdir + ".log", "w")
        proc = subprocess.Popen([
            "/usr/bin/python3", "-I", fvcheckd_py, "serve",
            "--state", sdir, "--challenge", chal_path, "--challenge-sha256", csha,
            "--config", cfg_path, "--base", chal_path, "--threads", str(args.threads), "--bins-dir", args.bins_dir,
            "--pkgroot", args.pkgroot,
        ], stdout=lf, stderr=subprocess.STDOUT)
        sock = os.path.join(sdir, "sock")
        for _ in range(1800):
            if os.path.exists(sock):
                break
            if proc.poll() is not None:
                lf.close()
                raise RuntimeError(f"fvcheckd {tag} died:\n{open(sdir + '.log').read()}")
            time.sleep(0.1)
        try:
            for name, sol, cfg, exp in items:
                for mode in ("delta", "full"):
                    t0 = time.time()
                    fb = 0
                    if mode == "delta":
                        r = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": sol, "config": cfg, "timeout": 300.0}, 320.0)
                        if r.get("verdict") == "FALLBACK_REQUIRED":
                            fb = 1
                            r = fvcheckd.send_req(sdir, {"op": "check_full", "export": sol, "config": cfg, "timeout": 300.0}, 320.0)
                    else:
                        r = fvcheckd.send_req(sdir, {"op": "check_full", "export": sol, "config": cfg, "timeout": 300.0}, 320.0)
                    dt = round(time.time() - t0, 3)
                    v = r.get("verdict", "ERROR")
                    ok = (v == exp)
                    if not ok:
                        fails += 1
                    st = "PASS" if ok else "FAIL"
                    rows.append(["mathlib-warm", f"{name}/{mode}", exp, r.get("exit"), v, dt, fb, st,
                                 str(r.get("reason", ""))[:120]])
                    print(f"  [{st}] {name}/{mode}: got={v} exp={exp} fb={fb} s={dt} :: {str(r.get('reason',''))[:80]}", flush=True)
        finally:
            try:
                fvcheckd.send_req(sdir, {"op": "stop"}, 10.0)
                proc.wait(timeout=10)
            except Exception:
                proc.kill()
                proc.wait()
            lf.close()

    tsv = os.path.join(args.out, "mathlib-warm.tsv")
    with open(tsv, "w") as f:
        f.write("gate\tcase\texpected\trc\tverdict\tseconds\tfallback\tstatus\treason\n")
        for row in rows:
            f.write("\t".join(str(x).replace("\t", " ").replace("\n", " ") for x in row) + "\n")
    summary = {
        "total": len(rows),
        "pass": sum(1 for r in rows if r[7] == "PASS"),
        "fail": fails,
        "no_export_buildfail": missing,
        "status": "PASS" if fails == 0 else "FAIL",
    }
    with open(os.path.join(args.out, "mathlib-warm.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n=== MATHLIB-WARM SUMMARY: {json.dumps(summary)} ===", flush=True)
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
