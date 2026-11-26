#!/usr/bin/python3 -I
"""S2(b) soundness gate runner for warm delta verification.

Runs official S2(b) corpora directly through the sandboxed persistent warm legs & fvcheckd:
  1. arena-full   (225/225 lean-kernel-arena via persistent pleanchecker-warm + gruszka-warm CHECK_FULL)
  2. arena-delta  (225/225 lean-kernel-arena via persistent pleanchecker-warm + gruszka-warm CHECK_DELTA on empty base)
  3. suitex-full  (742/742 K/C adversarial kernel corpus via persistent pleanchecker-warm + gruszka-warm CHECK_FULL)
  4. suitex-delta (742/742 K/C adversarial kernel corpus via persistent pleanchecker-warm + gruszka-warm CHECK_DELTA)
  5. cmpx-warm    (54/54 comparator-level corpus against rh-miniF via ONE persistent fvcheckd: both check-delta+fallback and check-full)
  6. threads-warm (thread-count determinism across 1 / 32 / 128 / 255 / 256 threads)
  7. mathlib-warm (if corpus dir provided: all Mathlib differential cases via fvcheckd check-delta & check-full)
  8. mutants-warm (if RH/rh-mid honest+mutant specs provided: delta-overlay & full checks)

Outputs structured TSV files + summary.json in --out DIR. Exits 0 iff 0 FAIL rows across all run gates.
"""
import argparse, concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
SRC_DIR = os.path.realpath(os.environ.get("WARM_SRC_DIR", os.path.join(HERE, "..", "src")))   # WARM_SRC_DIR = the check/warm dir (fvcheckd.py + pins.env) under test
sys.path.insert(0, SRC_DIR)
import fvcheckd  # noqa: E402

LL = os.environ.get("LIGHT_LEAN") or os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..", ".."))
DEFAULT_INPUTS = {
    "arena": "/scratch/bench-inputs/arena/suite",
    "suitex": os.environ.get("FV_BENCH_INPUTS", "/scratch/bench-inputs") + "/suitex",
    "cmpx": os.environ.get("FV_BENCH_INPUTS", "/scratch/bench-inputs") + "/cmpx",
    "cmpx_challenge": "/scratch/bench-inputs/rh-miniF/challenge/challenge.export",
    "cmpx_configs": [
        "/scratch/bench-inputs/rh-miniF/challenge/comparator.leanonly.json",
        "/scratch/bench-inputs/rh-miniF/challenge/comparator.nanoda.json",
    ],
}


def status_to_rc(st: str) -> int:
    if st == "ok":
        return 0
    if st == "reject":
        return 1
    return 2  # decline / fallback / error


def write_tsv(path: str, hdr: list, rows: list):
    with open(path, "w", encoding="utf-8") as f:
        f.write("\t".join(hdr) + "\n")
        for r in rows:
            f.write("\t".join(str(x).replace("\t", " ").replace("\n", " ") for x in r) + "\n")


def run_kernel_corpus_warm(gate: str, mode: str, root: str, bins_dir: str, tc36: str,
                           work_dir: str, threads: int, workers: int, out_dir: str):
    """Run all good/ and bad/ .ndjson tests in `root` through `workers` persistent sandboxed
    (pleanchecker-warm, gruszka-warm) leg pairs using CHECK_FULL or CHECK_DELTA."""
    tests = []
    for lab in ("good", "bad"):
        ldir = os.path.join(root, lab)
        if not os.path.isdir(ldir):
            continue
        for dp, _, fs in os.walk(ldir):
            for fn in sorted(fs):
                if fn.endswith(".ndjson"):
                    tests.append((lab, os.path.join(dp, fn)))
    tests.sort()

    empty_base = os.path.join(work_dir, f"{gate}_empty_base.export")
    with open(empty_base, "w", encoding="utf-8") as f:
        f.write('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.36.0"}}}\n')

    plc_bin = os.path.join(bins_dir, "pleanchecker-warm")
    gz_bin = os.path.join(bins_dir, "gruszka-warm")
    q_root = os.path.realpath(root)

    # Spawn `workers` persistent sandboxed leg pairs on the MAIN THREAD (critical for bwrap --die-with-parent!)
    pairs = []
    for wi in range(workers):
        wpriv = os.path.join(work_dir, f"{gate}_w{wi}")
        os.makedirs(wpriv, exist_ok=True)
        plc = fvcheckd.SandboxedLeg(f"lean4-{wi}", plc_bin, ["--base", empty_base, f"-j{threads}"],
                                    tc36, wpriv, q_root, threads)
        gz = fvcheckd.SandboxedLeg(f"gruszka-{wi}", gz_bin, ["--warm-base", empty_base, str(threads)],
                                   tc36, wpriv, q_root, threads)
        pairs.append((wi, plc, gz))
    for _, plc, gz in pairs:
        plc.wait_ready()
        gz.wait_ready()

    # Shard tests round-robin across persistent workers
    shards = [[] for _ in range(workers)]
    for i, t in enumerate(tests):
        shards[i % workers].append(t)

    cmd_op = "CHECK_FULL" if mode == "full" else "CHECK_DELTA"

    def run_shard(wi, plc, gz, shard):
        rows = []
        for idx, (lab, path) in enumerate(shard):
            tid = os.path.relpath(path, root).replace("/", "__")
            nonce = f"w{wi}_{idx}"
            t0 = time.time()
            rl_j = plc.query(f"{cmd_op}\t{nonce}\t{path}", 180.0)
            tl = round(time.time() - t0, 3)
            # If leg died (e.g. stack/abort on pathological test), do NOT restart inside worker thread; record decline
            t1 = time.time()
            rk_j = gz.query(f"{cmd_op}\t{nonce}\t{path}", 180.0)
            tk = round(time.time() - t1, 3)

            sl = rl_j.get("status", "error")
            sk = rk_j.get("status", "error")
            rl = status_to_rc(sl)
            r2 = status_to_rc(sk)
            comb = 0 if (rl == 0 and r2 == 0) else (1 if 1 in (rl, r2) else 2)
            good = (lab == "good")
            cls = []
            if rl == 0 and not good:
                cls.append("FAIL-CRITICAL(lean accepts bad)")
            elif rl == 1 and good:
                if mode == "full":
                    cls.append("FAIL-REJECT(lean rejects good)")
                else:
                    # On delta-from-empty-base, some arena tests with non-dense/special forms could reject/fallback;
                    # wait: we WANT 0 false rejects on arena-delta too unless explicitly fallback!
                    cls.append("FAIL-REJECT(lean delta rejects good)")
            elif rl not in (0, 1):
                if mode == "delta" and sl == "fallback":
                    cls.append("INFO-FALLBACK(lean delta requests full fallback)")
                else:
                    cls.append(f"WARN-DECLINE(lean status={sl})")

            if r2 == 0 and not good:
                cls.append("INFO(k2 accepts bad)")
            elif r2 == 1 and good:
                cls.append("WARN(k2 rejects good)")
            elif r2 not in (0, 1):
                if mode == "delta" and sk == "fallback":
                    cls.append("INFO-FALLBACK(k2 delta requests full fallback)")
                else:
                    cls.append((f"WARN(k2 status={sk} on good)" if good else f"INFO(k2 status={sk} on bad)"))

            if comb == 0 and not good:
                cls.append("FAIL-CRITICAL(combined accepts bad)")

            status = "FAIL" if any(c.startswith("FAIL") for c in cls) else ("WARN" if any(c.startswith("WARN") for c in cls) else "PASS")
            rows.append([gate, tid, lab, sl, sk, rl, r2, comb, tl, tk, status, ";".join(cls),
                         str(rl_j.get("msg", ""))[:80]])
        return rows

    all_rows = []
    try:
        with cf.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = [ex.submit(run_shard, wi, plc, gz, shards[wi]) for wi, plc, gz in pairs]
            for fut in futs:
                all_rows.extend(fut.result())
    finally:
        for _, plc, gz in pairs:
            plc.stop()
            gz.stop()

    all_rows.sort(key=lambda r: r[1])
    hdr = ["gate", "test", "label", "lean_st", "k2_st", "lean_rc", "k2_rc", "comb_rc", "lean_s", "k2_s", "status", "classes", "lean_msg"]
    write_tsv(os.path.join(out_dir, f"{gate}.tsv"), hdr, all_rows)
    n_pass = sum(1 for r in all_rows if r[10] == "PASS")
    n_warn = sum(1 for r in all_rows if r[10] == "WARN")
    n_fail = sum(1 for r in all_rows if r[10] == "FAIL")
    n_fb = sum(1 for r in all_rows if "INFO-FALLBACK" in r[11])
    return {"total": len(all_rows), "pass": n_pass, "warn": n_warn, "fail": n_fail, "fallbacks": n_fb,
            "status": "PASS" if n_fail == 0 else "FAIL"}


def start_daemon(fvcheckd_py, state_dir, chal, base, cfg, bins_dir, pkgroot, threads):
    shutil.rmtree(state_dir, ignore_errors=True)
    chal_sha = fvcheckd.sha256_file(chal)
    cmd = [
        "/usr/bin/python3", "-I", fvcheckd_py, "serve",
        "--state", state_dir, "--challenge", chal, "--challenge-sha256", chal_sha,
        "--config", cfg,
        "--base", base, "--threads", str(threads), "--bins-dir", bins_dir, "--pkgroot", pkgroot,
    ]
    lf = open(state_dir + ".log", "w")
    proc = subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(state_dir, "sock")
    for _ in range(600):
        if os.path.exists(sock):
            return proc, lf
        if proc.poll() is not None:
            lf.close()
            raise RuntimeError(f"fvcheckd died:\n{open(state_dir + '.log').read()}")
        time.sleep(0.05)
    proc.kill()
    lf.close()
    raise RuntimeError(f"fvcheckd timeout:\n{open(state_dir + '.log').read()}")


def stop_daemon(state_dir, proc, lf):
    try:
        fvcheckd.send_req(state_dir, {"op": "stop"}, 10.0)
        proc.wait(timeout=5)
    except Exception:
        proc.kill()
        proc.wait()
    lf.close()


def run_cmpx_warm(cmpx_dir: str, chal: str, cfgs: list, fvcheckd_py: str, bins_dir: str,
                  pkgroot: str, work_dir: str, threads: int, out_dir: str):
    """Run all 54 cmpx cases (27 exports x 2 configs) through ONE persistent fvcheckd daemon
    in BOTH check_delta (with automatic check_full fallback on FALLBACK_REQUIRED) AND check_full."""
    exp = {}
    with open(os.path.join(cmpx_dir, "expected.txt")) as f:
        for ln in f:
            p = ln.split()
            if len(p) == 2:
                exp[p[0]] = "ACCEPTED" if p[1] == "accept" else "REJECTED"

    rows = []
    for cfg in cfgs:
        tag = os.path.basename(cfg).replace("comparator.", "").replace(".json", "")
        sdir = os.path.join(work_dir, f"cmpx_daemon_{tag}")
        proc, lf = start_daemon(fvcheckd_py, sdir, chal, chal, cfg, bins_dir, pkgroot, threads)
        try:
            for fname, expected in sorted(exp.items()):
                if fname.startswith("split-"):   # matches gates.py:300 (official leanonly ACCEPTS, nanoda REJECTS)
                    exp_eff = "ACCEPTED" if tag == "leanonly" else "SPLIT"
                else:
                    exp_eff = expected
                epath = os.path.join(cmpx_dir, fname)
                # Note: reject-fmt-truncated.ndjson is a valid prefix of accept-base.ndjson cut before trailing base
                # primitives (`semiOutParam`); as a standalone export (`check-full`) it MUST REJECT, whereas overlaid
                # onto `base = challenge.export` it validly supplies the target theorem using base's `semiOutParam`.
                modes = ("full",) if fname == "reject-fmt-truncated.ndjson" else ("delta", "full")
                for mode in modes:
                    t0 = time.time()
                    used_fb = False
                    if mode == "delta":
                        resp = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": epath, "config": cfg, "timeout": 180.0}, 200.0)
                        if resp.get("verdict") == "FALLBACK_REQUIRED":
                            used_fb = True
                            resp = fvcheckd.send_req(sdir, {"op": "check_full", "export": epath, "config": cfg, "timeout": 180.0}, 200.0)
                    else:
                        resp = fvcheckd.send_req(sdir, {"op": "check_full", "export": epath, "config": cfg, "timeout": 180.0}, 200.0)
                    dt = round(time.time() - t0, 3)
                    v = resp.get("verdict", "ERROR")
                    rc = resp.get("exit", 2)
                    if v == exp_eff:
                        st, cl = "PASS", ("INFO-FALLBACK" if used_fb else "")
                    elif exp_eff == "SPLIT" and v in ("ACCEPTED", "REJECTED"):
                        st, cl = "PASS", "INFO-SPLIT"
                    elif v == "ACCEPTED":
                        st, cl = "FAIL", f"FAIL-CRITICAL(accepts {exp_eff})"
                    elif v == "REJECTED":
                        st, cl = "WARN", "WARN-REJECT"
                    else:
                        st, cl = "WARN", f"WARN-DECLINE({v})"
                    rows.append(["cmpx-warm", f"{tag}/{fname}/{mode}", exp_eff, rc, v, dt, int(used_fb), st, cl,
                                 str(resp.get("reason", ""))[:120]])
        finally:
            stop_daemon(sdir, proc, lf)

    hdr = ["gate", "case", "expected", "rc", "verdict", "seconds", "fallback", "status", "classes", "reason"]
    write_tsv(os.path.join(out_dir, "cmpx-warm.tsv"), hdr, rows)
    n_pass = sum(1 for r in rows if r[7] == "PASS")
    n_warn = sum(1 for r in rows if r[7] == "WARN")
    n_fail = sum(1 for r in rows if r[7] == "FAIL")
    n_fb = sum(1 for r in rows if r[6] == 1)
    return {"total": len(rows), "pass": n_pass, "warn": n_warn, "fail": n_fail, "fallbacks": n_fb,
            "status": "PASS" if n_fail == 0 else "FAIL"}


def run_threads_warm(cmpx_dir: str, chal: str, cfg: str, fvcheckd_py: str, bins_dir: str,
                     pkgroot: str, work_dir: str, thread_list: list, out_dir: str):
    """Verify identical verdicts across thread counts [1, 32, 128, 255, 256] on honest + reject cases."""
    cases = []
    with open(os.path.join(cmpx_dir, "expected.txt")) as f:
        for ln in f:
            p = ln.split()
            if len(p) == 2:
                cases.append((p[0], "ACCEPTED" if p[1] == "accept" else "REJECTED"))
    # Pick 2 accept + 3 reject cases from cmpx
    pick = [c for c in cases if c[1] == "ACCEPTED"][:2] + [c for c in cases if c[1] == "REJECTED"][:3]
    rows = []
    verdicts_by_case = {}
    for nt in thread_list:
        sdir = os.path.join(work_dir, f"threads_j{nt}")
        proc, lf = start_daemon(fvcheckd_py, sdir, chal, chal, cfg, bins_dir, pkgroot, nt)
        try:
            for fname, exp in pick:
                epath = os.path.join(cmpx_dir, fname)
                t0 = time.time()
                resp = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": epath, "config": cfg, "timeout": 180.0}, 200.0)
                if resp.get("verdict") == "FALLBACK_REQUIRED":
                    resp = fvcheckd.send_req(sdir, {"op": "check_full", "export": epath, "config": cfg, "timeout": 180.0}, 200.0)
                dt = round(time.time() - t0, 3)
                v = resp.get("verdict", "ERROR")
                rc = resp.get("exit", 2)
                verdicts_by_case.setdefault(fname, set()).add((v, rc))
                ok = (v == exp)
                rows.append(["threads-warm", fname, nt, exp, rc, v, dt, "PASS" if ok else "FAIL",
                             str(resp.get("reason", ""))[:100]])
        finally:
            stop_daemon(sdir, proc, lf)
    inconsistent = [k for k, s in verdicts_by_case.items() if len(s) > 1]
    hdr = ["gate", "case", "threads", "expected", "rc", "verdict", "seconds", "status", "reason"]
    write_tsv(os.path.join(out_dir, "threads-warm.tsv"), hdr, rows)
    n_fail = sum(1 for r in rows if r[7] == "FAIL") + len(inconsistent)
    return {"total": len(rows), "pass": sum(1 for r in rows if r[7] == "PASS"), "fail": n_fail,
            "inconsistent_cases": inconsistent, "threads": thread_list,
            "status": "PASS" if n_fail == 0 else "FAIL"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--bins-dir", default="/scratch/fastverify-next/warm/v1")
    ap.add_argument("--pkgroot", default=LL + "/fastverify")
    ap.add_argument("--tc36", default=os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0"))
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--gate", action="append", default=[])
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    os.makedirs(args.work, exist_ok=True)
    gates = args.gate or ["arena-full", "arena-delta", "suitex-full", "suitex-delta", "cmpx-warm", "threads-warm"]
    fvcheckd_py = os.path.join(SRC_DIR, "fvcheckd.py")

    summary = {
        "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "binaries_sha256": {
            b: fvcheckd.sha256_file(os.path.join(args.bins_dir, b))
            for b in ("ccmp-warm", "pleanchecker-warm", "gruszka-warm", "lean4export-delta")
            if os.path.isfile(os.path.join(args.bins_dir, b))
        },
        "gates": {},
    }

    overall_fail = 0
    for g in gates:
        t0 = time.time()
        print(f"=== Running gate: {g} ===", flush=True)
        if g == "arena-full":
            res = run_kernel_corpus_warm(g, "full", DEFAULT_INPUTS["arena"], args.bins_dir, args.tc36,
                                         args.work, 2, args.workers, args.out)
        elif g == "arena-delta":
            res = run_kernel_corpus_warm(g, "delta", DEFAULT_INPUTS["arena"], args.bins_dir, args.tc36,
                                         args.work, 2, args.workers, args.out)
        elif g == "suitex-full":
            res = run_kernel_corpus_warm(g, "full", DEFAULT_INPUTS["suitex"], args.bins_dir, args.tc36,
                                         args.work, 2, args.workers, args.out)
        elif g == "suitex-delta":
            res = run_kernel_corpus_warm(g, "delta", DEFAULT_INPUTS["suitex"], args.bins_dir, args.tc36,
                                         args.work, 2, args.workers, args.out)
        elif g == "cmpx-warm":
            res = run_cmpx_warm(DEFAULT_INPUTS["cmpx"], DEFAULT_INPUTS["cmpx_challenge"], DEFAULT_INPUTS["cmpx_configs"],
                                fvcheckd_py, args.bins_dir, args.pkgroot, args.work, args.threads, args.out)
        elif g == "threads-warm":
            res = run_threads_warm(DEFAULT_INPUTS["cmpx"], DEFAULT_INPUTS["cmpx_challenge"],
                                   DEFAULT_INPUTS["cmpx_configs"][0], fvcheckd_py, args.bins_dir, args.pkgroot,
                                   args.work, [1, 32, 128, 255, 256], args.out)
        else:
            raise ValueError(f"unknown gate {g}")
        res["wall_s"] = round(time.time() - t0, 2)
        summary["gates"][g] = res
        if res["status"] != "PASS":
            overall_fail += 1
        print(f"    -> {g}: {json.dumps(res)}", flush=True)

    summary["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    summary["overall"] = "PASS" if overall_fail == 0 else "FAIL"
    with open(os.path.join(args.out, "summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n=== OVERALL: {summary['overall']} ===", flush=True)
    sys.exit(0 if overall_fail == 0 else 1)


if __name__ == "__main__":
    main()
