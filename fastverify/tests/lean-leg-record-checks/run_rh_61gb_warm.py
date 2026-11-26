#!/usr/bin/python3 -I
"""Giant-proof 61.6 GB RH check and benchmark for fvcheckd.

Tests the full 61.6 GB RH honest export (1.48M constants, 175k modules) + ALL 4 published RH mutants (M1-M4)
+ sorryAx edit + 8 concurrent agents hitting ONE persistent 61.6 GB fvcheckd daemon!

1. Extracts tiny (~2-30 KB) minimal deltas for honest_1thm, M1, M2, M3, M4 using C++ `warm-delta-extract decls`
   (~15 s/delta at 4 GB/s) and densely re-indexes each into valid lean4export 3.1.0 NDJSON.
2. Starts ONE persistent fvcheckd daemon on 61.6 GB RH (`orig.export` vs official `verify/challenge/challenge.export`),
   measuring startup_s and exact per-leg RSS.
3. Judges:
   - honest_1thm (5 reps): MUST be ACCEPTED (measures warm 3-leg latency on 61.6 GB!)
   - M1 (early ill-typed proof): MUST be REJECTED
   - M2 (late ill-typed proof): MUST be REJECTED
   - M3 (illegal axiom 51 steps deep, fakeAx): MUST be REJECTED
   - M4 (statement def RiemannZetaZerosOnLine := True): MUST be REJECTED
   - 8 concurrent agents sending honest + M1-M4 simultaneously!
"""
import argparse, concurrent.futures as cf, json, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
SRC_DIR = os.path.realpath(os.environ.get("WARM_SRC_DIR", os.path.join(HERE, "..", "src")))   # the check/warm under test
sys.path.insert(0, SRC_DIR)
import fvcheckd  # noqa: E402

LL = os.environ.get("LIGHT_LEAN") or os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..", ".."))
RH_ORIG = os.environ.get("FV_BENCH_INPUTS", "/scratch/bench-inputs") + "/rh/orig.export"
RH_CHAL = LL + "/verify/challenge/challenge.export"
RH_CFG = os.environ.get("RH_CFG", LL + "/verify/challenge/comparator.leanonly.json")
SPECS_DIR = LL + "/fastverify/tests/sound-gates/specs"


def dense_reindex(raw_jsonl: str, out_ndjson: str) -> int:
    """Densely re-index a small raw JSONL (from warm-delta-extract) into standard lean4export 3.1.0 NDJSON."""
    lines = [ln.strip() for ln in open(raw_jsonl, encoding="utf-8") if ln.strip()]
    meta = lines[0]
    raw_n, raw_l, raw_e, decls = [], [], [], []
    seen_n, seen_l, seen_e = set(), set(), set()
    for ln in lines[1:]:
        obj = json.loads(ln)
        if "in" in obj:
            if obj["in"] not in seen_n:
                seen_n.add(obj["in"]); raw_n.append(obj)
        elif "il" in obj:
            if obj["il"] not in seen_l:
                seen_l.add(obj["il"]); raw_l.append(obj)
        elif "ie" in obj:
            if obj["ie"] not in seen_e:
                seen_e.add(obj["ie"]); raw_e.append(obj)
        else:
            decls.append(obj)
    raw_n.sort(key=lambda o: o["in"])
    raw_l.sort(key=lambda o: o["il"])
    raw_e.sort(key=lambda o: o["ie"])

    nmap = {0: 0}
    lmap = {0: 0}
    emap = {}
    out = [meta]
    for obj in raw_n:
        nid = len(nmap)
        nmap[obj["in"]] = nid
        if "str" in obj:
            out.append(json.dumps({"in": nid, "str": {"pre": nmap[obj["str"]["pre"]], "str": obj["str"]["str"]}}, separators=(",", ":")))
        else:
            out.append(json.dumps({"in": nid, "num": {"pre": nmap[obj["num"]["pre"]], "i": obj["num"]["i"]}}, separators=(",", ":")))
    for obj in raw_l:
        lid = len(lmap)
        lmap[obj["il"]] = lid
        if "succ" in obj:
            out.append(json.dumps({"il": lid, "succ": lmap[obj["succ"]]}, separators=(",", ":")))
        elif "max" in obj:
            out.append(json.dumps({"il": lid, "max": [lmap[obj["max"][0]], lmap[obj["max"][1]]]}, separators=(",", ":")))
        elif "imax" in obj:
            out.append(json.dumps({"il": lid, "imax": [lmap[obj["imax"][0]], lmap[obj["imax"][1]]]}, separators=(",", ":")))
        elif "param" in obj:
            out.append(json.dumps({"il": lid, "param": nmap[obj["param"]]}, separators=(",", ":")))
    for obj in raw_e:
        eid = len(emap)
        emap[obj["ie"]] = eid
        no = {"ie": eid}
        if "bvar" in obj:
            no["bvar"] = obj["bvar"]
        elif "sort" in obj:
            no["sort"] = lmap[obj["sort"]]
        elif "const" in obj:
            no["const"] = {"name": nmap[obj["const"]["name"]], "us": [lmap[u] for u in obj["const"]["us"]]}
        elif "app" in obj:
            no["app"] = {"fn": emap[obj["app"]["fn"]], "arg": emap[obj["app"]["arg"]]}
        elif "lam" in obj:
            v = obj["lam"]
            no["lam"] = {"name": nmap[v["name"]], "type": emap[v["type"]], "body": emap[v["body"]], "binderInfo": v["binderInfo"]}
        elif "forallE" in obj:
            v = obj["forallE"]
            no["forallE"] = {"name": nmap[v["name"]], "type": emap[v["type"]], "body": emap[v["body"]], "binderInfo": v["binderInfo"]}
        elif "letE" in obj:
            v = obj["letE"]
            no["letE"] = {"name": nmap[v["name"]], "type": emap[v["type"]], "value": emap[v["value"]], "body": emap[v["body"]], "nondep": v["nondep"]}
        elif "proj" in obj:
            v = obj["proj"]
            no["proj"] = {"typeName": nmap[v["typeName"]], "idx": v["idx"], "struct": emap[v["struct"]]}
        elif "natVal" in obj:
            no["natVal"] = obj["natVal"]
        elif "strVal" in obj:
            no["strVal"] = obj["strVal"]
        elif "mdata" in obj:
            no["mdata"] = {"expr": emap[obj["mdata"]["expr"]], "data": obj["mdata"]["data"]}
        out.append(json.dumps(no, separators=(",", ":")))

    for obj in decls:
        if "axiom" in obj:
            v = obj["axiom"]
            no = {"axiom": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "isUnsafe": v["isUnsafe"]}}
        elif "def" in obj:
            v = obj["def"]
            no = {"def": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "value": emap[v["value"]], "hints": v["hints"], "safety": v["safety"], "all": [nmap[x] for x in v["all"]]}}
        elif "thm" in obj:
            v = obj["thm"]
            no = {"thm": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "value": emap[v["value"]], "all": [nmap[x] for x in v["all"]]}}
        elif "opaque" in obj:
            v = obj["opaque"]
            no = {"opaque": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "value": emap[v["value"]], "isUnsafe": v.get("isUnsafe", False), "all": [nmap[x] for x in v["all"]]}}
        else:
            no = obj
        out.append(json.dumps(no, separators=(",", ":")))

    with open(out_ndjson, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    return os.path.getsize(out_ndjson)


def parse_spec(path: str):
    """Return (max_off, old_lines, new_lines) from an fvmut .spec file."""
    max_off = 0
    olds, news = [], []
    for raw in open(path, encoding="utf-8"):
        s = raw.strip()
        if s.startswith("E "):
            max_off = max(max_off, int(s.split()[1]))
        elif s.startswith("O "):
            olds.append(s[2:])
        elif s.startswith("N "):
            news.append(s[2:])
    return max_off, olds, news


def get_tree_rss_gb(root_pid: int) -> dict:
    children, comms = {}, {}
    for e in os.listdir("/proc"):
        if not e.isdigit():
            continue
        pid = int(e)
        try:
            with open(f"/proc/{pid}/status") as f:
                ppid, nm, rss = None, "", 0
                for ln in f:
                    if ln.startswith("Name:"): nm = ln.split(":", 1)[1].strip()
                    elif ln.startswith("PPid:"): ppid = int(ln.split(":", 1)[1].strip())
                    elif ln.startswith("VmRSS:"): rss = int(ln.split()[1])
                if ppid is not None:
                    children.setdefault(ppid, []).append(pid)
                    comms[pid] = (nm, rss)
        except Exception:
            pass
    out = {}
    st = [root_pid]
    while st:
        p = st.pop()
        if p in comms:
            nm, rss = comms[p]
            out[nm] = round(out.get(nm, 0.0) + rss / 1048576.0, 2)
        st.extend(children.get(p, []))
    out["total_gb"] = round(sum(out.values()), 2)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--orig", default=RH_ORIG)
    ap.add_argument("--chal", default=RH_CHAL)
    ap.add_argument("--cfg", default=RH_CFG)
    ap.add_argument("--specs-dir", default=SPECS_DIR)
    ap.add_argument("--fvcheckd", default=os.path.join(SRC_DIR, "fvcheckd.py"))
    ap.add_argument("--bins-dir", default=os.environ.get("FV_WARM_BINS", "/scratch/fastverify-next/warm/v1"))
    ap.add_argument("--pkgroot", default=LL + "/fastverify")
    ap.add_argument("--tc36", default=os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0"))
    ap.add_argument("--threads", type=int, default=64)
    args = ap.parse_args()

    os.makedirs(args.work, exist_ok=True)
    os.makedirs(args.out, exist_ok=True)
    extractor = os.path.join(args.bins_dir, "warm-delta-extract")

    # 1. Extract minimal deltas for honest_M2_orig, M1, M2, M3, M4 in parallel!
    jobs = {}
    m2_off, m2_olds, _ = parse_spec(os.path.join(args.specs_dir, "M2.spec"))
    jobs["honest_1thm"] = (m2_off, m2_olds, "ACCEPTED")
    for m in ("M1", "M2", "M3", "M4"):
        off, _, news = parse_spec(os.path.join(args.specs_dir, f"{m}.spec"))
        jobs[m] = (off, news, "REJECTED")

    print(f"=== Extracting 5 minimal deltas from 61.6 GB RH export (parallel C++ backward scan) ===", flush=True)
    t_ex0 = time.time()
    delta_paths = {}
    def _extract(item):
        name, (off, dlines, exp) = item
        dp = os.path.join(args.work, f"rh_{name}.ndjson")
        if os.path.isfile(dp) and os.path.getsize(dp) > 0:
            return name, dp, os.path.getsize(dp), exp
        dlf = os.path.join(args.work, f"rh_{name}.decls.jsonl")
        rawf = os.path.join(args.work, f"rh_{name}.raw.jsonl")
        with open(dlf, "w") as f:
            f.write("\n".join(dlines) + "\n")
        subprocess.run([extractor, "decls", args.orig, str(off + 1024), dlf, rawf], check=True)
        sz = dense_reindex(rawf, dp)
        return name, dp, sz, exp

    with cf.ThreadPoolExecutor(max_workers=5) as ex:
        for name, dp, sz, exp in ex.map(_extract, jobs.items()):
            delta_paths[name] = (dp, sz, exp)
            print(f"  delta {name:12s}: {sz:8d} bytes (expected {exp})", flush=True)
    print(f"Extracted all 5 RH deltas in {time.time()-t_ex0:.1f}s", flush=True)

    # 2. Start ONE persistent fvcheckd daemon on the 61.6 GB RH honest export!
    sdir = os.path.join(args.work, "rh61_fvcheckd")
    shutil.rmtree(sdir, ignore_errors=True)
    chal_sha = fvcheckd.sha256_file(args.chal)
    fvcheckd_py = os.path.realpath(args.fvcheckd)
    print(f"\n=== Starting persistent fvcheckd on 61.6 GB RH (threads={args.threads}) ===", flush=True)
    t_st0 = time.time()
    lf = open(sdir + ".log", "w")
    proc = subprocess.Popen([
        "/usr/bin/python3", "-I", fvcheckd_py, "serve",
        "--state", sdir, "--challenge", args.chal, "--challenge-sha256", chal_sha,
        "--config", RH_CFG, "--base", args.orig, "--threads", str(args.threads), "--bins-dir", args.bins_dir,
        "--pkgroot", args.pkgroot, "--tc36", args.tc36,
    ], stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(sdir, "sock")
    for _ in range(18000):  # up to 30 min (expected ~4-8 min)
        if os.path.exists(sock):
            break
        if proc.poll() is not None:
            lf.close()
            raise RuntimeError(f"RH fvcheckd died:\n{open(sdir + '.log').read()}")
        time.sleep(0.5)
    startup_s = round(time.time() - t_st0, 2)
    ready = json.load(open(os.path.join(sdir, "ready.json")))
    rss_ready = get_tree_rss_gb(proc.pid)
    print(f"61.6 GB RH fvcheckd READY in {startup_s}s, RSS={rss_ready}, legs={ready['legs']}", flush=True)

    rows = []
    fails = 0
    try:
        # 3. Honest 1-thm delta (5 reps) + Empty delta
        empty_d = os.path.join(args.work, "rh_empty.ndjson")
        with open(empty_d, "w") as f:
            f.write('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.33.1"}}}\n')
        r0 = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": empty_d, "config": args.cfg, "timeout": 300.0}, 320.0)
        legs0 = {k: v.get("ms") for k, v in r0.get("legs", {}).items()}
        print(f"  [empty delta] verdict={r0.get('verdict')} wall_ms={r0.get('wall_ms')} legs_ms={legs0}", flush=True)

        hdp, hsz, _ = delta_paths["honest_1thm"]
        honest_ms = []
        for rep in range(5):
            r = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": hdp, "config": args.cfg, "timeout": 300.0}, 320.0)
            honest_ms.append(r.get("wall_ms"))
            if rep == 0:
                ok = (r.get("verdict") == "ACCEPTED")
                if not ok: fails += 1
                rows.append({"case": "honest_1thm", "bytes": hsz, "expected": "ACCEPTED", "verdict": r.get("verdict"),
                             "exit": r.get("exit"), "wall_ms": r.get("wall_ms"), "legs": {k: v.get("ms") for k, v in r.get("legs", {}).items()},
                             "pass": ok, "reason": str(r.get("reason", ""))[:120]})
        print(f"  [honest_1thm ({hsz}B), 5 reps] wall_ms={honest_ms}", flush=True)

        # 4. All 4 published RH mutants M1, M2, M3, M4!
        for m in ("M1", "M2", "M3", "M4"):
            dp, sz, exp = delta_paths[m]
            r = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": dp, "config": args.cfg, "timeout": 300.0}, 320.0)
            ok = (r.get("verdict") == exp)
            if not ok: fails += 1
            rows.append({"case": m, "bytes": sz, "expected": exp, "verdict": r.get("verdict"),
                         "exit": r.get("exit"), "wall_ms": r.get("wall_ms"),
                         "legs": {k: v.get("ms") for k, v in r.get("legs", {}).items()},
                         "pass": ok, "reason": str(r.get("reason", ""))[:120]})
            legsm = {k: v.get("ms") for k, v in r.get("legs", {}).items()}
            print(f"  [{'PASS' if ok else 'FAIL'}] {m} ({sz}B): verdict={r.get('verdict')} (exp {exp}) wall_ms={r.get('wall_ms')} legs={legsm} :: {str(r.get('reason',''))[:80]}", flush=True)

        # 5. 8 concurrent agents hitting the 61.6 GB RH daemon simultaneously!
        t_c0 = time.time()
        c_items = [("honest_1thm", hdp, "ACCEPTED"), ("M1", delta_paths["M1"][0], "REJECTED"),
                   ("M2", delta_paths["M2"][0], "REJECTED"), ("M3", delta_paths["M3"][0], "REJECTED"),
                   ("M4", delta_paths["M4"][0], "REJECTED"), ("honest_1thm", hdp, "ACCEPTED"),
                   ("honest_1thm", hdp, "ACCEPTED"), ("M3", delta_paths["M3"][0], "REJECTED")]
        def _ask(it):
            nm, dp, exp = it
            tq = time.time()
            r = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": dp, "config": args.cfg, "timeout": 300.0}, 320.0)
            return nm, round((time.time() - tq) * 1000.0, 1), r.get("verdict") == exp
        with cf.ThreadPoolExecutor(max_workers=8) as ex:
            c_res = list(ex.map(_ask, c_items))
        c_wall = round(time.time() - t_c0, 3)
        rss_end = get_tree_rss_gb(proc.pid)
        print(f"  [8 concurrent agents on 61.6 GB RH] wall={c_wall}s, ok={sum(x[2] for x in c_res)}/8, results={c_res}, RSS={rss_end}", flush=True)
    finally:
        try:
            fvcheckd.send_req(sdir, {"op": "stop"}, 15.0)
            proc.wait(timeout=15)
        except Exception:
            proc.kill()
            proc.wait()
        lf.close()

    summary = {
        "project": "RH-61.6GB",
        "threads": args.threads,
        "startup_s": startup_s,
        "rss_ready_gb": rss_ready,
        "rss_end_gb": rss_end,
        "legs_ready": ready["legs"],
        "honest_1thm_ms_5reps": honest_ms,
        "rows": rows,
        "concurrent_8": {"wall_s": c_wall, "results": c_res},
        "fail": fails,
        "status": "PASS" if fails == 0 else "FAIL",
    }
    out_json = os.path.join(args.out, "rh-61gb-warm.json")
    with open(out_json, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n=== RH 61.6 GB WARM SUMMARY: {json.dumps(summary, indent=2)} ===", flush=True)
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
