#!/usr/bin/python3 -I
"""fvclient.py — benchmark client of fvserve. Runs on the node of the service (Unix socket).

    fvclient.py seq   --state DIR --pset NAME ATTEMPTS_DIR [--n N] [--out TSV]       one attempt at a time (latency)
    fvclient.py burst --state DIR --pset NAME ATTEMPTS_DIR [--conc C] [--out TSV]     all attempts at once, C connections
    fvclient.py bestof --state DIR --pset NAME --theorem T FILE... [--out TSV]       N attempts of one theorem at once

ATTEMPTS_DIR/<theorem>.lean (batchverify layout). Prints one TSV row per attempt and a summary line.
"""
import argparse, concurrent.futures as cf, json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import fvserve  # noqa: E402

COLS = ["theorem", "file", "kind", "expected", "verdict", "total_s", "queue_s", "batch_s", "batch_size", "build_s", "export_s", "native_s",
        "check_s", "check_wall_s", "nchecks", "why"]


def one(state, pset, thm, path):
    t = time.time()
    if pset.endswith("*"):            # --pset 'p_*': one problem set per theorem (per-problem official challenges)
        pset = pset[:-1] + thm
    r = fvserve.request(state, {"op": "verify", "pset": pset, "theorem": thm, "source": open(path).read()})
    r["client_s"] = round(time.time() - t, 3)
    r["file"] = os.path.basename(path)
    r["path"] = path
    ex = r.get("exports") or []
    ch = r.get("checks") or []
    r["export_s"] = round(sum(e.get("s") or 0 for e in ex), 3)
    r["native_s"] = round(sum(e.get("native_s") or 0 for e in ex), 3)
    r["check_s"] = round(sum(c.get("s") or 0 for c in ch), 3)
    r["check_wall_s"] = round(sum(c.get("check_wall_s") or 0 for c in ch), 3)
    r["nchecks"] = len(ch)
    r["why"] = (r.get("why") or "")[:100].replace("\t", " ").replace("\n", " ")
    return r


def emit(rows, out, t_all):
    lines = ["\t".join(COLS)] + ["\t".join(str(r.get(c, "")) for c in COLS) for r in rows]
    print("\n".join(lines))
    if out:
        with open(out, "w") as f:
            f.write("\n".join(lines) + "\n")
    tot = sorted(r.get("total_s") or 0 for r in rows)
    v = {}
    for r in rows:
        v[r.get("verdict")] = v.get(r.get("verdict"), 0) + 1
    if tot:
        print(json.dumps({"n": len(rows), "wall_s": round(t_all, 3), "per_hour": round(3600 * len(rows) / t_all),
                          "median_total_s": tot[len(tot) // 2], "max_total_s": tot[-1], "verdicts": v}))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["seq", "burst", "bestof", "stream"])
    ap.add_argument("--state", required=True)
    ap.add_argument("--pset", required=True)
    ap.add_argument("--theorem")
    ap.add_argument("--n", type=int, default=0)
    ap.add_argument("--conc", type=int, default=0)
    ap.add_argument("--out")
    ap.add_argument("paths", nargs="+")
    a = ap.parse_args()
    labels = {}
    if a.mode == "bestof":
        jobs = [(a.theorem, p) for p in a.paths]
    elif a.mode == "stream":   # mkstream.py output: batch-KKK/<theorem>.lean in stream order + labels.json
        d = a.paths[0]
        lab = json.load(open(os.path.join(d, "labels.json")))
        jobs = []
        for b in sorted(lab):
            for th, (kind, exp) in sorted(lab[b].items()):
                p = os.path.join(d, b, th + ".lean")
                jobs.append((th, p))
                labels[p] = (kind, exp)
        if a.n:
            jobs = jobs[:a.n]
    else:
        d = a.paths[0]
        jobs = [(f[:-5], os.path.join(d, f)) for f in sorted(os.listdir(d)) if f.endswith(".lean")]
        if a.n:
            jobs = jobs[:a.n]
    t = time.time()
    if a.mode == "seq":
        rows = [one(a.state, a.pset, th, p) for th, p in jobs]
    else:
        with cf.ThreadPoolExecutor(a.conc or len(jobs)) as ex:
            rows = list(ex.map(lambda j: one(a.state, a.pset, *j), jobs))
    if labels:
        for r in rows:
            k = labels.get(r["path"], ("?", "?"))
            r["kind"], r["expected"] = k
        bad = [r for r in rows if r["expected"] == "REJECTED" and r.get("verdict") == "ACCEPTED"]
        miss = [r for r in rows if r.get("verdict") != r["expected"]]
        print(json.dumps({"stream_mismatches": len(miss), "false_accepts": len(bad)}))
    emit(rows, a.out, time.time() - t)


if __name__ == "__main__":
    main()
