#!/usr/bin/python3 -I
"""tools/fvwork/replay.py - replay a sequence of project states (a real git history, an agent's edit stream) through a
running fvwork daemon and record the edit -> verdict latency of every state. Untrusted measurement code.

  replay.py --state S (--commits DIR [--start I] [--end J] | --git REPO --revs FILE | --edits FILE.jsonl)
            [--think SEC] [--out FILE.tsv] [--mode optimistic|full|interface] [--no-advance] [--concurrency C]

  --commits DIR  directories DIR/NNN-<sha>/ = source trees of consecutive commits (tools/ci/ci-fetch.sh layout)
  --git/--revs   a git repository and a file with one revision per line (oldest first)
  --edits FILE   JSON lines {"label": .., "files": {"rel/path": "content" | null}} = changed files over the CURRENT base
  --think SEC    pause between requests (agent / human think time); the daemon pre-warms the kernel leg meanwhile
  --wait-warm SEC  before each request, wait (at most SEC) until a pre-warmed kernel leg on the current base is ready
                 (PRs that arrive minutes/hours apart: the daemon has re-warmed meanwhile); the wait is not latency
  --concurrency C  C clients submit at once (many agents on one repository; with --no-advance every request is judged
                 against the same base)
Output: one TSV row per state (id, label, verdict, latency_s, queue_s, build_s, export_s, check_s, attempts, dirty, warm,
why, id, export_sha256) + a JSON summary line (median / p90 / max latency, verdict counts) on stdout.
"""
import argparse, json, os, statistics, sys, threading, time

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location("fvwork", os.path.join(os.path.dirname(os.path.realpath(__file__)), "fvwork.py"))
fvwork = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fvwork)

COLS = ["n", "label", "verdict", "latency_s", "queue_s", "materialize_s", "build_s", "export_s", "check_s", "attempts",
        "dirty", "seed", "warm", "base_advanced", "frontier", "ledger", "drift", "why", "id", "export_sha256"]


def row(n, label, r):
    atts = r.get("attempts") or []
    return {"n": n, "label": label, "verdict": r.get("verdict"), "latency_s": r.get("latency_s"),
            "queue_s": r.get("queue_s"), "materialize_s": r.get("materialize_s"), "build_s": r.get("build_s"),
            "export_s": r.get("export_s"), "check_s": r.get("check_s"),
            "attempts": "+".join(f"{a.get('mode')}:{a.get('outcome')}" for a in atts),
            "dirty": "+".join(str((a.get("build") or {}).get("dirty")) for a in atts),
            "seed": "+".join(str((a.get("build") or {}).get("seed")) for a in atts),
            "warm": "+".join("w" if a.get("warm") else "c" for a in atts if "warm" in a),
            "base_advanced": r.get("base_advanced"),
            "frontier": len(r["frontier"]) if isinstance(r.get("frontier"), list) else "",
            "ledger": ("closed=%d new=%d restated=%d" % (len(r["ledger"]["closed_since_base"]), len(r["ledger"]["new_since_base"]),
                                                        len(r["ledger"]["restated_since_base"]))) if r.get("ledger") else "",
            "drift": ("stmt_changed=%s %s" % (r["drift"].get("statement_changed"), ",".join(
                (r["drift"].get("names") or {}).get("STATEMENT-CHANGED", [])[:3]))) if r.get("drift") else "",
            "why": (r.get("why") or "")[:160].replace("\t", " ").replace("\n", " "),
            "id": r.get("id"), "export_sha256": r.get("export_sha256")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--state", required=True)
    ap.add_argument("--commits"); ap.add_argument("--start", type=int, default=0); ap.add_argument("--end", type=int)
    ap.add_argument("--git"); ap.add_argument("--revs"); ap.add_argument("--edits")
    ap.add_argument("--think", type=float, default=0.0); ap.add_argument("--out")
    ap.add_argument("--mode"); ap.add_argument("--no-advance", action="store_true")
    ap.add_argument("--concurrency", type=int, default=1)
    ap.add_argument("--optimistic-only", action="store_true")
    ap.add_argument("--drift", action="store_true")
    ap.add_argument("--merge", action="store_true")
    ap.add_argument("--wait-warm", type=float, default=0.0)
    a = ap.parse_args()
    reqs = []
    if a.commits:
        ds = sorted(d for d in os.listdir(a.commits) if os.path.isdir(os.path.join(a.commits, d)))
        for d in ds:
            i = int(d.split("-")[0])
            if i < a.start or (a.end is not None and i > a.end):
                continue
            reqs.append((d, {"tree": os.path.join(os.path.realpath(a.commits), d)}))
    elif a.git:
        for ln in open(a.revs):
            if ln.strip():
                reqs.append((ln.strip()[:12], {"git": os.path.realpath(a.git), "rev": ln.strip()}))
    elif a.edits:
        for i, ln in enumerate(open(a.edits)):
            if ln.strip():
                e = json.loads(ln)
                reqs.append((e.get("label", f"edit{i}"), {"files": e["files"]}))
    else:
        sys.exit("replay: give --commits, --git/--revs or --edits")
    rows, lock = [], threading.Lock()
    t_begin = time.time()
    out = open(a.out, "w") if a.out else None
    if out:
        out.write("\t".join(COLS) + "\n"); out.flush()

    def wait_warm():
        t0 = time.time()
        while time.time() - t0 < a.wait_warm:
            try:
                st = fvwork.request(a.state, {"op": "status"}, timeout=10)
                if any(w.get("ready") and w.get("snap_is_base") for w in st.get("warm") or []):
                    return round(time.time() - t0, 1)
            except (OSError, ValueError):
                pass
            time.sleep(5)
        return round(time.time() - t0, 1)

    def one(n, label, body):
        if a.wait_warm:
            print(json.dumps({"label": label, "waited_for_warm_s": wait_warm()}), flush=True)
        req = dict(body, op="verify", label=label, advance=not a.no_advance)
        if a.mode:
            req["mode"] = a.mode
        if a.optimistic_only:
            req["optimistic_only"] = True
        if a.drift:
            req["drift"] = True
        if a.merge:
            req["merge"] = True
        t0 = time.time()
        try:
            r = fvwork.request(a.state, req)
        except OSError as e:
            r = {"verdict": "NO-VERDICT", "why": f"client: {e}"}
        r.setdefault("latency_s", round(time.time() - t0, 3))
        x = row(n, label, r)
        with lock:
            rows.append(x)
            if out:
                out.write("\t".join(str(x[c]) for c in COLS) + "\n"); out.flush()
            print(json.dumps(x), flush=True)

    if a.concurrency <= 1:
        for n, (label, body) in enumerate(reqs):
            one(n, label, body)
            if a.think and n + 1 < len(reqs):
                time.sleep(a.think)
    else:
        for k in range(0, len(reqs), a.concurrency):
            th = [threading.Thread(target=one, args=(k + j, lab, b)) for j, (lab, b) in enumerate(reqs[k:k + a.concurrency])]
            for t in th:
                t.start()
            for t in th:
                t.join()
            if a.think:
                time.sleep(a.think)
    lat = sorted(x["latency_s"] for x in rows if isinstance(x["latency_s"], (int, float)))
    wall = time.time() - t_begin
    summ = {"states": len(rows), "verdicts": {v: sum(1 for x in rows if x["verdict"] == v) for v in
                                              sorted(set(x["verdict"] or "?" for x in rows))},
            "wall_s": round(wall, 1), "states_per_min": round(len(rows) / wall * 60, 2) if wall > 0 else None}
    if lat:
        summ.update({"latency_median_s": round(statistics.median(lat), 2),
                     "latency_p90_s": round(lat[min(len(lat) - 1, int(0.9 * len(lat)))], 2),
                     "latency_max_s": round(lat[-1], 2), "latency_sum_s": round(sum(lat), 1)})
    print(json.dumps({"summary": summ}), flush=True)


if __name__ == "__main__":
    main()
