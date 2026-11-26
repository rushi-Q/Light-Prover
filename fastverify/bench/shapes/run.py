#!/usr/bin/python3 -I
"""run.py ROOT CASE PRESET THREADS [--tag TAG] [-- extra fastverify args]

Runs `bin/fastverify ROOT/CASE/project ROOT/challenge OUT --preset PRESET --threads THREADS` (OUT under ROOT/runs),
then appends one JSON line to ROOT/results.jsonl: verdict, per-stage seconds, build option/toolchain, scheduler stats
(modules, sum of module walls and CPU, scheduler wall), export size/sha256, check legs. The solution export and the
work tree are deleted afterwards (only result.json and the logs stay). The challenge export is given + pinned when
ROOT/challenge/challenge.export exists (sound mode needs --challenge-sha256).
Also usable for any project dir: CASE may be an absolute path to a directory holding project/ (and optional challenge/).
"""
import json, os, subprocess, sys, time, glob

FV = os.environ.get("FASTVERIFY", "$LIGHT_LEAN/fastverify")
WS = os.environ.get("PACKAGES_WS", "$LIGHT_LEAN/verify/challenge")


def sched_stats(logdir):
    out = {}
    for f in glob.glob(os.path.join(logdir, "build-fast*", "sched.out")):
        mods, walls, cpus, start = 0, 0.0, 0.0, None
        for line in open(f):
            try:
                e = json.loads(line)
            except Exception:  # noqa: BLE001
                continue
            if e.get("event") == "start":
                start = {k: e.get(k) for k in ("mods", "jobs", "lean", "zygote", "zygote_prefix", "merged_groups",
                                               "j1_when_saturated", "early_release", "extra_args")}
            elif e.get("event") == "module":
                mods += 1; walls += e.get("wall") or 0; cpus += e.get("cpu") or 0
            elif e.get("event") == "summary":
                out["sched_wall"] = e.get("wall"); out["built"] = e.get("built"); out["failed"] = e.get("failed")
        out.update({"sched_start": start, "module_events": mods, "sum_wall": round(walls, 2), "sum_cpu": round(cpus, 2)})
    return out


def main():
    a = sys.argv[1:]
    extra = []
    if "--" in a:
        i = a.index("--"); extra = a[i + 1:]; a = a[:i]
    tag = ""
    if "--tag" in a:
        i = a.index("--tag"); tag = a[i + 1]; del a[i:i + 2]
    root, case, preset, threads = a
    cdir = case if os.path.isabs(case) else os.path.join(root, case)
    cname = os.path.basename(cdir.rstrip("/"))
    chal = os.path.join(cdir, "challenge") if os.path.isdir(os.path.join(cdir, "challenge")) else os.path.join(root, "challenge")
    stamp = time.strftime("%H%M%S", time.gmtime())
    out = os.path.join(root, "runs", f"{cname}-{preset}{('-' + tag) if tag else ''}-t{threads}-{stamp}")
    os.makedirs(os.path.join(root, "runs"), exist_ok=True)
    args = [f"{FV}/bin/fastverify", os.path.join(cdir, "project"), chal, out, "--preset", preset, "--threads", threads,
            "--packages", WS]
    shaf = os.path.join(chal, "challenge.export.sha256")
    if os.path.exists(shaf) and preset.startswith("sound") and "--challenge-sha256" not in extra:
        args += ["--challenge-sha256", open(shaf).read().split()[0]]
    args += extra
    t0 = time.time()
    with open(out + ".log", "w") as lf:
        rc = subprocess.run(args, stdout=lf, stderr=subprocess.STDOUT).returncode
    wall = time.time() - t0
    rec = {"case": cname, "preset": preset, "tag": tag, "threads": int(threads), "host": os.uname()[1], "rc": rc,
           "wall": round(wall, 2), "out": out, "extra": extra, "when": time.strftime("%FT%TZ", time.gmtime())}
    try:
        r = json.load(open(os.path.join(out, "result.json")))
        rec.update({k: r.get(k) for k in ("verdict", "verdict_fast", "trust", "stage_seconds")})
        b = r.get("build") or {}
        rec["build"] = {"option": b.get("option"), "mode": b.get("mode"), "exit": b.get("exit"),
                        "attempts": [(x.get("option"), x.get("exit"), x.get("seconds"),
                                      (x.get("stage") or {}).get("detail")) for x in b.get("attempts", [])]}
        e = r.get("export") or {}
        rec["export"] = {"option": e.get("option"), "size": e.get("size"), "sha256": e.get("sha256"),
                         "seconds": e.get("seconds")}
        ch = r.get("checks") or {}
        rec["checks"] = {k: {"verdict": v.get("verdict"), "seconds": v.get("seconds"),
                             "legs": {lk: lv.get("seconds") if isinstance(lv, dict) else lv
                                      for lk, lv in (v.get("legs") or {}).items()} if isinstance(v.get("legs"), dict) else None}
                         for k, v in ch.items() if isinstance(v, dict)}
        cj = os.path.join(cdir, "case.json")
        if os.path.exists(cj):
            rec["case_info"] = json.load(open(cj))
    except Exception as ex:  # noqa: BLE001
        rec["error"] = repr(ex)
    rec["sched"] = sched_stats(os.path.join(out, "log"))
    # keep the run small: drop the export and every big log artifact (plan.jsonl of a Mathlib project is ~0.5 GB,
    # merge/, planner/, native/ another ~0.8 GB); keep result.json, sched.out and the small logs
    for dp, dns, fns in os.walk(out, topdown=False):
        for fn in fns:
            fp = os.path.join(dp, fn)
            try:
                if fn == "solution.export" or (os.path.getsize(fp) > 2_000_000 and
                                               fn not in ("sched.out", "result.json", "challenge.export")):
                    os.remove(fp)
            except OSError:
                pass
        for dn in dns:
            try:
                os.rmdir(os.path.join(dp, dn))   # only empty directories
            except OSError:
                pass
    with open(os.path.join(root, "results.jsonl"), "a") as f:
        f.write(json.dumps(rec) + "\n")
    print(json.dumps({k: rec.get(k) for k in ("case", "preset", "rc", "wall", "verdict", "stage_seconds")}))
    print(" sched:", json.dumps(rec["sched"].get("sum_wall")), rec["sched"].get("sched_wall"),
          (rec["sched"].get("sched_start") or {}).get("lean"))


if __name__ == "__main__":
    main()
