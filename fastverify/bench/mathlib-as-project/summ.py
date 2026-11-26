#!/usr/bin/env python3
"""summ.py RUNDIR... : one line per fastverify run: verdict, build option/mode, stage seconds, export size/sha, sched stats
(modules, sum of module walls/cpu, max wall, makespan) from build-fast/sched.out when present."""
import json, os, sys
def sched_stats(p):
    if not os.path.exists(p): return {}
    n = 0; wall = cpu = mx = end = 0.0; j1 = nat = 0; st = {}
    for ln in open(p):
        try: r = json.loads(ln)
        except Exception: continue
        if r.get("event") == "start": st = r
        if r.get("event") == "module":
            n += 1; wall += r.get("wall", 0); cpu += r.get("cpu", 0); mx = max(mx, r.get("wall", 0))
            end = max(end, r.get("start", 0) + r.get("wall", 0)); j1 += bool(r.get("j1")); nat += bool(r.get("native"))
    return {"mods": n, "sum_wall": round(wall, 1), "sum_cpu": round(cpu, 1), "max_wall": round(mx, 1), "makespan": round(end, 1),
            "j1": j1, "zygote": st.get("zygote"), "lean": os.path.basename(os.path.dirname(os.path.dirname(st.get("lean", "") or "x/x/x")))}
for d in sys.argv[1:]:
    try: r = json.load(open(os.path.join(d, "result.json")))
    except Exception as e: print(d, "no result", e); continue
    b = r.get("build") or {}; ss = r.get("stage_seconds", {})
    att = ",".join(f'{a.get("option")}/{a.get("mode")}:{a.get("exit")}' for a in (b.get("attempts") or []))
    s = sched_stats(os.path.join(d, "log", "build-fast", "sched.out"))
    print(json.dumps({"run": os.path.basename(d), "verdict": r.get("verdict"), "trust": r.get("trust"), "build_attempts": att,
                      "stage": ss, "export": [(r.get("export") or {}).get("option"), (r.get("export") or {}).get("size"),
                      ((r.get("export") or {}).get("sha256") or "")[:16]], "chal_sha": (r.get("inputs", {}).get("challenge_export", {}).get("sha256") or "")[:16],
                      "sched": s, "warnings": r.get("warnings", [])[:3]}))
