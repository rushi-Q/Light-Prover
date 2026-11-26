#!/usr/bin/env python3
"""
fastverify/bench/lowmem/run_c5_cliff.py — survival cliff of 8 and 16 concurrent checks under tight shared cgroup caps.

Tests:
  1. Mixed workload (50% honest, 25% drift, 25% unpermitted axiom) at tighter shared caps:
     - N=8  (thr=2): mem = 8G, 10G, 12G
     - N=16 (thr=2): mem = 12G, 16G, 20G
  2. 100%-honest burst (all N=8 agents submit valid 1.10 GB rh-mid proofs simultaneously, thr=4):
     - N=8  (thr=4): mem = 16G, 20G, 24G, 32G
"""
import json
import os
import shutil
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
from run_c5_benchmarks import CGRUN, make_swarm_configs


def run_trial(script, mode_name, sol, chal, base_cfg, n_agents, thr_per_agent, shared_mem, all_honest, out_dir):
    tag = "honest" if all_honest else "mixed"
    w = os.path.join(out_dir, f"cliff_{tag}_{mode_name}_N{n_agents}_{shared_mem}")
    shutil.rmtree(w, ignore_errors=True)
    os.makedirs(w, exist_ok=True)
    p_honest, p_drift, p_tight = make_swarm_configs(base_cfg, w)

    tasks = []
    for i in range(n_agents):
        if all_honest or i % 4 in (0, 2):
            tasks.append((i, "honest", p_honest, 0))
        elif i % 4 == 1:
            tasks.append((i, "stmt_drift", p_drift, 1))
        else:
            tasks.append((i, "illegal_axiom", p_tight, 1))

    inner_py = os.path.join(w, "inner.py")
    open(inner_py, "w").write("""
import concurrent.futures as cf, json, os, subprocess, sys, time
cfg = json.load(open(sys.argv[1]))
cg_rel = ""
for ln in open("/proc/self/cgroup"):
    if ln.startswith("0::"):
        cg_rel = ln.strip().split("::", 1)[1]
cg_dir = "/sys/fs/cgroup" + cg_rel

def run_one(item):
    idx, kind, cpath, want_rc = item
    aw = os.path.join(cfg["w"], f"agent_{idx}")
    os.makedirs(aw, exist_ok=True)
    jf = os.path.join(aw, "res.json")
    t0 = time.monotonic()
    extra_args = ["--private-inputs", "--mem-budget-mb", str(cfg["per_agent_mb"])] if cfg["is_lowmem"] else []
    p = subprocess.run([
        cfg["script"], cfg["sol"], cfg["chal"], cpath,
        "--threads", str(cfg["thr"]), "--workdir", aw, "--json", jf
    ] + extra_args, capture_output=True, text=True)
    dt = round(time.monotonic() - t0, 3)
    verdict = None
    if os.path.isfile(jf):
        try: verdict = json.load(open(jf)).get("verdict")
        except Exception: pass
    return {"idx": idx, "kind": kind, "want_rc": want_rc, "rc": p.returncode, "verdict": verdict, "wall_s": dt}

t0 = time.monotonic()
with cf.ThreadPoolExecutor(max_workers=len(cfg["tasks"])) as ex:
    res = list(ex.map(run_one, cfg["tasks"]))
wall = round(time.monotonic() - t0, 3)
peak_mb = None
oom_kills = 0
for fn in ("memory.peak", "memory.current"):
    fp = os.path.join(cg_dir, fn)
    if os.path.exists(fp):
        try:
            peak_mb = round(int(open(fp).read().strip()) / 1048576.0, 1)
            break
        except Exception:
            pass
evp = os.path.join(cg_dir, "memory.events")
if os.path.exists(evp):
    for ln in open(evp):
        if ln.startswith("oom_kill "):
            oom_kills = int(ln.split()[1])
json.dump({"wall_s": wall, "cgroup_peak_mb": peak_mb, "oom_kills": oom_kills, "agents": res}, open(cfg["out_json"], "w"))
""")
    mem_gb = int(shared_mem.rstrip("G"))
    spec_json = os.path.join(w, "spec.json")
    res_json = os.path.join(w, "res.json")
    json.dump({
        "w": w, "script": script, "is_lowmem": (mode_name == "check-sound-lowmem"),
        "per_agent_mb": max(1024, (mem_gb * 1024) // n_agents),
        "sol": sol, "chal": chal, "thr": thr_per_agent, "tasks": tasks, "out_json": res_json
    }, open(spec_json, "w"))

    t0 = time.monotonic()
    p = subprocess.run([CGRUN, "--mem", shared_mem, "--", sys.executable, "-I", inner_py, spec_json],
                       capture_output=True, text=True)
    outer_wall = round(time.monotonic() - t0, 2)
    if os.path.isfile(res_json):
        d = json.load(open(res_json))
        agents = d["agents"]
        exact = sum(1 for a in agents if a["rc"] == a["want_rc"])
        declined = sum(1 for a in agents if a["rc"] not in (0, 1))
        false_v = sum(1 for a in agents if (a["want_rc"] == 1 and a["rc"] == 0) or (a["want_rc"] == 0 and a["rc"] == 1))
        ok_lats = sorted(a["wall_s"] for a in agents if a["rc"] == a["want_rc"])
        p50 = round(statistics.median(ok_lats), 2) if ok_lats else None
        peak_mb = d.get("cgroup_peak_mb")
        oom_kills = d.get("oom_kills", 0)
        wall_s = d["wall_s"]
    else:
        exact, declined, false_v, p50, peak_mb, oom_kills, wall_s = 0, n_agents, 0, None, None, -1, outer_wall
    shutil.rmtree(w, ignore_errors=True)
    row = {
        "workload": tag, "mode": mode_name, "n_agents": n_agents, "thr_per_agent": thr_per_agent,
        "shared_mem": shared_mem, "exact": f"{exact}/{n_agents}", "exact_count": exact,
        "declined": declined, "oom_kills": oom_kills, "false_verdicts": false_v,
        "wall_s": wall_s, "p50_s": p50, "cgroup_peak_mb": peak_mb,
        "verdicts_per_min": round(exact * 60.0 / wall_s, 1) if wall_s > 0 and exact > 0 else 0.0,
    }
    print(f"[CLIFF-{tag.upper():6s}] N={n_agents:2d} mem={shared_mem:4s} | {mode_name:18s} | exact={exact:2d}/{n_agents:<2d} | oom={oom_kills:2d} | false={false_v} | peak={str(peak_mb):>7s} MB | wall={wall_s:6.2f}s | p50={str(p50):>5s}s", flush=True)
    return row


def main():
    fv, bench_in, out_dir = sys.argv[1], sys.argv[2], sys.argv[3]
    os.makedirs(out_dir, exist_ok=True)
    cs_std = os.path.join(fv, "check", "sound", "check-sound.sh")
    cs_lm = os.path.join(fv, "check", "lowmem", "check-sound-lowmem.sh")
    sol = f"{bench_in}/rh-mid/ref/solution.export"
    chal = f"{bench_in}/rh-mid/challenge/challenge.export"
    cfg = f"{bench_in}/rh-mid/challenge/comparator.json"

    rows = []
    # 1. Mixed workload, tight caps
    for n_ag, thr, mems in [(8, 2, ["8G", "10G", "12G"]), (16, 2, ["12G", "16G", "20G"])]:
        for mem in mems:
            for mname, sc in [("check-sound", cs_std), ("check-sound-lowmem", cs_lm)]:
                rows.append(run_trial(sc, mname, sol, chal, cfg, n_ag, thr, mem, False, out_dir))
    # 2. All-honest burst (all 8 agents run full kernel replay simultaneously!)
    for mem in ["16G", "20G", "24G", "32G"]:
        for mname, sc in [("check-sound", cs_std), ("check-sound-lowmem", cs_lm)]:
            rows.append(run_trial(sc, mname, sol, chal, cfg, 8, 4, mem, True, out_dir))

    json.dump(rows, open(os.path.join(out_dir, "swarm_cliff.json"), "w"), indent=2)
    print("CLIFF_BENCHMARKS_DONE", flush=True)


if __name__ == "__main__":
    main()
