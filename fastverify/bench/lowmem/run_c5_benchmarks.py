#!/usr/bin/env python3
"""
fastverify/bench/lowmem/run_c5_benchmarks.py — memory floors of the standard and low-memory sound checks, and concurrent checks.

Measures under real Linux cgroup-v2 `memory.max` (a cgroup scope launcher, swap=0):
  1. Single-check memory floor sweep (`check-sound.sh` vs `check-sound-lowmem.sh`) on:
     - `rh-miniF` (46 MB),
     - `rh-mid` (1.10 GB),
     - `Mathlib` (6.07 GB).
  2. Concurrent checks (8 & 16 concurrent verification jobs inside ONE shared
     `16G` / `24G` / `32G` / `48G` cgroup, mixed workload: 50% valid proof, 25% sorryAx, 25% statement drift):
     survival rate, p50/p95 latency, throughput (verdicts/min), and zero false accepts/rejects.
"""
import concurrent.futures as cf
import json
import os
import shutil
import statistics
import subprocess
import sys
import time

CGRUN = os.path.expanduser("cgrun")   # the cgroup scope launcher (a command on PATH; edit for another location)


def parse_last_json(text):
    for line in reversed(text.splitlines()):
        line = line.strip()
        if line.startswith("{") and line.endswith("}"):
            try:
                return json.loads(line)
            except Exception:
                pass
    return None


def run_single_floor(cs_std, cs_lm, cases, out_dir):
    rows = []
    wroot = os.path.join(out_dir, "work_single")
    os.makedirs(wroot, exist_ok=True)
    for cname, sol, chal, cfg, thr, mems in cases:
        for mem in mems:
            for mode, script in [("check-sound", cs_std), ("check-sound-lowmem", cs_lm)]:
                w = os.path.join(wroot, f"{cname}_{mode}_{mem}")
                shutil.rmtree(w, ignore_errors=True)
                os.makedirs(w, exist_ok=True)
                jf = os.path.join(w, "res.json")
                cmd = [
                    CGRUN, "--mem", mem, "--",
                    script, sol, chal, cfg,
                    "--threads", str(thr),
                    "--workdir", w,
                    "--json", jf,
                ] + (["--private-inputs"] if mode == "check-sound-lowmem" else [])
                t0 = time.monotonic()
                p = subprocess.run(cmd, capture_output=True, text=True)
                dt = round(time.monotonic() - t0, 2)
                j = None
                if os.path.isfile(jf):
                    try:
                        j = json.load(open(jf))
                    except Exception:
                        pass
                if j is None:
                    j = parse_last_json(p.stdout)
                verdict = j.get("verdict") if j else ("OOM_DECLINED" if p.returncode in (2, 137, 143) else f"RC_{p.returncode}")
                eff_t = j.get("effective_threads", thr) if j else thr
                shutil.rmtree(w, ignore_errors=True)
                row = {
                    "case": cname,
                    "mode": mode,
                    "mem_limit": mem,
                    "req_threads": thr,
                    "eff_threads": eff_t,
                    "rc": p.returncode,
                    "verdict": verdict,
                    "wall_s": dt,
                }
                rows.append(row)
                print(f"[SINGLE] {cname:14s} | {mode:18s} | mem={mem:5s} | rc={p.returncode:3d} | {verdict:12s} | {dt:6.2f}s", flush=True)
    return rows


def make_swarm_configs(base_cfg_path, work_dir):
    """Create 3 submission configs against the same export:
      - kind 'honest': unmodified comparator.json -> expected ACCEPTED (0)
      - kind 'stmt_drift': adds a missing/renamed target theorem -> expected REJECTED (1)
      - kind 'axiom_tight': removes Classical.choice from permitted_axioms -> expected REJECTED (1)
    """
    base = json.load(open(base_cfg_path))
    p_honest = os.path.join(work_dir, "cfg_honest.json")
    json.dump(base, open(p_honest, "w"))

    drift = dict(base)
    drift["theorem_names"] = list(base["theorem_names"]) + ["AgentSwarm.drifted_lemma_stmt"]
    p_drift = os.path.join(work_dir, "cfg_drift.json")
    json.dump(drift, open(p_drift, "w"))

    tight = dict(base)
    tight["permitted_axioms"] = [a for a in base["permitted_axioms"] if a != "Classical.choice"]
    p_tight = os.path.join(work_dir, "cfg_tight.json")
    json.dump(tight, open(p_tight, "w"))
    return p_honest, p_drift, p_tight


def run_swarm_trial(script, mode_name, sol, chal, base_cfg, n_agents, thr_per_agent, shared_mem, out_dir):
    """Run `n_agents` concurrent verification jobs INSIDE ONE shared `cgrun --mem <shared_mem>` scope."""
    w = os.path.join(out_dir, f"swarm_{mode_name}_N{n_agents}_{shared_mem}")
    shutil.rmtree(w, ignore_errors=True)
    os.makedirs(w, exist_ok=True)
    p_honest, p_drift, p_tight = make_swarm_configs(base_cfg, w)

    # Workload mix: 50% honest proof, 25% statement drift, 25% illegal axiom
    tasks = []
    for i in range(n_agents):
        if i % 4 in (0, 2):
            tasks.append((i, "honest", p_honest, 0))
        elif i % 4 == 1:
            tasks.append((i, "stmt_drift", p_drift, 1))
        else:
            tasks.append((i, "illegal_axiom", p_tight, 1))

    inner_py = os.path.join(w, "inner_swarm.py")
    open(inner_py, "w").write("""
import concurrent.futures as cf, json, os, subprocess, sys, time
cfg = json.load(open(sys.argv[1]))
# Sample our own cgroup's memory.peak / memory.current
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
    extra_args = ["--private-inputs"] if cfg["is_lowmem"] else []
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
for fn in ("memory.peak", "memory.current"):
    fp = os.path.join(cg_dir, fn)
    if os.path.exists(fp):
        try:
            peak_mb = round(int(open(fp).read().strip()) / 1048576.0, 1)
            break
        except Exception:
            pass
json.dump({"wall_s": wall, "cgroup_peak_mb": peak_mb, "agents": res}, open(cfg["out_json"], "w"))
""")
    spec_json = os.path.join(w, "spec.json")
    res_json = os.path.join(w, "swarm_res.json")
    json.dump({
        "w": w, "script": script, "is_lowmem": (mode_name == "check-sound-lowmem"),
        "sol": sol, "chal": chal,
        "thr": thr_per_agent, "tasks": tasks, "out_json": res_json
    }, open(spec_json, "w"))

    t0 = time.monotonic()
    p = subprocess.run([CGRUN, "--mem", shared_mem, "--", sys.executable, "-I", inner_py, spec_json],
                       capture_output=True, text=True)
    outer_wall = round(time.monotonic() - t0, 2)

    if os.path.isfile(res_json):
        data = json.load(open(res_json))
        agents = data["agents"]
        exact = sum(1 for a in agents if a["rc"] == a["want_rc"])
        false_verdicts = sum(
            1 for a in agents
            if (a["want_rc"] == 1 and a["rc"] == 0) or (a["want_rc"] == 0 and a["rc"] == 1)
        )
        lats = sorted(a["wall_s"] for a in agents)
        p50 = round(statistics.median(lats), 2) if lats else None
        p95 = round(lats[min(len(lats) - 1, int(len(lats) * 0.95))], 2) if lats else None
        peak_mb = data.get("cgroup_peak_mb")
        wall_s = data["wall_s"]
    else:
        # Entire systemd scope killed by OOMPolicy=stop on first OOM!
        exact = 0
        false_verdicts = 0
        p50 = None
        p95 = None
        peak_mb = None
        wall_s = outer_wall

    shutil.rmtree(w, ignore_errors=True)
    summary = {
        "mode": mode_name,
        "n_agents": n_agents,
        "thr_per_agent": thr_per_agent,
        "shared_mem": shared_mem,
        "scope_rc": p.returncode,
        "completed_exact": f"{exact}/{n_agents}",
        "exact_count": exact,
        "false_verdicts": false_verdicts,
        "wall_s": wall_s,
        "p50_s": p50,
        "p95_s": p95,
        "cgroup_peak_mb": peak_mb,
        "verdicts_per_min": round(exact * 60.0 / wall_s, 1) if wall_s > 0 and exact > 0 else 0.0,
    }
    print(f"[SWARM] N={n_agents:2d} mem={shared_mem:4s} | {mode_name:18s} | exact={exact:2d}/{n_agents:<2d} | false={false_verdicts} | peak={str(peak_mb):>7s} MB | wall={wall_s:6.2f}s | p50={str(p50):>5s}s | tput={summary['verdicts_per_min']:5.1f}/min", flush=True)
    return summary


def main():
    fv = sys.argv[1]
    bench_in = sys.argv[2]
    out_dir = sys.argv[3]
    os.makedirs(out_dir, exist_ok=True)

    cs_std = os.path.join(fv, "check", "sound", "check-sound.sh")
    cs_lm = os.path.join(fv, "check", "lowmem", "check-sound-lowmem.sh")

    # Mathlib comparator config (Nat.add_comm against rh-miniF challenge export)
    ml_cfg = os.path.join(out_dir, "mathlib_cmp.json")
    json.dump({
        "challenge_module": "Challenge",
        "solution_module": "Mathlib",
        "theorem_names": ["Nat.add_comm"],
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]
    }, open(ml_cfg, "w"))

    single_cases = [
        ("rh-miniF-46MB",
         f"{bench_in}/rh-miniF/ref/solution.export",
         f"{bench_in}/rh-miniF/challenge/challenge.export",
         f"{bench_in}/rh-miniF/challenge/comparator.json",
         8, ["512M", "768M", "1G", "1536M", "2G"]),
        ("rh-mid-1.1GB",
         f"{bench_in}/rh-mid/ref/solution.export",
         f"{bench_in}/rh-mid/challenge/challenge.export",
         f"{bench_in}/rh-mid/challenge/comparator.json",
         16, ["2G", "3G", "4G", "5G", "6G", "8G"]),
        ("Mathlib-6.1GB",
         f"{bench_in}/mathlib/export/mathlib.export",
         f"{bench_in}/rh-miniF/challenge/challenge.export",
         ml_cfg,
         16, ["8G", "10G", "12G", "16G", "20G", "24G", "32G"]),
    ]
    single_rows = run_single_floor(cs_std, cs_lm, single_cases, out_dir)
    json.dump(single_rows, open(os.path.join(out_dir, "single_floors.json"), "w"), indent=2)

    swarm_rows = []
    # 8 & 16 concurrent agents on rh-mid (1.10 GB) under shared node memory budgets!
    rhmid_sol = f"{bench_in}/rh-mid/ref/solution.export"
    rhmid_chal = f"{bench_in}/rh-mid/challenge/challenge.export"
    rhmid_cfg = f"{bench_in}/rh-mid/challenge/comparator.json"
    for n_ag, thr, mems in [(8, 4, ["16G", "24G", "32G", "48G"]), (16, 4, ["24G", "32G", "48G", "64G"])]:
        for mem in mems:
            for mode_name, script in [("check-sound", cs_std), ("check-sound-lowmem", cs_lm)]:
                swarm_rows.append(run_swarm_trial(script, mode_name, rhmid_sol, rhmid_chal, rhmid_cfg, n_ag, thr, mem, out_dir))
    json.dump(swarm_rows, open(os.path.join(out_dir, "swarm_results.json"), "w"), indent=2)
    print("ALL_C5_BENCHMARKS_DONE", flush=True)


if __name__ == "__main__":
    main()
