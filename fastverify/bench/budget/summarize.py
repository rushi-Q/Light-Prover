#!/usr/bin/env python3
"""summarize.py [-I] DIR_OR_JSON... : one table row per cgrun JSON (name, limits, exit, wall, peak GB, sampled anon/file/shmem
GB, oom kills, cpu seconds, verdict parsed from the sibling .out/.log when present). --tsv for machine-readable output."""
import glob, json, os, re, sys

def gb(x):
    return "" if x in (None, "null") else f"{int(x) / 2**30:.2f}"

def verdict_of(jpath):
    base = jpath[:-5]
    for ext in (".out", ".log"):
        p = base + ext
        if os.path.exists(p):
            try:
                txt = open(p, errors="replace").read()
            except OSError:
                continue
            m = re.findall(r'"verdict":"([A-Z_]+)"', txt) or re.findall(r"verdict ([A-Z_]+) \(exit", txt)
            if m:
                return m[-1]
    return ""

def rows(paths):
    out = []
    for p in paths:
        try:
            j = json.load(open(p))
        except Exception as e:  # noqa: BLE001
            out.append((os.path.basename(p), f"unreadable: {e}"))
            continue
        lim = j.get("limits", {})
        sm = j.get("sampled_max", {}) or {}
        ev = j.get("memory_events", {}) or {}
        cpu = j.get("cpu_stat", {}) or {}
        out.append(dict(
            name=j.get("name", os.path.basename(p)), mem=lim.get("memory_max", ""), high=lim.get("memory_high", ""),
            cpus=lim.get("cpus", ""), quota=lim.get("cpu_quota_pct", ""), exit=j.get("exit"),
            wall=f"{float(j.get('wall_s', 0)):.1f}", peak=gb(j.get("memory_peak")), anon=gb(sm.get("anon")),
            file=gb(sm.get("file")), shmem=gb(sm.get("shmem")), oom=ev.get("oom_kill", ""), maxev=ev.get("max", ""),
            cpu_s=f"{int(cpu.get('usage_usec', 0)) / 1e6:.0f}", thr=cpu.get("nr_throttled", ""),
            verdict=verdict_of(p), host=j.get("host", "")))
    return out

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    tsv = "--tsv" in sys.argv
    paths = []
    for a in args:
        if os.path.isdir(a):
            paths += sorted(glob.glob(os.path.join(a, "*.json")))
        else:
            paths.append(a)
    cols = ["name", "mem", "cpus", "quota", "exit", "verdict", "wall", "peak", "anon", "file", "shmem", "oom", "maxev",
            "cpu_s", "thr", "host"]
    rs = rows(paths)
    if tsv:
        print("\t".join(cols))
        for r in rs:
            print("\t".join("" if isinstance(r, tuple) else str(r.get(c, "")) for c in cols))
        return
    w = {c: max(len(c), *(len(str(r.get(c, ""))) for r in rs if isinstance(r, dict))) for c in cols}
    print(" ".join(c.ljust(w[c]) for c in cols))
    for r in rs:
        if isinstance(r, tuple):
            print(r[0], r[1]); continue
        print(" ".join(str(r.get(c, "")).ljust(w[c]) for c in cols))

if __name__ == "__main__":
    main()
