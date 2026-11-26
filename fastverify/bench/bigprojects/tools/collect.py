#!/usr/bin/python3 -I
"""collect.py RUNDIR... -> one TSV row per fastverify run: stage seconds, build option/attempts, modules, sum of module
walls / CPU and the critical path from the scheduler log (B1-B3), export size, check legs, verdict."""
import json, os, sys, glob

def sched_stats(logdir):
    for sub in ("build-fast", "build-fast-b1"):
        p = os.path.join(logdir, sub, "sched.out")
        if not os.path.exists(p):
            continue
        mods, walls, cpus, fin, deps = 0, 0.0, 0.0, {}, {}
        tc = None
        zy = {}
        for line in open(p):
            try:
                e = json.loads(line)
            except Exception:
                continue
            ev = e.get("event")
            if ev == "start":
                tc = e.get("lean")
            if ev == "module" and e.get("rc") == 0:
                mods += 1; walls += e.get("wall", 0); cpus += e.get("cpu", 0) or 0
                fin[e["module"]] = e.get("start", 0) + e.get("wall", 0)
            if ev == "zygote-children":
                zy = {"zy_children": e.get("n"), "zy_misses": e.get("misses")}
            if ev == "zygote-ready":
                zy["zy_up"] = e.get("up")
            if ev == "summary":
                zy["sched_wall"] = e.get("wall")
        return dict(sub=sub, modules=mods, sum_walls=round(walls, 1), sum_cpu=round(cpus, 1),
                    last_end=round(max(fin.values()), 1) if fin else None, lean=(tc or "").split("/")[-3] if tc else None, **zy)
    return {}

cols = ["run", "preset", "verdict", "reason", "threads", "preflight", "prepare", "challenge", "build", "build_opts",
        "modules", "sched_wall", "sum_walls", "sum_cpu", "lean", "zy_up", "zy_children", "export", "export_opt",
        "export_MB", "check", "check_legs", "total"]
print("\t".join(cols))
for d in sys.argv[1:]:
    try:
        r = json.load(open(os.path.join(d, "result.json")))
    except Exception as ex:
        print(os.path.basename(d.rstrip("/")) + "\tNO-RESULT\t" + str(ex)); continue
    st = r.get("stage_seconds", {})
    b = r.get("build") or {}; e = r.get("export") or {}
    ch = r.get("checks") or {}
    chk = []
    for k, v in ch.items():
        lm = (v.get("stage") or {}).get("leg_ms") or {}
        chk.append("%s:%s:%s" % (k, v.get("verdict"), v.get("seconds")) + ("[" + ",".join("%s=%.0f" % (a.split()[0], b_ / 1000) for a, b_ in lm.items()) + "]" if lm else ""))
    s = sched_stats(os.path.join(d, "log"))
    ce = (r.get("inputs") or {}).get("challenge_export") or {}
    tot = sum(v for k, v in st.items() if k in ("preflight", "prepare", "build", "export", "sha256_export", "checks_total"))
    row = dict(run=os.path.basename(d.rstrip("/")), preset=(r.get("mode") or {}).get("preset"), verdict=r.get("verdict"),
               reason=(r.get("verdict_basis") or "")[:80].replace("\t", " "), threads=r.get("threads"),
               preflight=st.get("preflight"), prepare=st.get("prepare"), challenge=ce.get("seconds"), build=st.get("build"),
               build_opts="+".join("%s:%s:%s" % (a.get("option"), a.get("exit"), a.get("seconds")) for a in b.get("attempts", [])),
               export=st.get("export"), export_opt=e.get("option"), export_MB=round((e.get("size") or 0) / 1e6, 1),
               check=st.get("checks_total"), check_legs=" ".join(chk), total=round(tot, 1), **s)
    print("\t".join(str(row.get(c, "")) for c in cols))
