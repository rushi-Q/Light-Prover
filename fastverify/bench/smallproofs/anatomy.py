#!/usr/bin/python3 -I
"""anatomy.py CORPUS OUT.tsv RUNSDIR... : per case one row: official stage times (reference run) and, for the fast
presets, the intrinsic work (lean module wall/cpu from sched.out, native exporter seconds, kernel leg ms) vs the stage
times (the difference = per-run fixed cost of the package stage)."""
import glob, json, os, re, sys
corpus, out = sys.argv[1], sys.argv[2]
cases = json.load(open(os.path.join(corpus, "cases.json")))

def J(p):
    try:
        return json.load(open(p))
    except Exception:
        return None

def sched(d):
    w = c = 0.0; n = 0; zy = None
    try:
        for ln in open(os.path.join(d, "log", "build-fast", "sched.out")):
            if ln.startswith("{"):
                e = json.loads(ln)
                if e.get("event") == "module":
                    w += e.get("wall", 0); c += e.get("cpu", 0); n += 1
                if e.get("event") == "zygote-ready":
                    zy = e.get("up")
    except Exception:
        return None, None, None, None
    return round(w, 2), round(c, 2), n, zy

rows = []
for runs in sys.argv[3:]:
    for d in sorted(glob.glob(os.path.join(runs, "*"))):
        if not os.path.isdir(d):
            continue
        tag = os.path.basename(d)
        parts = tag.split(".")
        case, preset = parts[0], parts[1]
        rtag = ".".join(parts[2:])
        r = J(os.path.join(d, "result.json"))
        if not r:
            continue
        ss = r.get("stage_seconds") or {}
        row = {"case": case, "preset": preset, "tag": rtag, "style": cases.get(case, {}).get("style"),
               "imports": cases.get(case, {}).get("imports"), "n_thm": cases.get(case, {}).get("n_theorems"),
               "verdict": r.get("verdict"), "trust": r.get("trust"),
               "wall_minus_prepare": None, "preflight": ss.get("preflight"), "build": ss.get("build"),
               "export": ss.get("export"),
               "check": round(sum(v for k, v in ss.items() if k.startswith("check_") and isinstance(v, (int, float))), 3),
               "export_MB": round(((r.get("export") or {}).get("size") or 0) / 1e6, 2),
               "build_opt": (r.get("build") or {}).get("option")}
        try:
            t0 = r["started"]; t1 = r["finished"]
        except KeyError:
            t0 = t1 = None
        mw, mc, nm, zy = sched(d)
        row.update({"lean_wall": mw, "lean_cpu": mc, "n_mod": nm, "zygote_up": zy})
        e = J(os.path.join(d, "log", "export.json")) or {}
        row["e1_native_s"] = round(((e.get("native") or {}).get("seconds") or 0), 3) or None
        s = J(os.path.join(d, "log", "sound.json")) or {}
        lm = s.get("leg_ms") or {}
        row["cs_wall"] = s.get("wall_s")
        row["leg_lean_ms"] = lm.get("kernel Lean default"); row["leg_gruszka_ms"] = lm.get("kernel gruszka (second kernel)")
        row["leg_compare_ms"] = lm.get("compare (parse, compareAt, checkAxioms)")
        a = J(os.path.join(d, "log", "checkA.json")) or {}
        row["c1_wall"] = a.get("wall_s")
        o = J(os.path.join(d, "log", "official.json")) or {}
        row["c0_s"] = o.get("seconds")
        rows.append(row)
keys = list(rows[0].keys())
with open(out, "w") as f:
    f.write("\t".join(keys) + "\n")
    for x in rows:
        f.write("\t".join("" if x.get(k) is None else str(x.get(k)) for k in keys) + "\n")
print(len(rows), "rows ->", out)
