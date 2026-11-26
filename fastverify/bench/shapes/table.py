#!/usr/bin/python3 -I
"""table.py RESULTS.jsonl [...] [--md]  -> one row per case: shape facts + per-preset stage times + speed-ups.

Columns per preset P: total = wall of the whole bin/fastverify run; B/E/C = build / export / checks stage seconds;
F = fixed part (preflight + prepare). Speed-up columns: official total / preset total, and official build / preset build.
The last record of each (case, preset, tag) wins (re-runs replace earlier ones)."""
import json, sys
from collections import OrderedDict


def load(paths):
    recs = OrderedDict()
    for p in paths:
        for line in open(p):
            try:
                r = json.loads(line)
            except Exception:  # noqa: BLE001
                continue
            key = (r["case"], r["preset"] + (("-" + r["tag"]) if r.get("tag") else ""))
            recs[key] = r
    return recs


def print_detail(recs, md):
    """per run: fixed part of the build stage (stage - scheduler wall), scheduler wall, processes, per-process wall/CPU"""
    hdr = ["case", "preset", "verdict", "total", "pre+prep", "build", "build fixed", "sched wall", "lean procs",
           "wall/proc", "cpu/proc", "sum cpu", "export", "check", "toolchain"]
    rows = []
    for (c, p), r in recs.items():
        s = r.get("stage_seconds") or {}
        sc = r.get("sched") or {}
        st = sc.get("sched_start") or {}
        n = sc.get("module_events") or 0
        b = s.get("build", 0)
        sw = sc.get("sched_wall")
        lean = str(st.get("lean") or ("official lake" if p.startswith("reference") else ""))
        tc = "T1-nopgo" if "nopgo" in lean else "zygote-T1" if "s01zy" in lean else "T1-pgo" if "pgo" in lean else \
            "official" if lean else ""
        if st.get("zygote") and "s01zy" in lean:
            tc += "+zygote"
        rows.append([c, p, str(r.get("verdict")), f"{r['wall']:.1f}", f"{s.get('preflight', 0) + s.get('prepare', 0):.1f}",
                     f"{b:.1f}", f"{b - sw:.1f}" if sw is not None else "", f"{sw:.1f}" if sw is not None else "",
                     str(n) if n else "", f"{sc['sum_wall'] / n:.2f}" if n else "", f"{sc['sum_cpu'] / n:.2f}" if n else "",
                     f"{sc['sum_cpu']:.0f}" if n else "", f"{s.get('export', 0):.1f}", f"{s.get('checks_total', 0):.1f}", tc])
    if md:
        print("| " + " | ".join(hdr) + " |"); print("|" + "---|" * len(hdr))
        for r in rows:
            print("| " + " | ".join(r) + " |")
    else:
        w = [max(len(h), *(len(r[i]) for r in rows)) for i, h in enumerate(hdr)]
        print("  ".join(h.ljust(w[i]) for i, h in enumerate(hdr)))
        for r in rows:
            print("  ".join(x.ljust(w[i]) for i, x in enumerate(r)))


def main():
    a = sys.argv[1:]
    md = "--md" in a
    detail = "--detail" in a
    only = None
    if "--presets" in a:
        i = a.index("--presets"); only = a[i + 1].split(","); del a[i:i + 2]
    a = [x for x in a if x not in ("--md", "--detail")]
    recs = load(a)
    if detail:
        print_detail(recs, md)
        return
    cases = OrderedDict()
    for (c, p), r in recs.items():
        cases.setdefault(c, {})[p] = r
    presets = []
    for c in cases.values():
        for p in c:
            if p not in presets:
                presets.append(p)
    order = [p for p in ("reference", "fast-exact", "sound") if p in presets] + \
            [p for p in presets if p not in ("reference", "fast-exact", "sound")]
    if only:
        order = [p for p in only if p in presets]

    def skey(c):   # base, shape, size, content
        parts = c.split("-")
        if len(parts) == 4:
            n = parts[2].split("x"); size = 1
            for x in n:
                size *= int(x) if x.isdigit() else 1
            return (parts[0], {"wide": 0, "layered": 1, "deep": 2}.get(parts[1], 3), parts[3] != "tiny", parts[3], size)
        return ("~", 9, True, c, 0)
    cases = OrderedDict(sorted(cases.items(), key=lambda kv: skey(kv[0])))
    hdr = ["case", "mods", "depth", "export MB"]
    for p in order:
        hdr += [f"{p} total", f"{p} B/E/C"]
    hdr += ["sound vs official (total)", "sound vs official (build)"]
    rows = []
    for c, ps in cases.items():
        any_r = next(iter(ps.values()))
        ci = any_r.get("case_info") or {}
        size = None
        for r in ps.values():
            s = (r.get("export") or {}).get("size")
            if s:
                size = s
        row = [c, str(ci.get("modules", "")), str(ci.get("depth", "")), f"{size / 1e6:.1f}" if size else ""]
        for p in order:
            r = ps.get(p)
            if not r:
                row += ["", ""]; continue
            s = r.get("stage_seconds") or {}
            v = r.get("verdict") or "?"
            mark = "" if v == "ACCEPTED" else f" {v}"
            row += [f"{r['wall']:.1f}{mark}",
                    f"{s.get('build', 0):.1f}/{s.get('export', 0):.1f}/{s.get('checks_total', 0):.1f}"]
        o, so = ps.get("reference"), ps.get("sound")
        if o and so and so.get("wall"):
            ob, sb = (o.get("stage_seconds") or {}).get("build"), (so.get("stage_seconds") or {}).get("build")
            row += [f"{o['wall'] / so['wall']:.2f}x", f"{ob / sb:.2f}x" if ob and sb else ""]
        else:
            row += ["", ""]
        rows.append(row)
    if md:
        print("| " + " | ".join(hdr) + " |")
        print("|" + "---|" * len(hdr))
        for r in rows:
            print("| " + " | ".join(r) + " |")
    else:
        w = [max(len(h), *(len(r[i]) for r in rows)) for i, h in enumerate(hdr)] if rows else [len(h) for h in hdr]
        print("  ".join(h.ljust(w[i]) for i, h in enumerate(hdr)))
        for r in rows:
            print("  ".join(x.ljust(w[i]) for i, x in enumerate(r)))


if __name__ == "__main__":
    main()
