#!/usr/bin/python3 -I
"""mkreport.py RESULTS_DIR : markdown tables from the cgrun JSONs under RESULTS_DIR
(sweep1 = export-in check vs threads / memory caps, legs1 = legs alone, limits1 = memory floors, src* = from-sources runs,
swarm1 = concurrent checks, rh/ml named runs). Verdicts come from the sibling .out/.log files when present, else from the
result.json copied next to the cgrun JSON (TAG.result.json)."""
import glob, json, os, re, sys

GiB = 2 ** 30
SIZES = {"miniF": ("rh-miniF", 48065997), "mid": ("rh-mid", 1104038853), "ml": ("Mathlib", 6067502667),
         "rh": ("RH", 61570595788), "mlclos": ("Mathlib-as-project closure (10 targets)", 524020761),
         "n2mid": ("rh-mid (Intel host, cross-machine)", 1104038853),
         "n2ml": ("Mathlib (Intel host, cross-machine)", 6067502667),
         "chal437": ("4.37 RH challenge export (bb37c4bb: Mathlib closure of the 5 RH statements)", 363237517)}
CHECKS437 = {"chal437": "4.36 CS via the cross-version gate", "chal437b": "4.36 CS via the cross-version gate",
             "chal437cs437": "CS-437, staged build (ccmp e046aa89, pleanchecker f527ac01; the later opt-in judge pins pleanchecker d1c17ba9)",
             "m437x-cs436": "4.36 CS (check-sound.sh default pins)",
             "m437x-cs437": "CS-437 v1 (check-sound.sh --pins pins-437.env 001f3d2b: ccmp e046aa89, pleanchecker d1c17ba9; the plain replay)",
             "m437x-cs437f": "CS-437 v2 (check-sound.sh v2.2, revision 2, --pins pins-437.env 896866c2 + --hide lean-4.37.0-rc1-no-expose.txt: pleanchecker c105dd1f, encapsulated replay)"}
MAIN437X = ("cache-based 4.37 community-main export (main 9c9f665e sources, build artifacts from the community's "
            "published Lake cache, E1-437; 61,172,326,067 B, sha 40b0fe82)")

def load(p):
    try:
        return json.load(open(p))
    except Exception:
        return None

def verdict_near(p):
    base = p[:-5]
    for ext in (".out", ".log"):
        if os.path.exists(base + ext):
            txt = open(base + ext, errors="replace").read()
            m = re.findall(r'"verdict":"([A-Z_]+)"', txt) or re.findall(r"verdict ([A-Z_]+) \(exit", txt)
            if m:
                return m[-1]
    rj = base.replace(".cg", "") + ".result.json"
    if os.path.exists(rj):
        r = load(rj)
        if r:
            return r.get("verdict", "")
    return ""

def gb(x):
    return "" if x in (None, "null") else f"{int(x) / GiB:.1f}"

def main():
    R = sys.argv[1]
    rows = []
    for p in sorted(glob.glob(os.path.join(R, "**", "*.json"), recursive=True)):
        j = load(p)
        if not isinstance(j, dict) or "memory_peak" not in j:
            continue
        rows.append((p, j))
    # A: export-in check vs threads (unlimited)
    print("### A. Export-in trusted check (`check-sound.sh`, three legs concurrent): wall and cgroup peak vs threads\n")
    print("| export | size | threads | wall s | peak GB | anon GB | CPU s | verdict |\n|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^sw-(miniF|mid|ml|rh|n2mid|n2ml)\.T(\d+)$", j.get("name", ""))
        if not m or j["limits"].get("memory_max") not in ("max", None):
            continue
        lab, t = m.group(1), int(m.group(2))
        sm = j.get("sampled_max") or {}
        print(f"| {SIZES[lab][0]} | {SIZES[lab][1] / GiB:.2f} GB | {t} | {float(j['wall_s']):.1f} | {gb(j['memory_peak'])} | "
              f"{gb(sm.get('anon'))} | {int(j['cpu_stat'].get('usage_usec', 0)) / 1e6:.0f} | {verdict_near(p)} |")
    print("\n### B. Each leg alone (pinned binaries; ccmp with stub kernels = parse + compareAt + checkAxioms)\n")
    print("| export | leg | threads | wall s | peak GB |\n|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^lg-(miniF|mid|ml|rh)\.(plc|grz|ccmp)\.T(\d+)$", j.get("name", ""))
        if not m:
            continue
        leg = {"plc": "pleanchecker (official kernel)", "grz": "gruszka", "ccmp": "ccmp"}[m.group(2)]
        print(f"| {SIZES[m.group(1)][0]} | {leg} | {m.group(3)} | {float(j['wall_s']):.1f} | {gb(j['memory_peak'])} |")
    print("\n### C. Memory caps (`memory.max`, swap 0): outcome of the export-in check\n")
    print("| export | threads | memory.max | outcome | wall s | peak GB | OOM kills |\n|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^sw-(miniF|mid|ml|rh|n2mid|n2ml)(?:lim)?\.T(\d+)\.M(\S+)$", j.get("name", ""))
        if not m:
            continue
        ev = j.get("memory_events") or {}
        v = verdict_near(p) or ("killed (scope stopped)" if j.get("scope_terminated") else f"exit {j['exit']}")
        print(f"| {SIZES[m.group(1)][0]} | {m.group(2)} | {m.group(3)} | {v} | {float(j['wall_s']):.1f} | {gb(j['memory_peak'])} | {ev.get('oom_kill', '')} |")
    print("\n### D. From sources (`bin/fastverify --preset sound`; `.nozy` = the preset's item list without zygote / zygote-prefix / native-pkg / j1-saturated; mlwhole = Mathlib built as the project with the item list of bench/mathlib-as-project)\n")
    print("| run (project.cpus.cap) | cpus | memory.max | threads | verdict | total s | build s | build attempts (option, exit, s) | peak GB | anon GB | OOM kills | largest process |\n|---|---|---|---|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^fv-(.+)$", j.get("name", ""))
        if not m:
            continue
        rj = p.replace(".cg.json", ".result.json")
        r = load(rj) or {}
        ss = r.get("stage_seconds", {}) or {}
        b = r.get("build") or {}
        ev = j.get("memory_events") or {}
        sm = j.get("sampled_max") or {}
        att = "; ".join(f"{a.get('option')} {a.get('exit')} {round(a.get('seconds', 0))}" for a in (b.get("attempts") or []))
        top = ""
        bc = j.get("max_rss_by_comm") or {}
        if bc:
            c, v = max(bc.items(), key=lambda kv: kv[1]["max_rss"])
            top = f"{c} {v['max_rss'] / GiB:.1f} GB x{v['max_concurrent']}"
        print(f"| {m.group(1)} | {j['limits'].get('cpus', '')} | {j['limits'].get('memory_max', '')} | {r.get('threads', '')} | "
              f"{r.get('verdict', verdict_near(p))} | {float(j['wall_s']):.0f} | {ss.get('build', '')} | {att} | "
              f"{gb(j['memory_peak'])} | {gb(sm.get('anon'))} | {ev.get('oom_kill', '')} | {top} |")
    print("\n### E. Concurrent checks (N clients on one machine): one scope, N `check-sound.sh` at once\n")
    print("| case | cpus | memory.max | N x threads | all verdicts | per-check wall s | group peak GB | CPU s |\n|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^sw-(miniF|mid|ml|rh)\.N(\d+)\.T(\d+)\.(\S+)$", j.get("name", ""))
        if not m:
            continue
        tsv = p.replace(".cg.json", ".runs.tsv")
        walls, verdicts = [], []
        if os.path.exists(tsv):
            for ln in open(tsv):
                f = ln.rstrip("\n").split("\t")
                if len(f) >= 4:
                    verdicts.append(f[2]); walls.append(float(f[3]))
        vs = ",".join(sorted(set(verdicts))) if verdicts else ""
        ws = f"{min(walls):.0f}-{max(walls):.0f}" if walls else ""
        print(f"| {SIZES[m.group(1)][0]} | {j['limits'].get('cpus', '')} | {j['limits'].get('memory_max', '')} | {m.group(2)} x {m.group(3)} | {vs} | {ws} | {gb(j['memory_peak'])} | {int(j['cpu_stat'].get('usage_usec', 0)) / 1e6:.0f} |")
    section_f(rows)
    section_g(rows)
    section_g3(rows)
    section_g4b(rows)
    section_g5()

def section_g(rows):
    print("\n### G. Lean 4.37.0-rc1 path on ordinary hardware (cgrun scopes)\n")
    print("G1. One-module `import Mathlib` attempt on 4.37.0-rc1 + Mathlib 31ce06ea (every preset goes through the "
          "cross-version gate on 4.37: B0 official build + bundled 4.37 leanexport, then the preset's checks - `sound` = the 4.36 "
          "trusted check CS, `default` = official comparator + checkA + checkB), 4 CPUs; `cold` = Mathlib oleans, toolchain and "
          "project evicted from the page cache before the run (bench/budget/evict.py), so the scope's peak includes the olean reads.\n")
    print("| run | preset | memory.max | cache | verdict | total s | challenge s | build s | export s | check s | peak GB | anon GB | OOM kills |\n|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^fv-attempt437\.c(\d+)\.m(\d+)(\.cold)?(\.sound)?$", j.get("name", ""))
        if not m:
            continue
        r = load(p.replace(".cg.json", ".result.json")) or {}
        ss = r.get("stage_seconds", {}) or {}
        ev = j.get("memory_events") or {}
        sm = j.get("sampled_max") or {}
        if "check_sound" in ss:
            preset, chk = "sound (CS)", ss.get("check_sound", "")
        else:
            preset, chk = "default (C1+C3+C0)", ss.get("checks_total", "")
        print(f"| attempt437 {m.group(1)} CPUs | {preset} | {m.group(2)} GB | {'cold' if m.group(3) else 'warm'} | {r.get('verdict', verdict_near(p))} | "
              f"{float(j['wall_s']):.0f} | {ss.get('prepare', '')} | {ss.get('build', '')} | {ss.get('export', '')} | {chk} | "
              f"{gb(j['memory_peak'])} | {gb(sm.get('anon'))} | {ev.get('oom_kill', '')} |")
    print("\nG2. Export-in trusted check of the 4.37 challenge export (0.34 GB; the sorried challenge is also the 'solution', so the "
          "expected verdict is REJECTED by sorryAx after the full replay - a memory/time row, not a judgement): the 4.36 check vs "
          "the 4.37 check (staged build, then the opt-in build), threads and caps.\n")
    print("| check | threads | memory.max | outcome | wall s | peak GB | anon GB | CPU s | OOM kills |\n|---|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^sw-(chal437\w*)\.T(\d+)(?:\.M(\S+))?$", j.get("name", ""))
        if not m or m.group(1) not in CHECKS437:
            continue
        ev = j.get("memory_events") or {}
        sm = j.get("sampled_max") or {}
        v = verdict_near(p) or ("killed (scope stopped)" if j.get("scope_terminated") else f"exit {j['exit']}")
        print(f"| {CHECKS437[m.group(1)]} | {m.group(2)} | {m.group(3) or 'max'} | {v} | {float(j['wall_s']):.1f} | {gb(j['memory_peak'])} | "
              f"{gb(sm.get('anon'))} | {int((j.get('cpu_stat') or {}).get('usage_usec', 0)) / 1e6:.0f} | {ev.get('oom_kill', '')} |")

def section_g3(rows):
    print("\nG3. A 64-core / 256 GB workstation: cold build of community main 9c9f665e (146,883-module Main closure) from "
          "sources with the package as it behaves on 4.37 (--preset sound -> cross-version gate -> B0 official "
          "lake build + bundled 4.37 leanexport + the 4.36 trusted check), one cgrun scope: cpuset = 64 physical cores "
          "(CPUs 8-71, no SMT siblings), memory.max 256 GB, swap 0, export on /scratch; official-build.sh limited to "
          "64 lake jobs (an earlier version of the script ran 220).\n")
    print("| run | verdict | total s | prepare s | build s | export s | check s | peak GB | anon GB | OOM kills | largest process |\n|---|---|---|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^fv-main437\.c(\d+)\.m(\d+)$", j.get("name", ""))
        if not m:
            continue
        r = load(p.replace(".cg.json", ".result.json")) or {}
        ss = r.get("stage_seconds", {}) or {}
        ev = j.get("memory_events") or {}
        sm = j.get("sampled_max") or {}
        bc = j.get("max_rss_by_comm") or {}
        top = ""
        if bc:
            c, v = max(bc.items(), key=lambda kv: kv[1]["max_rss"])
            top = f"{c} {v['max_rss'] / GiB:.1f} GB x{v['max_concurrent']}"
        v = r.get("verdict") or verdict_near(p) or ("killed (scope stopped)" if j.get("scope_terminated") else f"exit {j['exit']}")
        print(f"| main437 {m.group(1)} cores / {m.group(2)} GB | {v} | {float(j['wall_s']):.0f} | {ss.get('prepare', '')} | {ss.get('build', '')} | "
              f"{ss.get('export', '')} | {ss.get('check_sound', ss.get('checks_total', ''))} | {gb(j['memory_peak'])} | {gb(sm.get('anon'))} | "
              f"{ev.get('oom_kill', '')} | {top} |")
    # the continuation of the kept tree after the disk-full stop (continue_build.sh) and the native export of the result
    # (export_kept.sh): same sandbox and binds, same scope limits; the summed build wall is the cold official build time
    for p, j in rows:
        n = j.get("name", "")
        if n not in ("fv-main437-continue", "fv-main437-export"):
            continue
        ev = j.get("memory_events") or {}
        sm = j.get("sampled_max") or {}
        d = os.path.dirname(p)
        extra = ""
        if n == "fv-main437-continue":
            try:
                extra = f"{open(os.path.join(d, 'built.count')).read().strip()} modules built"
            except OSError:
                try:
                    extra = f"{open(os.path.join(d, 'build.log'), errors='replace').read().count('Built')} modules built"
                except OSError:
                    pass
        else:
            try:
                extra = "export " + open(os.path.join(d, "solution.export.sha256")).read().split()[0][:8] + "; " + \
                        open(os.path.join(d, "closure.out"), errors="replace").read().strip().splitlines()[-1][:60]
            except (OSError, IndexError):
                pass
        label = "main437 continuation (lake build, kept tree)" if n == "fv-main437-continue" else "main437 E1-437 export of the kept tree"
        print(f"| {label} | exit {j['exit']}{' (scope stopped)' if j.get('scope_terminated') else ''} | {float(j['wall_s']):.0f} | | "
              f"{float(j['wall_s']):.0f} | | | {gb(j['memory_peak'])} | {gb(sm.get('anon'))} | {ev.get('oom_kill', '')} | {extra} |")
    print(f"\nG4. Export-in trusted check of the {MAIN437X}, against the pinned RH challenge bb37c4bb (idle machine, one scope "
          "per row; CACHE-BASED input, not from sources).\n")
    print("| check | threads | memory.max | outcome | wall s | peak GB | anon GB | CPU s | OOM kills |\n|---|---|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^sw-(m437x-cs43[67]f?)\.T(\d+)(?:\.M(\S+))?$", j.get("name", ""))
        if not m:
            continue
        ev = j.get("memory_events") or {}
        sm = j.get("sampled_max") or {}
        v = verdict_near(p) or ("killed (scope stopped)" if j.get("scope_terminated") else f"exit {j['exit']}")
        note = p[:-5] + ".note"   # a note next to the JSON (e.g. a row stopped by hand): shown instead of the raw outcome
        if os.path.exists(note):
            v = open(note).read().strip()
        print(f"| {CHECKS437[m.group(1)]} | {m.group(2)} | {m.group(3) or 'max'} | {v} | {float(j['wall_s']):.1f} | {gb(j['memory_peak'])} | "
              f"{gb(sm.get('anon'))} | {int((j.get('cpu_stat') or {}).get('usage_usec', 0)) / 1e6:.0f} | {ev.get('oom_kill', '')} |")

def section_g4b(rows):
    print("\nG4b. Control: the OFFICIAL unmodified Lean 4.37.0-rc1 `leanchecker --from-export` on the same 61 GB export, one process "
          "(700 GB cap, 8 CPUs; also run on a second host).\n")
    print("| run | outcome | wall s | peak GB | anon GB | CPU s |\n|---|---|---|---|---|---|")
    for p, j in rows:
        if j.get("name") != "lc437-official":
            continue
        note = p[:-8] + ".note"
        v = open(note).read().strip() if os.path.exists(note) else f"exit {j['exit']}"
        sm = j.get("sampled_max") or {}
        print(f"| official leanchecker 4.37, single process | {v} | {float(j['wall_s']):.0f} | {gb(j['memory_peak'])} | {gb(sm.get('anon'))} | "
              f"{int((j.get('cpu_stat') or {}).get('usage_usec', 0)) / 1e6:.0f} |")

def section_g5():
    print("\nG5. Per-PR cost on the cache-restored community-main tree (hard-link copy + `patch -p1`, official incremental "
          "`lake build` in the small scope with LEAN_NUM_THREADS = its CPUs, E1-437 export of the Main closure for the pinned "
          "targets + closure guard in the large scope; the CS-437 check of a per-PR export is skipped: an export byte-identical to "
          "the base export - sha 40b0fe82, ACCEPTED by CS-437 in 1,037-1,109 s (G4) - needs no new check; pr321's check "
          "ran on an earlier CS-437 build and was stopped in a replay blow-up). `rebuilt` counts lake's Built "
          "lines; pr321 (default targets) also compiled the ~2,500 modules outside Main's import closure that the community cache never "
          "contained; pr321b is the clean re-run of the same PR with `lake build Main` only, as the later rows. For scale: fvwork in "
          "optimistic mode rebuilt PR #313 in 29 s / 3 modules (the official incremental build re-elaborates the whole importer "
          "cone, 364 modules here). PR #304 is the deep one: 21,622 modules rebuilt by the official incremental build (importer cone 15,075 in a PR "
          "catalog, static dirty cone 24,415 in a separate fast path, which with the module-system interface cutoff rebuilt 81 modules in 59.44 s) "
          "- the official incremental build is the sound fallback, not the daily path.\n")
    print("| PR | files | build scope | build wall s | CPU s | rebuilt | build peak / anon GB | export scope | export wall s | export peak GB | export bytes | sha = base? | check |\n|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    base_sha = "40b0fe8230a1399b7e819b8439ed51c800a3a39122fe6d7b912f371919c6afeb"
    for p in sorted(glob.glob(os.path.join(sys.argv[1], "**", "summary.json"), recursive=True)):
        s = load(p) or {}
        if "build" not in s:
            continue
        d = os.path.dirname(p)
        sha = ""
        try:
            sha = open(os.path.join(d, "solution.export.sha256")).read().split()[0]
        except OSError:
            pass
        bcg = load(os.path.join(d, "build.cg.json")) or {}
        cpu = int((bcg.get("cpu_stat") or {}).get("usage_usec", 0)) / 1e6
        chk = (s.get("check", {}).get("verdict") or "").strip('"')
        note = os.path.join(d, "check.note")
        if os.path.exists(note):
            chk = "stopped (see note)"
        bs, xs = s.get("build_scope", {}), s.get("big_scope", {})
        for sc in (bs, xs):
            if str(sc.get("memory_max", "")).isdigit():
                sc["memory_max"] = f"{int(sc['memory_max']) / GiB:.0f}G"
        print(f"| {s.get('tag')} | {s.get('patched_files')} | {bs.get('cpus')} / {bs.get('memory_max')} | {s['build'].get('wall_s') and round(s['build']['wall_s'])} | {cpu:.0f} | "
              f"{s['build'].get('built_modules')} | {gb(s['build'].get('peak'))} / {gb(s['build'].get('anon'))} | {xs.get('cpus')} / {xs.get('memory_max')} | "
              f"{s['export'].get('wall_s') and round(s['export']['wall_s'])} | {gb(s['export'].get('peak'))} | {s['export'].get('bytes')} | "
              f"{'yes' if sha == base_sha else ('no' if sha else '')} | {chk} |")

def section_f(rows):
    print("\n### F. Export stage E1 alone (native exporter on an existing build tree; Intel host)\n")
    print("| export | threads | wall s | cgroup peak GB | anon GB | file (output cache) GB | exporter RSS GB (incl. mapped oleans) |\n|---|---|---|---|---|---|---|")
    for p, j in rows:
        m = re.match(r"^e1-(miniF|mid|ml|rh|mlclos)\.T(\d+)$", j.get("name", ""))
        if not m:
            continue
        sm = j.get("sampled_max") or {}
        top = j.get("top_procs") or []
        rss = max((t["max_rss"] for t in top if str(t.get("comm", "")).startswith("lean4export")), default=None)
        print(f"| {SIZES[m.group(1)][0]} | {m.group(2)} | {float(j['wall_s']):.1f} | {gb(j['memory_peak'])} | {gb(sm.get('anon'))} | {gb(sm.get('file'))} | {gb(rss)} |")

if __name__ == "__main__":
    main()
