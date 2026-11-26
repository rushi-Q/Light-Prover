#!/usr/bin/env python3
"""stats.py WD [--prefer t1,t2,...] — summarize a tryat_batch run: positions tried, closable positions, per-tactic
success, candidate line/char savings (non-overlapping, preferred tactic per position), totals vs the modules' size."""
import json, os, sys, collections, glob

wd = sys.argv[1]
prefer = None
if "--prefer" in sys.argv:
    pl = sys.argv[sys.argv.index("--prefer") + 1]
    prefer = pl.split(";") if ";" in pl else pl.split(",")
idx = {}
for ln in open(os.path.join(wd, "index.txt")):
    n, rel = ln.split()
    idx[n] = rel
done = {}
for f in glob.glob(os.path.join(wd, "res", "*.done")):
    n = os.path.basename(f)[:-5]
    rc, sec, rel = open(f).read().split()
    done[n] = (int(rc), float(sec))
tac_try = collections.Counter(); tac_ok = collections.Counter(); tac_ms = collections.Counter(); tac_hb = collections.Counter()
tot_pos = tot_ok = 0
lines_saved = chars_saved = 0
mod_lines = mod_chars = 0
by_len = collections.defaultdict(lambda: [0, 0, 0])  # suffix lines bucket -> positions, closable, lines saved
top = [0, 0]
first_ok = collections.Counter()
for n, (rc, sec) in done.items():
    rf = os.path.join(wd, "res", n + ".jsonl")
    src = open(os.path.join(wd, "in", n + ".lean"), "rb").read() if os.path.exists(os.path.join(wd, "in", n + ".lean")) else b""
    mod_lines += src.count(b"\n"); mod_chars += len(src)
    if not os.path.exists(rf):
        continue
    pos = collections.OrderedDict()
    for ln in open(rf):
        try:
            r = json.loads(ln)
        except Exception:
            continue
        pos.setdefault((r["spos"], r["epos"]), []).append(r)
        tac_try[r["tmpl"] if "tmpl" in r else r["tac"]] += 1
        if r["ok"]:
            tac_ok[r.get("tmpl", r["tac"])] += 1; tac_hb[r.get("tmpl", r["tac"])] += r["hb"]
        tac_ms[r.get("tmpl", r["tac"])] += r["ms"]
    chosen = []
    for (sp, ep), rs in pos.items():
        tot_pos += 1
        L = rs[0]["eline"] - rs[0]["line"] + 1
        b = "2" if L <= 2 else "3-4" if L <= 4 else "5-8" if L <= 8 else "9-16" if L <= 16 else "17+"
        by_len[b][0] += 1
        if rs[0]["idx"] == 1 and rs[0]["sline"] == rs[0]["line"]:
            pass
        oks = [r for r in rs if r["ok"]]
        if not oks:
            continue
        tot_ok += 1
        if prefer:
            oks.sort(key=lambda r: prefer.index(r.get("tmpl", r["tac"])) if r.get("tmpl", r["tac"]) in prefer else 99)
        first_ok[oks[0].get("tmpl", oks[0]["tac"])] += 1
        chosen.append((sp, ep, L, oks[0], b))
    chosen.sort(key=lambda c: -(c[1] - c[0]))
    sel = []
    for c in chosen:
        if all(c[1] <= d[0] or d[1] <= c[0] for d in sel):
            sel.append(c)
    for sp, ep, L, r, b in sel:
        txt = r["tac"] if r["ngoals"] == 1 else f"all_goals ({r['tac']})"
        lines_saved += L - 1
        chars_saved += (ep - sp) - len(txt.encode())
        by_len[b][1] += 1; by_len[b][2] += L - 1
print(f"modules done {len(done)} (rc!=0: {sum(1 for v in done.values() if v[0] != 0)}), wall-sum {sum(v[1] for v in done.values()):.0f} s")
print(f"module lines {mod_lines}, chars {mod_chars}")
print(f"positions {tot_pos}, closable {tot_ok} ({100*tot_ok/max(tot_pos,1):.1f}%)")
print(f"candidate savings (non-overlapping): lines {lines_saved} ({100*lines_saved/max(mod_lines,1):.2f}% of module lines), chars {chars_saved} ({100*chars_saved/max(mod_chars,1):.2f}%)")
print("per tactic: tries ok ok% sum_ms mean_hb_ok")
for t in tac_try:
    print(f"  {t:28s} {tac_try[t]:7d} {tac_ok[t]:6d} {100*tac_ok[t]/tac_try[t]:5.1f}% {tac_ms[t]/1000:9.0f}s {tac_hb[t]/max(tac_ok[t],1):8.0f}")
print("chosen tactic per closable position:", dict(first_ok))
print("by suffix length: positions closable lines_saved")
for b in ["2", "3-4", "5-8", "9-16", "17+"]:
    print(f"  {b:5s} {by_len[b][0]:6d} {by_len[b][1]:6d} {by_len[b][2]:6d}")
