#!/usr/bin/env python3
"""report.py NAME=TRY_WD[:APPLY_OUT] ... — markdown tables of autoshorten runs (search + apply) for COMPRESSION.md.
Per run: modules finished, their lines, positions tried, closable share, candidate savings (all / leaf-only), per-closer
first successes, cost, proof-term size ratio (new/original DAG size), and, with APPLY_OUT, the verified edits (applied,
reverted, lines/chars saved, module elaboration wall time before/after)."""
import json, os, re, sys, glob, collections

STRUCT = re.compile(r"(^|\s)(have|obtain|suffices|calc|show|rcases|by_cases|induction|cases|match|refine)\b")


def load_run(wd):
    idx = dict(l.split() for l in open(os.path.join(wd, "index.txt")))
    R = dict(mods=0, lines=0, chars=0, wall=0.0, pos=0, ok=0, L_all=0, C_all=0, L_leaf=0, C_leaf=0, n_leaf=0,
             first=collections.Counter(), tries=collections.Counter(), ms=collections.Counter(),
             osz=collections.Counter(), nsz=collections.Counter(), nsz_n=collections.Counter(),
             bylen=collections.defaultdict(lambda: [0, 0]), top=0, top_ok=0, top_by=collections.Counter())
    for f in glob.glob(os.path.join(wd, "res", "*.done")):
        n = os.path.basename(f)[:-5]
        rc, sec, rel = open(f).read().split()
        R["mods"] += 1; R["wall"] += float(sec)
        src = os.path.join(wd, "in", n + ".lean")
        data = open(src, "rb").read() if os.path.exists(src) else b""
        R["lines"] += data.count(b"\n"); R["chars"] += len(data)
        rf = os.path.join(wd, "res", n + ".jsonl")
        if not os.path.exists(rf):
            continue
        pos = collections.OrderedDict()
        for l in open(rf):
            try:
                r = json.loads(l)
            except Exception:
                continue
            t = r.get("tmpl", r["tac"])
            R["tries"][t] += 1; R["ms"][t] += r["ms"]
            pos.setdefault((r["spos"], r["epos"]), []).append(r)
        topseen = set()
        cand = []
        for (sp, ep), rs in pos.items():
            R["pos"] += 1
            L = rs[0]["eline"] - rs[0]["line"] + 1
            b = "2" if L <= 2 else "3-4" if L <= 4 else "5-8" if L <= 8 else "9-16" if L <= 16 else "17+"
            R["bylen"][b][0] += 1
            istop = rs[0]["idx"] == 1 and rs[0]["line"] == rs[0]["sline"] and rs[0]["decl"] not in topseen
            if rs[0]["idx"] == 1 and rs[0]["line"] == rs[0]["sline"]:
                topseen.add(rs[0]["decl"])
            if istop:
                R["top"] += 1
            oks = [r for r in rs if r["ok"]]
            if istop and oks:
                R["top_ok"] += 1
                for t in set(r.get("tmpl", r["tac"]) for r in oks):
                    R["top_by"][t] += 1
            if not oks:
                continue
            R["ok"] += 1; R["bylen"][b][1] += 1
            r = oks[0]
            t = r.get("tmpl", r["tac"])
            R["first"][t] += 1
            if r.get("osz", 0) > 0:
                R["osz"][t] += r["osz"]; R["nsz"][t] += r["nsz"]; R["nsz_n"][t] += 1
            txt = r["tac"] if r["ngoals"] == 1 else f"all_goals ({r['tac']})"
            leaf = not STRUCT.search(data[sp:ep].decode("utf-8", "replace"))
            cand.append((sp, ep, L, len(txt.encode()), leaf))
        for leafonly in (False, True):
            sel = []
            for c in sorted([c for c in cand if c[4] or not leafonly], key=lambda c: -(c[1] - c[0])):
                if all(c[1] <= d[0] or d[1] <= c[0] for d in sel):
                    sel.append(c)
            for sp, ep, L, tl, leaf in sel:
                if leafonly:
                    R["L_leaf"] += L - 1; R["C_leaf"] += (ep - sp) - tl; R["n_leaf"] += 1
                else:
                    R["L_all"] += L - 1; R["C_all"] += (ep - sp) - tl
    return R


def load_apply(out):
    A = dict(mods=0, cand_mods=0, applied=0, reverted=0, l0=0, l1=0, c0=0, c1=0, w0=0.0, w1=0.0, failed=0)
    for f in glob.glob(os.path.join(out, "apply.d", "*.json")):
        r = json.loads(open(f).read().strip().splitlines()[-1])
        A["mods"] += 1
        if r.get("status") == "no-candidate":
            continue
        A["cand_mods"] += 1
        if r.get("status") != "ok":
            A["failed"] += 1; continue
        A["applied"] += r.get("applied", 0); A["reverted"] += r.get("reverted", 0)
        A["l0"] += r.get("lines0", 0); A["l1"] += r.get("lines1", 0); A["c0"] += r.get("chars0", 0); A["c1"] += r.get("chars1", 0)
        if "new" in r:
            A["w0"] += r["orig"]["wall"]; A["w1"] += r["new"]["wall"]
    return A


def pct(a, b):
    return f"{100 * a / b:.2f}%" if b else "-"


def main():
    runs = []
    for arg in sys.argv[1:]:
        name, rest = arg.split("=", 1)
        wd, _, ap = rest.partition(":")
        runs.append((name, load_run(wd), load_apply(ap) if ap else None))
    print("| run | modules | lines | positions tried | closable | candidate lines saved (all / leaf-only) | chars saved (all / leaf-only) | whole proofs closable | search wall per module |")
    print("|---|---|---|---|---|---|---|---|---|")
    for name, R, A in runs:
        print(f"| {name} | {R['mods']} | {R['lines']:,} | {R['pos']:,} | {R['ok']:,} ({pct(R['ok'], R['pos'])}) | "
              f"{R['L_all']:,} ({pct(R['L_all'], R['lines'])}) / {R['L_leaf']:,} ({pct(R['L_leaf'], R['lines'])}) | "
              f"{pct(R['C_all'], R['chars'])} / {pct(R['C_leaf'], R['chars'])} | {R['top_ok']}/{R['top']} ({pct(R['top_ok'], R['top'])}) | "
              f"{R['wall'] / max(R['mods'], 1):.0f} s |")
    print()
    for name, R, A in runs:
        print(f"**{name}** — per closer (greedy ladder order: first success per position; tries include failures)\n")
        print("| closer | tries | first successes | success rate | total search time | new/original proof DAG size |")
        print("|---|---|---|---|---|---|")
        for t in R["tries"]:
            ratio = f"{R['nsz'][t] / R['osz'][t]:.2f} (n={R['nsz_n'][t]})" if R["osz"][t] else "-"
            print(f"| `{t}` | {R['tries'][t]:,} | {R['first'][t]} | {pct(R['first'][t], R['tries'][t])} | {R['ms'][t] / 1000:,.0f} s | {ratio} |")
        print()
        print("| suffix lines | positions | closable |\n|---|---|---|")
        for b in ["2", "3-4", "5-8", "9-16", "17+"]:
            print(f"| {b} | {R['bylen'][b][0]:,} | {R['bylen'][b][1]:,} ({pct(R['bylen'][b][1], R['bylen'][b][0])}) |")
        print()
    if any(A for _, _, A in runs):
        print("| run (apply + re-elaboration) | modules with candidates | edits applied | reverted | lines saved in those modules | chars saved | module elaboration wall (orig -> new) |")
        print("|---|---|---|---|---|---|---|")
        for name, R, A in runs:
            if not A:
                continue
            print(f"| {name} | {A['cand_mods']} (failed {A['failed']}) | {A['applied']:,} | {A['reverted']} | {A['l0'] - A['l1']:,} of {A['l0']:,} ({pct(A['l0'] - A['l1'], A['l0'])}) | "
                  f"{pct(A['c0'] - A['c1'], A['c0'])} | {A['w0']:.0f} s -> {A['w1']:.0f} s ({pct(A['w1'] - A['w0'], A['w0'])}) |")


if __name__ == "__main__":
    main()
