#!/usr/bin/env python3
"""fill.py CONFIG.json -> fills the @@TOKENS@@ of sections/{correctness,frontier}.md from the recorded result tables
and writes sections/out/{correctness,frontier}.md (then published with secedit.py).
CONFIG: {"canonical": "results/rF", "runs": [[label, dir, ref_dir_or_null], ...], "cases": cases.json,
         "verifiers": verifiers.tsv, "mut": [dirs], "t21c0": "text", "amd": dir_or_null}"""
import collections, csv, json, os, subprocess, sys

H = os.path.dirname(os.path.abspath(__file__))
cfg = json.load(open(sys.argv[1]))
cases = json.load(open(cfg["cases"]))

def tsv(p):
    with open(p) as f:
        return list(csv.DictReader(f, delimiter="\t"))

def runrows(d):
    return {(r["case"], r["preset"]): r for r in tsv(os.path.join(d, "summary.tsv"))}

canon = runrows(cfg["canonical"])
canon_ref = {c: r["verdict"] for (c, p), r in canon.items() if p == "reference"}
total = 0
lines = []
for label, d, refd in cfg["runs"]:
    rr = runrows(d)
    ref = {c: r["verdict"] for (c, p), r in rr.items() if p == "reference"} or canon_ref
    if refd:
        ref = {c: r["verdict"] for (c, p), r in runrows(refd).items() if p == "reference"}
    n = agree = crit = sdiff = 0
    for (c, p), r in rr.items():
        total += 1
        if p == "reference":
            continue
        n += 1
        ov = ref.get(c)
        if r["verdict"] == ov:
            agree += 1
        elif p in ("sound", "fastest") and r["verdict"] == cases.get(c, {}).get("expected_sound"):
            sdiff += 1
        if r["verdict"] == "ACCEPTED" and ov == "REJECTED" and not (p in ("sound", "fastest") and cases.get(c, {}).get("expected_sound") == "ACCEPTED"):
            crit += 1
        if r["verdict"] == "ACCEPTED" and cases.get(c, {}).get("challenge") in ("CHF", "CHMF"):
            crit += 1
    nref = sum(1 for (c, p) in rr if p == "reference")
    nov = sum(1 for (c, p), r in rr.items() if p != "reference" and r["verdict"] not in ("ACCEPTED", "REJECTED"))
    lines.append("| %s | %d (%d official + %d fast) | %d / %d%s%s | %d |" % (label, len(rr), nref, n, agree, n,
                 (" (+%d documented accept of a valid proof, T21)" % sdiff) if sdiff else "",
                 ("; %d no verdict" % nov) if nov else "", crit))

# catcher counts on the canonical official runs
src = open(os.path.join(H, "report.py")).read().split('presets = ["reference"')[0]
ns = {"sys": sys}
sys_argv = sys.argv
sys.argv = ["x", cfg["cases"], os.path.join(cfg["canonical"], "summary.tsv"), cfg["verifiers"]]
exec(src, ns)
sys.argv = sys_argv
cnt = collections.Counter(ns["catcher"](r) for (c, p), r in canon.items() if p == "reference" and r["verdict"] != "ACCEPTED")
nrej = sum(cnt.values())
catch = ", ".join("%s %d" % (k, v) for k, v in cnt.most_common())

# mutation table
mt = subprocess.run([sys.executable, os.path.join(H, "mutsum.py")] + cfg["mut"], capture_output=True, text=True).stdout
mutn = 0
for l in mt.splitlines():
    if l.startswith("| **total**"):
        mutn = int(l.split("|")[2])
audit = open(os.path.join(H, "AUDIT-primitives.md")).read().split("\n", 2)[2]
rep = subprocess.run([sys.executable, os.path.join(H, "report.py"), cfg["cases"], os.path.join(cfg["canonical"], "summary.tsv"),
                      cfg["verifiers"]] + ([os.path.join(cfg["amd"], "summary.tsv")] if cfg.get("amd") else []),
                     capture_output=True, text=True).stdout
mut_runs = 2 * mutn
tok = {"@@RUNTABLE@@": "\n".join(lines), "@@NREJ@@": str(nrej), "@@CATCH@@": catch, "@@MUTN@@": str(mutn),
       "@@MUTTABLE@@": mt.strip(), "@@AUDIT@@": audit.strip(), "@@TOTALRUNS@@": "{:,}".format(total + mut_runs),
       "@@NCASES@@": str(len(cases)), "@@T21C0@@": cfg.get("t21c0", "pending"), "@@VERIFTABLE@@": rep.strip()}
os.makedirs(os.path.join(H, "sections", "out"), exist_ok=True)
for name in ("correctness.md", "frontier.md"):
    s = open(os.path.join(H, "sections", name)).read()
    for k, v in tok.items():
        s = s.replace(k, v)
    left = [w for w in s.split() if w.startswith("@@")]
    open(os.path.join(H, "sections", "out", name), "w").write(s)
    print(name, "unfilled:", left)
print("total runs", total, "mutants", mutn)
