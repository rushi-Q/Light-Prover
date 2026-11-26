#!/usr/bin/env python3
"""policy.py SRC IN.tsv OUT.tsv --policy all|leaf|leaf-or-hinted — readability policy over an autoshorten edit list (team TSV
format, line numbers against SRC). leaf: drop every edit whose replaced lines contain a structural step (have, obtain,
suffices, calc, show, rcases, by_cases, induction, cases, match, refine) = the proof skeleton stays; leaf-or-hinted: such
an edit is kept only if its closer is hinted (names facts: `simp [..]`, `grind [..]`, ...). Dropping edits from a
module-verified set is safe: each replacement closes its own goals independently of the others."""
import re, sys
STRUCT = re.compile(r"(^|\s)(have|obtain|suffices|calc|show|rcases|by_cases|induction|cases|match|refine)\b")
src, inp, outp = sys.argv[1:4]
pol = sys.argv[sys.argv.index("--policy") + 1] if "--policy" in sys.argv else "all"
cache = {}
kept = dropped = 0
with open(outp, "w") as o:
    for line in open(inp):
        f = line.rstrip("\n").split("\t", 5)
        if pol != "all":
            if f[0] not in cache:
                path = f[0] if f[0].endswith(".lean") else f[0].replace(".", "/") + ".lean"
                cache[f[0]] = open(f"{src}/{path}", encoding="utf-8").read().split("\n")
            orig = "\n".join(cache[f[0]][int(f[1]) - 1:int(f[2])])
            rep = f[5].replace("\\n", "\n")
            if STRUCT.search(orig) and (pol == "leaf" or "[" not in rep):
                dropped += 1; continue
        o.write(line); kept += 1
print(f"policy {pol}: kept {kept}, dropped {dropped}")
