#!/usr/bin/env python3
"""mutsum.py OUTROOT... -> mutation campaign summary: per operator, reference (official flow) vs sound verdicts; every
disagreement listed (CRITICAL if sound ACCEPTED where the reference REJECTED)."""
import collections, csv, sys
rows = []
for R in sys.argv[1:]:
    with open(R + "/summary.tsv") as f:
        rows += list(csv.DictReader(f, delimiter="\t"))
by = collections.defaultdict(dict)
for r in rows:
    by[r["case"]][r["preset"]] = r
ops = collections.defaultdict(lambda: collections.Counter())
dis = []
for c, d in sorted(by.items()):
    op = c.split("__")[-1]
    ref, snd = d.get("reference"), d.get("sound")
    if not ref or not snd:
        ops[op]["incomplete"] += 1
        continue
    rv, sv = ref["verdict"], snd["verdict"]
    ops[op]["ref " + rv] += 1
    if rv == sv:
        ops[op]["agree"] += 1
    else:
        ops[op]["DISAGREE"] += 1
        dis.append((c, rv, sv, ("CRITICAL" if sv == "ACCEPTED" else "availability"), snd["reason"][:160], ref["reason"][:120]))
tot = collections.Counter()
print("| operator | pairs | official ACCEPTED | official REJECTED | other | sound == official | disagreements |")
print("|---|---|---|---|---|---|---|")
for op in sorted(ops):
    o = ops[op]; tot.update(o)
    n = o["agree"] + o["DISAGREE"]
    other = n - o["ref ACCEPTED"] - o["ref REJECTED"]
    print("| %s | %d | %d | %d | %d | %d | %d |" % (op, n, o["ref ACCEPTED"], o["ref REJECTED"], other, o["agree"], o["DISAGREE"]))
n = tot["agree"] + tot["DISAGREE"]
print("| **total** | %d | %d | %d | %d | %d | %d |" % (n, tot["ref ACCEPTED"], tot["ref REJECTED"], n - tot["ref ACCEPTED"] - tot["ref REJECTED"], tot["agree"], tot["DISAGREE"]))
if tot["incomplete"]:
    print("\n(incomplete pairs: %d)" % tot["incomplete"])
for x in dis:
    print("DISAGREE %s: official %s, sound %s [%s] sound: %s | official: %s" % x)
