#!/usr/bin/env python3
"""report.py CASES_JSON SUMMARY_TSV VERIFIERS_TSV [AMD_SUMMARY_TSV] > results.md

Merges the full-verifier runs (run.sh -> summary.tsv: official reference / sound / fast-exact / default) and the naive
verifier configurations (verifiers.py -> verifiers.tsv: V1 compiles, V2 no sorry warning, V3 + #print axioms + statement
text, V4 kernel replay only) into the tables of the cheat benchmark. "fooled" = the configuration ACCEPTS a case whose
official verdict is REJECTED (for challenge CHF / CHMF: a proof of a false statement).
"""
import csv, json, sys

cases = json.load(open(sys.argv[1]))
def tsv(p):
    with open(p) as f:
        return list(csv.DictReader(f, delimiter="\t"))
runs = tsv(sys.argv[2])
ver = {r["case"]: r for r in tsv(sys.argv[3])}
amd = {}
if len(sys.argv) > 4:
    for r in tsv(sys.argv[4]):
        amd[(r["case"], r["preset"])] = r
by = {(r["case"], r["preset"]): r for r in runs}

def catcher(r):
    if not r:
        return "-"
    if r["verdict"] == "ACCEPTED":
        return "(accepted)"
    rs = r["reason"]
    if "build(" in rs:
        return "build fails"
    if "export(" in rs:
        return "export fails (target missing)"
    if "statement do not match" in rs or "kind don't match" in rs or "Const does not match" in rs or "Const not found" in rs:
        return "comparison (statement/definition)"
    if "Constant not found" in rs:
        return "axiom-closure walk (dependency missing)"
    if "Illegal axiom" in rs:
        return "axiom check"
    if "kernel" in rs.lower() or "exited with" in rs or "rejected" in rs:
        return "kernel replay"
    return rs[:40]

def short_v(r):
    if not r:
        return "-"
    return {"ACCEPTED": "ACC", "REJECTED": "rej"}.get(r["verdict"], r["verdict"])

presets = ["reference", "sound", "fast-exact", "default"]
out = []
out.append("| case | class | official (reference) | sound | fast-exact | default | sound on AMD (zygote) | caught by (official flow) "
           "| V1 compiles | V2 +no sorry | V3 +axioms +text | V4 kernel only |")
out.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
fooled = {k: [] for k in ("V1", "V2", "V3", "V4", "reference", "sound", "fast-exact", "default", "amd-sound")}
nrej = 0
agree = disagree = 0
valid_extra = []
for c in sorted(cases):
    m = cases[c]
    ref = by.get((c, "reference"))
    exp = ref["verdict"] if ref else m["expected_official"]
    cells = []
    for p in presets:
        r = by.get((c, p))
        cells.append(short_v(r))
        if r and ref:
            if r["verdict"] == ref["verdict"]:
                agree += 1
            else:
                disagree += 1
        if r and r["verdict"] == "ACCEPTED" and exp == "REJECTED":
            if p == "sound" and m.get("expected_sound") == "ACCEPTED" and m["challenge"] not in ("CHF", "CHMF"):
                cells[-1] = "ACC (valid proof, official build fails)"   # documented: the official comparator accepts its export
                valid_extra.append(c)
            else:
                fooled[p].append(c)
    a = amd.get((c, "sound"))
    cells.append(short_v(a) if a else "-")
    if a and a["verdict"] == "ACCEPTED" and exp == "REJECTED":
        if m.get("expected_sound") == "ACCEPTED" and m["challenge"] not in ("CHF", "CHMF"):
            cells[-1] = "ACC (valid proof, official build fails)"
        else:
            fooled["amd-sound"].append(c)
    v = ver.get(c, {})
    vc = []
    for k in ("V1", "V2", "V3"):
        acc = v.get(k) == "True"
        vc.append("ACC" if acc else "rej" if v else "-")
        if acc and exp == "REJECTED":
            fooled[k].append(c)
    v4 = v.get("V4", "-")
    acc4 = v4 == "ACCEPT"
    vc.append("ACC" if acc4 else ("rej" if v4 in ("REJECT", "export-failed", "no-build") else v4))
    if acc4 and exp == "REJECTED":
        fooled["V4"].append(c)
    if exp == "REJECTED":
        nrej += 1
    mark = lambda s: ("**%s**" % s) if (s == "ACC" and exp == "REJECTED") else s
    out.append("| %s | %s | %s | %s | %s | %s |" % (c, m["cls"], " | ".join(mark(x) for x in cells), catcher(ref),
                                                     " | ".join(mark(x) for x in vc), ""))
    out[-1] = out[-1].rstrip(" |") + " |"
print("\n".join(out))
print()
print("Cases with official verdict REJECTED: %d; full-verifier verdicts equal to the official one: %d of %d (%d differ%s)."
      % (nrej, agree, agree + disagree, disagree,
         (": " + ", ".join(valid_extra) + " = sound accepts a VALID proof whose official build fails; the unmodified official "
          "lake comparator accepts the very export the sound run checked") if valid_extra else ""))
print()
print("| verifier configuration | accepts how many of the %d officially rejected cases | which |" % nrej)
print("|---|---|---|")
names = {"V1": "V1 `lake build` succeeds", "V2": "V2 + no `sorry` warning", "V3": "V3 + `#print axioms` only standard + statement text verbatim",
         "V4": "V4 kernel replay only (official lean4export + leanchecker 4.36)", "reference": "official `lake comparator` flow (reference)",
         "sound": "fastverify `--preset sound` (test host)", "fast-exact": "fastverify `--preset fast-exact`", "default": "fastverify `--preset default`",
         "amd-sound": "fastverify `--preset sound` (AMD, zygote toolchain)"}
for k in ("V1", "V2", "V3", "V4", "reference", "sound", "fast-exact", "default", "amd-sound"):
    if k == "amd-sound" and not amd:
        continue
    print("| %s | %d | %s |" % (names[k], len(fooled[k]), ", ".join(x.split("-")[0] for x in fooled[k]) or "-"))
