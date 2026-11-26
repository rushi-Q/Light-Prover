#!/usr/bin/env python3
"""summarize.py OUTROOT -> OUTROOT/summary.tsv (one row per case x preset) and OUTROOT/summary.md (case x preset pivot).

status per row: PASS (verdict == expected official verdict), FAIL-CRITICAL (ACCEPTED where the expected verdict is
REJECTED: on challenge CHF every ACCEPT is unsound), WARN (no verdict / false reject of an expected accept), DIFF (other).
The 'reference' preset IS the official flow (B0 + E0 + C0, unmodified Lean 4.33.1 / lean4export / Lean 4.36 lake
comparator): its verdict is the oracle; 'expected_official' in cases.json is the a-priori expectation, checked against it.
"""
import json, os, sys

R = sys.argv[1]
cases = json.load(open(os.path.join(R, "corpus", "cases.json")))
done = {}
p = os.path.join(R, "runs", "done.txt")
if os.path.exists(p):
    for line in open(p):
        f = line.split()
        if len(f) >= 4:
            done[(f[0], f[1])] = (int(f[2]), float(f[3]))

def short(s, n=140):
    s = " ".join(str(s).split())
    return s if len(s) <= n else s[:n - 3] + "..."

def reason_of(r):
    out = []
    for name, c in sorted((r.get("checks") or {}).items()):
        if not isinstance(c, dict):
            continue
        st = c.get("stage") or {}
        msg = st.get("reason") or st.get("detail") or st.get("message") or st.get("error") or c.get("reason") or ""
        out.append("%s=%s%s" % (name, c.get("verdict"), (": " + short(msg, 110)) if msg else ""))
    b = r.get("build") or {}
    if b and b.get("exit") not in (0, None):
        out.append("build(%s) exit %s" % (b.get("option"), b.get("exit")))
    e = r.get("export") or {}
    if e and e.get("exit") not in (0, None):
        out.append("export(%s) exit %s" % (e.get("option"), e.get("exit")))
    return "; ".join(out)

rows = []
presets = []
for (c, pr), (rc, secs) in sorted(done.items()):
    if pr not in presets:
        presets.append(pr)
    meta = cases.get(c, {})
    exp = meta.get("expected_official", "?")
    try:
        r = json.load(open(os.path.join(R, "runs", "%s.%s" % (c, pr), "result.json")))
    except Exception as ex:
        r = {"verdict": "NO-RESULT", "exit": rc}
    v = r.get("verdict")
    b = r.get("build") or {}
    battempts = "+".join("%s:%s" % (a.get("option"), a.get("exit")) for a in (b.get("attempts") or []))
    e = r.get("export") or {}
    eattempts = "+".join("%s:%s" % (a.get("option"), a.get("exit")) for a in (e.get("attempts") or []))
    if pr in ("sound", "fastest") and meta.get("expected_sound") and v == meta["expected_sound"]:   # both build with B3 retries
        st = "PASS" if v == exp else "PASS-SOUND-DIFF"   # documented: sound accepts a VALID proof the official build rejects
    elif v == exp:
        st = "PASS"
    elif v == "ACCEPTED":
        st = "FAIL-CRITICAL" if (exp == "REJECTED" or meta.get("challenge") == "CHF") else "DIFF"
    elif exp == "ACCEPTED":
        st = "WARN"
    else:
        st = "WARN" if v not in ("REJECTED",) else "DIFF"
    rows.append(dict(case=c, preset=pr, challenge=meta.get("challenge"), expected=exp, verdict=v, trust=r.get("trust"),
                     exit=r.get("exit", rc), seconds=secs, build=battempts, export=eattempts,
                     export_sha16=(e.get("sha256") or "")[:16], status=st, reason=reason_of(r),
                     cls=meta.get("cls"), catcher=meta.get("catcher")))

cols = ["case", "preset", "challenge", "expected", "verdict", "status", "trust", "exit", "seconds", "build", "export",
        "export_sha16", "cls", "catcher", "reason"]
with open(os.path.join(R, "summary.tsv"), "w") as f:
    f.write("\t".join(cols) + "\n")
    for x in rows:
        f.write("\t".join(str(x[k]) for k in cols) + "\n")

by = {(x["case"], x["preset"]): x for x in rows}
order = [p for p in ("reference", "sound", "fast-exact", "default") if p in presets] + [p for p in presets if p not in
         ("reference", "sound", "fast-exact", "default")]
with open(os.path.join(R, "summary.md"), "w") as f:
    f.write("| case | class | expected | " + " | ".join(order) + " | agree with reference |\n")
    f.write("|---|---|---|" + "---|" * len(order) + "---|\n")
    for c in sorted({x["case"] for x in rows}):
        cells, vs = [], []
        for p in order:
            x = by.get((c, p))
            if not x:
                cells.append("-")
                continue
            vs.append(x["verdict"])
            mark = "" if x["status"] == "PASS" else " **%s**" % x["status"]
            cells.append("%s (%.0f s)%s" % (x["verdict"], x["seconds"], mark))
        ref = by.get((c, "reference"))
        agree = "-" if not ref else ("yes" if all(v == ref["verdict"] for v in vs) else "**NO**")
        meta = cases.get(c, {})
        f.write("| %s | %s | %s | %s | %s |\n" % (c, meta.get("cls"), meta.get("expected_official"), " | ".join(cells), agree))
n = len(rows)
crit = [x for x in rows if x["status"].startswith("FAIL")]
print("rows %d, PASS %d (+%d PASS-SOUND-DIFF), WARN %d, DIFF %d, FAIL %d" % (n, sum(x["status"] == "PASS" for x in rows),
      sum(x["status"] == "PASS-SOUND-DIFF" for x in rows),
      sum(x["status"] == "WARN" for x in rows), sum(x["status"] == "DIFF" for x in rows), len(crit)))
for x in crit:
    print("FAIL", x["case"], x["preset"], x["verdict"], x["reason"])
