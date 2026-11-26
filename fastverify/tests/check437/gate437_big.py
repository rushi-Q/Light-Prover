#!/usr/bin/python3 -I
"""gate437_big.py PKG OUTDIR [--mathlib] [--mutants] [--threads-matrix] [--jobs J]  - the soundness checks that need the
cross-version 4.37 exports (XD, CASES, XR2 below; under $FV_XVERSION_INPUTS), run through PKG's
check/sound/check-sound.sh --pins check/sound/pins-437.env; expected = the OFFICIAL 4.37 lake comparator's verdicts
(check/xversion/diff/results/results-v4.37.0-rc1.tsv official_verdict; xr2 official-labels.json)."""
import concurrent.futures as cf, json, os, subprocess, sys, time
pkg, out = sys.argv[1], sys.argv[2]; args = sys.argv[3:]
jobs = int(args[args.index("--jobs") + 1]) if "--jobs" in args else 3
cs = f"{pkg}/check/sound/check-sound.sh"; pins = f"{pkg}/check/sound/pins-437.env"
XV = os.environ.get("FV_XVERSION_INPUTS", os.path.join(os.environ.get("FV_BENCH_INPUTS", "/scratch/bench-inputs"), "xversion"))
XD = os.path.join(XV, "xdiff/run-v4.37.0-rc1"); CASES = os.path.join(XV, "xdiff/cases-v4.37.0-rc1"); XR2 = os.path.join(XV, "xr2/v4.37.0-rc1-P1")
os.makedirs(out, exist_ok=True)
def run(name, export, chal, cfg, threads, extra=()):
    w = os.path.join(out, "w", name); os.makedirs(w, exist_ok=True); j = os.path.join(w, "check.json"); t0 = time.time()
    with open(os.path.join(w, "log"), "wb") as lf:
        p = subprocess.run(["timeout", "--kill-after=30", "7200", cs, export, chal, cfg, "--threads", str(threads), "--json", j, "--pins", pins] + list(extra),
                           stdout=lf, stderr=subprocess.STDOUT, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": w, "TMPDIR": w}, cwd=w)
    reason = ""
    try: reason = str(json.load(open(j)).get("reason", ""))[:200]
    except Exception: pass
    return p.returncode, round(time.time() - t0, 1), reason
V = {0: "ACCEPTED", 1: "REJECTED"}
def cls(exp, rc):
    got = V.get(rc, "NOVERDICT")
    if got == exp: return "PASS", got
    if exp == "REJECTED" and got == "ACCEPTED": return "FAIL-CRITICAL", got
    if exp == "ACCEPTED" and got == "REJECTED": return "FAIL-REJECT", got
    return "WARN-DECLINE", got
def table(path, hdr, rows):
    with open(path, "w") as f:
        f.write("\t".join(hdr) + "\n")
        for r in rows: f.write("\t".join(str(x) for x in r) + "\n")
if "--mathlib" in args:
    exp = {}
    for l in list(open(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..", "check", "xversion", "diff", "results", "results-v4.37.0-rc1.tsv")))[1:]:
        p = l.rstrip("\n").split("\t"); exp[p[0]] = p[3]
    cases = json.load(open(f"{CASES}/cases.json"))
    todo = [(c, m) for c, m in cases.items() if os.path.isfile(f"{XD}/p-{c}.export")]
    def one(t):
        c, m = t; ch = m["challenge"]
        rc, s, why = run("mathlib-" + c, f"{XD}/p-{c}.export", f"{XD}/chal-{ch}.export", f"{CASES}/challenges/{ch}/comparator.json", 16)
        k, got = cls(exp.get(c, "?"), rc); return ("mathlib", c, exp.get(c, "?"), rc, got, s, k, why)
    rows = []
    with cf.ThreadPoolExecutor(jobs) as ex:
        for r in ex.map(one, todo): rows.append(r)
    table(f"{out}/mathlib-437.tsv", ["gate", "case", "expected_official37", "rc", "verdict", "seconds", "status", "reason"], rows)
    print("mathlib:", len(rows), "cases;", sum(1 for r in rows if r[6] == "PASS"), "PASS;", [r[1] + ":" + r[6] for r in rows if r[6] != "PASS"])
if "--mutants" in args:
    lab = json.load(open(f"{XR2}/official-labels.json")); inp = json.load(open(f"{XR2}/inputs.json"))
    muts = inp.get("mutants", [])
    def one(m):
        rc, s, why = run("mut-" + m["name"], m["export"], m["challenge"], m["config"], 16)
        k, got = cls(lab.get(m["name"], m.get("expect", "?")), rc); return ("mutants", m["name"], lab.get(m["name"], "?"), rc, got, s, k, why)
    rows = []
    with cf.ThreadPoolExecutor(jobs) as ex:
        for r in ex.map(one, muts): rows.append(r)
    table(f"{out}/mutants-437.tsv", ["gate", "case", "expected_official37", "rc", "verdict", "seconds", "status", "reason"], rows)
    print("mutants:", len(rows), "cases;", sum(1 for r in rows if r[6] == "PASS"), "PASS;", [r[1] + ":" + r[6] for r in rows if r[6] != "PASS"])
if "--threads-matrix" in args:
    rows = []
    for t in (1, 32, 128, 255, 256, 384):
        for c, ch in (("P1", "P1"), ("P2-c-stronger", "P2")):
            rc, s, why = run(f"thr-{t}-{c}", f"{XD}/p-{c}.export", f"{XD}/chal-{ch}.export", f"{CASES}/challenges/{ch}/comparator.json", t)
            rows.append(("threads", c, t, rc, V.get(rc, "NOVERDICT"), s, why))
    table(f"{out}/threads-437.tsv", ["gate", "case", "threads", "rc", "verdict", "seconds", "reason"], rows)
    byc = {}
    for r in rows: byc.setdefault(r[1], set()).add(r[3])
    print("threads:", {k: sorted(v) for k, v in byc.items()}, "IDENTICAL" if all(len(v) == 1 for v in byc.values()) else "DIFFER")
