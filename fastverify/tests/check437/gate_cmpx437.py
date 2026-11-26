#!/usr/bin/python3 -I
"""gate_cmpx437.py CHECK_SOUND PINS CMPX_DIR CHALLENGE CFG1,CFG2 LABELS37.tsv OUT.tsv [JOBS]  - the cmpx corpus check (gates.py semantics)
for a check-sound.sh + pins file, labels = relabel_cmpx.py's label37 column (official 4.37 lake comparator)."""
import concurrent.futures as cf, json, os, subprocess, sys, time
cs, pins, cdir, chal, cfgs, lab, out = sys.argv[1:8]
jobs = int(sys.argv[8]) if len(sys.argv) > 8 else 6
labels = {}
for l in list(open(lab))[1:]:
    p = l.rstrip("\n").split("\t"); labels[(p[0], p[1])] = p[3]
def one(k):
    case, cfg = k
    w = os.path.join(os.path.dirname(os.path.abspath(out)), "cmpx-work", f"{case}.{os.path.basename(cfg)}"); os.makedirs(w, exist_ok=True)
    j = os.path.join(w, "check.json"); t0 = time.time()
    with open(os.path.join(w, "log"), "wb") as lf:
        p = subprocess.run(["timeout", "--kill-after=30", "1800", cs, os.path.join(cdir, case), chal, cfg, "--threads", "8", "--json", j, "--pins", pins],
                           stdout=lf, stderr=subprocess.STDOUT, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": w, "TMPDIR": w}, cwd=w)
    reason = ""
    try: reason = str(json.load(open(j)).get("reason", ""))[:160]
    except Exception: pass
    exp = labels.get((case, os.path.basename(cfg)), "?"); rc = p.returncode
    got = "accept" if rc == 0 else "reject" if rc == 1 else "noverdict"
    cls = "PASS" if got == exp else ("FAIL-CRITICAL" if exp == "reject" and got == "accept" else "FAIL-REJECT" if exp == "accept" and got == "reject" else "WARN-DECLINE")
    return (cls, case, os.path.basename(cfg), exp, got, rc, round(time.time() - t0, 1), reason)
cfgpath = {os.path.basename(c): c for c in cfgs.split(",")}
keys = sorted((case, cfgpath[cb]) for (case, cb) in labels if cb in cfgpath)
rows = []
with cf.ThreadPoolExecutor(jobs) as ex:
    for r in ex.map(one, keys): rows.append(r)
with open(out, "w") as f:
    f.write("class\tcase\tconfig\texpected37\tgot\trc\tsecs\treason\n")
    for r in rows: f.write("\t".join(str(x) for x in r) + "\n")
from collections import Counter
c = Counter(r[0] for r in rows); print(f"cmpx: {len(rows)} runs: " + ", ".join(f"{k} {v}" for k, v in sorted(c.items())) + f" -> {out}")
for r in rows:
    if r[0] != "PASS": print(" ", r[0], r[1], r[2], "expected", r[3], "got", r[4], "|", r[7][:120])
