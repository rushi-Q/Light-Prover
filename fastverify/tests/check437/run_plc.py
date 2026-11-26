#!/usr/bin/python3 -I
"""run_plc.py LABELS.tsv ROOT PLC OUT.tsv [JOBS] [THREADS]  - run a pleanchecker binary (`PLC -jT -v --from-export E`, bwrap
sandbox, env as check-sound.sh's Lean leg) on every export of a kernel-only corpus and compare its exit code with the
label37 column of LABELS.tsv (relabel_kernel.py output; path relative to ROOT). Classes: OK, FAIL-CRITICAL (official 4.37
rejects, leg accepts), FAIL-REJECT (official accepts, leg rejects), WARN-DECLINE (other exit)."""
import concurrent.futures as cf, os, subprocess, sys, time
lab, root, plc, out = sys.argv[1:5]
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 16
thr = int(sys.argv[6]) if len(sys.argv) > 6 else 4
hide = sys.argv[7] if len(sys.argv) > 7 else None   # PCHK_HIDE_FILE for the encapsulated replay
extra = [kv.split("=", 1) for kv in sys.argv[8].split(",")] if len(sys.argv) > 8 and sys.argv[8] else []   # extra K=V env (PCHK_ENCAP_BUDGET_MS, PCHK_LIVE_MS)
rows = [l.rstrip("\n").split("\t") for l in open(lab)][1:]
def one(r):
    label, _, rel = r[0], r[1], r[2]
    e = os.path.join(root, rel)
    cmd = ["/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--ro-bind", "/", "/",
           "--tmpfs", "/home", "--tmpfs", "/tmp", "--dev", "/dev", "--proc", "/proc", "--ro-bind", os.path.dirname(plc), os.path.dirname(plc),
           "--ro-bind", os.path.dirname(e), os.path.dirname(e), "--clearenv", "--setenv", "PATH", "/usr/bin:/bin",
           "--setenv", "LEAN_ABORT_ON_PANIC", "1", "--setenv", "LEAN_NUM_THREADS", str(thr), "--setenv", "LEAN_STACK_SIZE_KB", "917376",
           "--setenv", "LANG", "C.UTF-8"] + (["--ro-bind", os.path.dirname(hide), os.path.dirname(hide), "--setenv", "PCHK_HIDE_FILE", hide] if hide else []) + [a for k, v in extra for a in ("--setenv", k, v)] + ["--", "timeout", "--kill-after=10", "900", plc, "-j%d" % thr, "--from-export", e]
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, errors="replace")
    rc = p.returncode
    lines = [l for l in (p.stdout + "\n" + p.stderr).splitlines() if l.strip() and not l.startswith("[pchk")]
    last = (lines or [""])[-1][:240]
    got = "good" if rc == 0 else "bad" if rc == 1 else "noverdict"
    if got == label: cls = "OK"
    elif label == "bad" and got == "good": cls = "FAIL-CRITICAL"
    elif label == "good" and got == "bad": cls = "FAIL-REJECT"
    else: cls = "WARN-DECLINE"
    return (cls, label, got, rc, round(time.time() - t0, 2), rel, last)
res = []
with cf.ThreadPoolExecutor(jobs) as ex:
    for r in ex.map(one, rows):
        res.append(r)
with open(out, "w") as f:
    f.write("class\tlabel37\tgot\trc\tsecs\tpath\tlast_line\n")
    for r in res:
        f.write("\t".join(str(x) for x in r) + "\n")
from collections import Counter
c = Counter(r[0] for r in res)
print(f"{root}: {len(res)} tests: " + ", ".join(f"{k} {v}" for k, v in sorted(c.items())) + f" -> {out}")
for r in res:
    if r[0] != "OK":
        print(" ", r[0], r[5], "label", r[1], "got", r[2], "rc", r[3], "|", r[6][:150])
