#!/usr/bin/python3 -I
"""relabel_cmpx.py TC CMPX_DIR CHALLENGE_EXPORT CFG1[,CFG2..] OUT.tsv [JOBS]  - the OFFICIAL `lake comparator` of toolchain
TC (`--config CFG --challenge-from-export CH --solution-from-export S --inadvisably-no-sandbox`, run inside our own bwrap
without network, as check-sound.sh runs ccmp) on every *.ndjson of the comparator-level corpus CMPX_DIR; labels in
CMPX_DIR/expected.txt (accept/reject, from the official 4.36 comparator). Records rc (0 accept, 1 reject, 2 cannot run)
and the first `error:` line."""
import concurrent.futures as cf, os, subprocess, sys, tempfile, time
tc, cdir, chal, cfgs, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4].split(","), sys.argv[5]
jobs = int(sys.argv[6]) if len(sys.argv) > 6 else 8
exp = {}
for ln in open(os.path.join(cdir, "expected.txt")):
    p = ln.split()
    if len(p) >= 2:
        exp[p[0]] = p[1]
cases = sorted(f for f in os.listdir(cdir) if f.endswith(".ndjson"))
def one(t):
    case, cfg = t
    e = os.path.join(cdir, case)
    with tempfile.TemporaryDirectory(prefix="relabel-cmpx.", dir=os.environ.get("FV_WORK") or None) as w:
        cmd = ["/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--ro-bind", "/", "/",
               "--tmpfs", "/home", "--tmpfs", "/tmp", "--dev", "/dev", "--proc", "/proc", "--ro-bind", tc, tc,
               "--ro-bind", cdir, cdir, "--ro-bind", os.path.dirname(chal), os.path.dirname(chal), "--ro-bind", os.path.dirname(cfg), os.path.dirname(cfg),
               "--bind", w, w, "--chdir", w, "--clearenv", "--setenv", "PATH", tc + "/bin:/usr/bin:/bin", "--setenv", "HOME", w,
               "--setenv", "TMPDIR", w, "--setenv", "LEAN_ABORT_ON_PANIC", "1", "--setenv", "LANG", "C.UTF-8",
               "--", "timeout", "--kill-after=10", "1800", tc + "/bin/lake", "comparator", "--config", cfg,
               "--challenge-from-export", chal, "--solution-from-export", e, "--inadvisably-no-sandbox"]
        t0 = time.time()
        p = subprocess.run(cmd, capture_output=True, text=True, errors="replace")
        err = next((l for l in (p.stderr + "\n" + p.stdout).splitlines() if l.startswith("error:")), "")
        last = (p.stdout.strip().splitlines() or [""])[-1]
        rc = p.returncode
    lab = "accept" if rc == 0 else "reject" if rc == 1 else "cannotrun(%d)" % rc
    return (case, os.path.basename(cfg), exp.get(case, "?"), lab, rc, round(time.time() - t0, 1), (err or last)[:300])
rows = []
with cf.ThreadPoolExecutor(jobs) as ex:
    for r in ex.map(one, [(c, g) for c in cases for g in cfgs]):
        rows.append(r)
with open(out, "w") as f:
    f.write("case\tconfig\texpected36\tlabel37\trc\tsecs\tmessage\n")
    for r in rows:
        f.write("\t".join(str(x) for x in r) + "\n")
n = len(rows); same = sum(1 for r in rows if r[2] == r[3])
print(f"{cdir}: {n} runs, {same} = expected36, {n-same} differ -> {out}")
for r in rows:
    if r[2] != r[3]:
        print("  DIFF", r[0], r[1], "expected36", r[2], "-> 4.37", r[3], "|", r[6][:140])
