#!/usr/bin/python3 -I
"""relabel_kernel.py TC ROOT OUT.tsv [JOBS]  - run the OFFICIAL `leanchecker --silent --from-export` of toolchain TC on every
*.ndjson export under ROOT/{good,bad} (kernel-only corpora: arena, suitex), sandboxed like gates.py's legs
(bwrap, no network, env: LEAN_ABORT_ON_PANIC=1, LEAN_STACK_SIZE_KB=917376), and record rc + wall + last line.
rc 0 = the official kernel of TC accepts, 1 = rejects, other = no verdict. Output: TSV label37 (good/bad/noverdict), old
label (directory), path."""
import concurrent.futures as cf, os, subprocess, sys, time
tc, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 32
tests = []
for lab in ("good", "bad"):
    for d, _, fs in os.walk(os.path.join(root, lab)):
        for f in sorted(fs):
            if f.endswith(".ndjson"):
                tests.append((lab, os.path.join(d, f)))
tests.sort()
def one(t):
    lab, e = t
    cmd = ["/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--ro-bind", "/", "/",
           "--tmpfs", "/home", "--tmpfs", "/tmp", "--dev", "/dev", "--proc", "/proc", "--ro-bind", tc, tc,
           "--ro-bind", os.path.dirname(e), os.path.dirname(e), "--clearenv", "--setenv", "PATH", tc + "/bin:/usr/bin:/bin",
           "--setenv", "LEAN_ABORT_ON_PANIC", "1", "--setenv", "LEAN_STACK_SIZE_KB", "917376", "--setenv", "LANG", "C.UTF-8",
           "--", "timeout", "--kill-after=10", "900", tc + "/bin/leanchecker", "--from-export", e]
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, errors="replace")
    last = (p.stdout.strip().splitlines() or p.stderr.strip().splitlines() or [""])[-1][:300]
    rc = p.returncode
    new = "good" if rc == 0 else "bad" if rc == 1 else "noverdict(%d)" % rc
    return (new, lab, os.path.relpath(e, root), rc, round(time.time() - t0, 2), last)
rows = []
with cf.ThreadPoolExecutor(jobs) as ex:
    for r in ex.map(one, tests):
        rows.append(r)
with open(out, "w") as f:
    f.write("label37\tlabel_dir\tpath\trc\tsecs\tlast_line\n")
    for r in rows:
        f.write("\t".join(str(x) for x in r) + "\n")
n = len(rows); same = sum(1 for r in rows if r[0] == r[1]); nov = sum(1 for r in rows if r[0].startswith("noverdict"))
print(f"{root}: {n} tests, {same} labels unchanged, {n-same-nov} changed, {nov} no verdict -> {out}")
for r in rows:
    if r[0] != r[1]:
        print("  CHANGED", r[1], "->", r[0], r[2], "|", r[5][:120])
