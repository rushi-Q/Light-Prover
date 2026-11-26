#!/usr/bin/env python3
"""tests/mcp-symlink-paths/packages_dir_rows.py FV W -- packagesdir/*, deep-tree/* rows (packagesDir, .git indirection, deep trees, CI reports):
  packagesdir/packagesdir-vendor-link-refused, packagesdir/challenge-packagesdir-link-refused (the workspace manifest's packagesDir,
    not only .lake/packages), packagesdir/packagesdir-escape-refused, packagesdir/git-commondir-refused
  packagesdir/deep-cache-dir-exit-2, packagesdir/deep-incr-base-exit-2, packagesdir/deep-project-exit-2, packagesdir/deep-triage-repo-exit-2 (a
    tree deeper than the walkers' limit is a refusal, exit 2, no traceback)
  packagesdir/triage-no-theorem-unclear
  packagesdir/ci-cache-others-writable-refused, packagesdir/incr-base-others-writable-refused, packagesdir/ci-failed-retry-retires-stale-accepted,
    packagesdir/ci-refusal-retires-stale-accepted, packagesdir/ci-undelivered-no-cache-record, packagesdir/ci-truncated-cache-record-ignored,
    packagesdir/ci-out-dir-inside-project-refused
Prints PASS/FAIL rows; writes "P F" to W/count6f."""
import hashlib
import json
import os
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
fv, w = sys.argv[1], sys.argv[2]
_TX = ["--experimental"] if "--experimental" in subprocess.run([os.path.join(fv, "bin", "fv"), "triage", "--help"], capture_output=True, text=True).stdout else []   # the `fv triage --experimental` opt-in, only when the installed fv has it
A, O = os.path.join(w, "pdir_in"), os.path.join(w, "pdir_out")
os.makedirs(A)
os.makedirs(O)
P = F = 0


def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    if ok:
        P += 1
    else:
        F += 1


def fvcli(args, timeout=1800):
    return subprocess.run([os.path.join(fv, "bin", "fv")] + args, capture_output=True, text=True, timeout=timeout, cwd=A)


def incr_cold_path(p):
    """v0.1: `fv verify --incr-base` takes the COLD path and never reads the
    base's contents (only the base PATH is checked); True iff this run is that cold-path verdict with its warning"""
    try:
        j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    except ValueError:
        j = {}
    txt = json.dumps(j.get("warnings") or []) + str(j.get("verdict_basis") or "")
    return p.returncode == 0 and j.get("verdict") == "ACCEPTED" and "incremental mode is experimental" in txt and "cold path" in txt


GITENV = {"PATH": "/usr/bin:/bin", "HOME": w, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
          "GIT_COMMITTER_EMAIL": "t@t"}
ch = os.path.join(A, "chal")
os.makedirs(ch)
open(os.path.join(ch, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
open(os.path.join(ch, "lakefile.toml"), "w").write('name = "G"\ndefaultTargets = ["G"]\n[[lean_lib]]\nname = "G"\n')
open(os.path.join(ch, "lake-manifest.json"), "w").write('{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n')
open(os.path.join(ch, "G.lean"), "w").write("theorem g_thm (n : Nat) : n + 0 = n := by sorry\n")
json.dump({"challenge_module": "G", "solution_module": "G", "theorem_names": ["g_thm"], "definition_names": [],
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(os.path.join(ch, "comparator.json"), "w"))
pj = os.path.join(A, "proj")
shutil.copytree(ch, pj)
os.unlink(os.path.join(pj, "comparator.json"))
open(os.path.join(pj, "G.lean"), "w").write("theorem g_thm (n : Nat) : n + 0 = n := Nat.add_zero n\n")
pg = os.path.join(A, "pinned")
pi = fvcli(["init-challenge", ch, pg, "--threads", "4", "--json"], timeout=900)
try:
    csha = json.loads(pi.stdout)["challenge_sha256"]
except (ValueError, KeyError):
    csha = "0" * 64
    print("SETUP: fv init-challenge failed: %s" % (pi.stdout + pi.stderr)[-300:])
cfsha = hashlib.sha256(open(os.path.join(ch, "comparator.json"), "rb").read()).hexdigest()
PIN = ["--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4", "--json"]

# an outside git repository a link could point at
repo = os.path.join(O, "secret_repo")
os.makedirs(repo)
open(os.path.join(repo, "Secret.lean"), "w").write("theorem secret : True := trivial\n")
subprocess.run(["git", "init", "-q"], cwd=repo, env=GITENV, check=True)
subprocess.run(["git", "add", "."], cwd=repo, env=GITENV, check=True)
subprocess.run(["git", "commit", "-q", "-m", "s"], cwd=repo, env=GITENV, check=True)
head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, env=GITENV, capture_output=True, text=True).stdout.strip()


def manifest(d, pdir):
    json.dump({"version": "1.1.0", "packagesDir": pdir, "packages": [], "lakeDir": ".lake"},
              open(os.path.join(d, "lake-manifest.json"), "w"))


# ---- packagesDir from the workspace manifest
wv = os.path.join(A, "ws_vendor")
os.makedirs(os.path.join(wv, "vendor"))
manifest(wv, "vendor")
os.symlink(repo, os.path.join(wv, "vendor", "dep"))
p = fvcli(["verify", pj, "-c", pg, "--packages", wv] + PIN)
out = p.stdout + p.stderr
row(p.returncode == 2 and "symlink" in out and head not in out and repo not in out, "packagesdir/packagesdir-vendor-link-refused",
    "exit %d, outside HEAD / path printed %s" % (p.returncode, head in out or repo in out))
cl = os.path.join(A, "chal_pkgs")
shutil.copytree(pg, cl)
os.makedirs(os.path.join(cl, ".lake", "packages"))
os.makedirs(os.path.join(cl, ".lake", "pkgs"))
manifest(cl, ".lake/pkgs")
os.symlink(repo, os.path.join(cl, ".lake", "pkgs", "dep"))
p = fvcli(["verify", pj, "-c", cl] + PIN)
out = p.stdout + p.stderr
row(p.returncode == 2 and "symlink" in out and head not in out, "packagesdir/challenge-packagesdir-link-refused",
    "exit %d, outside HEAD printed %s" % (p.returncode, head in out))
we = os.path.join(A, "ws_escape")
os.makedirs(we)
manifest(we, "../ws_vendor/vendor")
p = fvcli(["verify", pj, "-c", pg, "--packages", we] + PIN)
row(p.returncode == 2 and "packagesDir" in p.stdout + p.stderr, "packagesdir/packagesdir-escape-refused", "exit %d" % p.returncode)

# ---- .git/commondir pointing at another repository
wc = os.path.join(A, "ws_commondir")
gd = os.path.join(wc, ".lake", "packages", "dep", ".git")
os.makedirs(os.path.join(gd, "objects"))
open(os.path.join(gd, "HEAD"), "w").write("ref: refs/heads/main\n")
open(os.path.join(gd, "commondir"), "w").write(os.path.join(repo, ".git") + "\n")
p = fvcli(["verify", pj, "-c", pg, "--packages", wc] + PIN)
out = p.stdout + p.stderr
row(p.returncode == 2 and "commondir" in out and head not in out, "packagesdir/git-commondir-refused",
    "exit %d, outside HEAD printed %s" % (p.returncode, head in out))


# ---- deep trees (1200 levels) are refused, exit 2, no traceback
def deep(root, levels=1200):
    os.makedirs(root)
    cur = root
    for i in range(levels):
        cur = os.path.join(cur, "d")
        os.mkdir(cur)
    return root


dc = deep(os.path.join(A, "deep_cache"))
p = fvcli(["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4",
           "--out-dir", os.path.join(A, "o_deep"), "--cache-dir", dc])
row((p.returncode == 2 or "--cache-dir ignored in v0.1" in p.stderr) and "Traceback" not in p.stderr, "packagesdir/deep-cache-dir-exit-2", "exit %d: %s" % (p.returncode, p.stderr.strip()[-100:]))
di = deep(os.path.join(A, "deep_incr"))
p = fvcli(["verify", pj, "-c", pg, "--incr-base", di] + PIN)
# an earlier package: refused (exit 2, no traceback); v0.1: the base is never read (cold path + warning)
row((p.returncode == 2 or incr_cold_path(p)) and "Traceback" not in p.stderr, "packagesdir/deep-incr-base-exit-2",
    "exit %d, cold path %s" % (p.returncode, incr_cold_path(p)))
dp = os.path.join(A, "deep_proj")
shutil.copytree(pj, dp)
cur = dp
for i in range(1200):
    cur = os.path.join(cur, "d")
    os.mkdir(cur)
p = fvcli(["verify", dp, "-c", pg] + PIN)
row(p.returncode == 2 and "Traceback" not in p.stderr, "packagesdir/deep-project-exit-2", "exit %d" % p.returncode)
tf = os.path.join(A, "t.lean")
open(tf, "w").write("theorem t (n : Nat) : n + 0 = n := by sorry\n")
p = fvcli(["triage", *_TX, tf, "--repo", dp, "--static-only", "--json"])
row(p.returncode == 2 and "Traceback" not in p.stderr, "packagesdir/deep-triage-repo-exit-2", "exit %d" % p.returncode)

# ---- nothing to triage is UNCLEAR (exit 2), never "OK, dispatch"
for lbl, body in (("empty", ""), ("comment-only", "-- nothing here\n")):
    ef = os.path.join(A, "e_%s.lean" % lbl)
    open(ef, "w").write(body)
    p = fvcli(["triage", *_TX, ef, "--static-only", "--json"])
    try:
        j = json.loads(p.stdout)
    except ValueError:
        j = {}
    row(p.returncode == 2 and j.get("status") == "UNCLEAR" and j.get("dispatch_recommended") is False,
        "packagesdir/triage-no-theorem-unclear-%s" % lbl, "exit %d status %r" % (p.returncode, j.get("status")))
# ---- trees the incremental tools keep using must be controlled by the caller alone
co = os.path.join(A, "cache_ow")
os.makedirs(os.path.join(co, "base"))
os.chmod(os.path.join(co, "base"), 0o777)
p = fvcli(["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4",
           "--out-dir", os.path.join(A, "o_ow"), "--cache-dir", co])
row(p.returncode == 2 and "writable by others" in p.stderr or "--cache-dir ignored in v0.1" in p.stderr, "packagesdir/ci-cache-others-writable-refused", "exit %d: %s" % (p.returncode, p.stderr.strip()[-90:]))
io = os.path.join(A, "incr_ow")
os.makedirs(os.path.join(io, "work"))
os.chmod(os.path.join(io, "work"), 0o777)
p = fvcli(["verify", pj, "-c", pg, "--incr-base", io] + PIN)
# an earlier package: refused; v0.1: the base's contents are never read (cold path + warning)
row((p.returncode == 2 and "writable by others" in p.stdout + p.stderr) or incr_cold_path(p), "packagesdir/incr-base-others-writable-refused",
    "exit %d, cold path %s" % (p.returncode, incr_cold_path(p)))

# ---- CI publication never shows a stale / undelivered ACCEPTED
CIP = ["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4"]
od = os.path.join(A, "ci_out")
p = fvcli(CIP + ["--out-dir", od])
first_ok = p.returncode == 0 and "ACCEPTED" in open(os.path.join(od, "summary.md"), errors="replace").read().upper() if os.path.isfile(os.path.join(od, "summary.md")) else False
bad_cfg = ("1" if cfsha[0] != "1" else "2") + cfsha[1:]
p = fvcli(["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", bad_cfg, "--threads", "4", "--out-dir", od])
left = [n for n in os.listdir(od) if n != "result-v1.json" and "ACCEPTED" in (open(os.path.join(od, n), errors="replace").read().upper()
                                                                            if os.path.isfile(os.path.join(od, n)) else "")]
try:
    rv = json.load(open(os.path.join(od, "result-v1.json"))).get("verdict")
except (OSError, ValueError):
    rv = None
row(first_ok and p.returncode != 0 and rv != "ACCEPTED" and not left and not os.path.exists(os.path.join(od, "run", "solution.export")),
    "packagesdir/ci-failed-retry-retires-stale-accepted", "first run ACCEPTED %s; retry exit %d, report %r, stale ACCEPTED files %s" % (
        first_ok, p.returncode, rv, left))
# a refusal (here a symlinked --pins) also retires the earlier reports and leaves an ERROR record
p = fvcli(CIP + ["--out-dir", od])
os.symlink(os.path.join(fv, "check", "sound", "pins.env"), os.path.join(A, "sym_pins.env"))
p2 = fvcli(CIP + ["--out-dir", od, "--pins", os.path.join(A, "sym_pins.env")])
try:
    rv = json.load(open(os.path.join(od, "result-v1.json"))).get("verdict")
except (OSError, ValueError):
    rv = None
row(p.returncode == 0 and p2.returncode == 2 and rv != "ACCEPTED" and not os.path.exists(os.path.join(od, "summary.md")),
    "packagesdir/ci-refusal-retires-stale-accepted", "pass exit %d; refusal exit %d, report %r, summary.md left %s" % (
        p.returncode, p2.returncode, rv, os.path.exists(os.path.join(od, "summary.md"))))
# delivery fails (--out-dir is a regular file): the fresh cache gets no last-v1.json of this undelivered run
cf2 = os.path.join(A, "cache_undeliv")
of = os.path.join(A, "out_is_file")
open(of, "w").write("x\n")
p = fvcli(CIP + ["--out-dir", of, "--cache-dir", cf2])
row(p.returncode == 2 and not os.path.exists(os.path.join(cf2, "last-v1.json")) and "ACCEPTED" not in p.stdout,
    "packagesdir/ci-undelivered-no-cache-record", "exit %d, cache last-v1.json %s" % (p.returncode, os.path.exists(os.path.join(cf2, "last-v1.json"))))
# a truncated previous-run record is set aside (optional input), the run is judged normally
ct = os.path.join(A, "cache_trunc")
os.makedirs(ct)
open(os.path.join(ct, "last-v1.json"), "w").write('{"verdict": "ACC')
p = fvcli(CIP + ["--out-dir", os.path.join(A, "o_trunc"), "--cache-dir", ct])
row(p.returncode == 0 and "ACCEPTED" in p.stdout, "packagesdir/ci-truncated-cache-record-ignored", "exit %d" % p.returncode)
# --out-dir inside the project is refused (as fv-ci.sh itself refuses it)
p = fvcli(CIP + ["--out-dir", os.path.join(pj, "reports")])
row(p.returncode == 2 and not os.path.exists(os.path.join(pj, "reports")), "packagesdir/ci-out-dir-inside-project-refused", "exit %d" % p.returncode)
# ---- deep-tree/*: the earlier reports are retired FIRST, on every exit path
def report_state(d):
    try:
        v = json.load(open(os.path.join(d, "result-v1.json"))).get("verdict")
    except (OSError, ValueError):
        v = None
    acc = [n for n in os.listdir(d) if os.path.isfile(os.path.join(d, n)) and "ACCEPTED" in open(os.path.join(d, n), errors="replace").read().upper()
           and n != "result-v1.json"] if os.path.isdir(d) else []
    return v, acc


od3 = os.path.join(A, "ci_out3")
p0 = fvcli(CIP + ["--out-dir", od3])
p = fvcli(["ci", "--experimental", "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--out-dir", od3])
v, acc = report_state(od3)
row(p0.returncode == 0 and p.returncode == 2 and v != "ACCEPTED" and not acc, "deep-tree/ci-missing-project-retires-stale-accepted",
    "pass exit %d; retry without --project exit %d, report %r, stale ACCEPTED files %s" % (p0.returncode, p.returncode, v, acc))
cdir = os.path.join(A, "cache_recdir")
os.makedirs(os.path.join(cdir, "last-v1.json"))
p = fvcli(CIP + ["--out-dir", os.path.join(A, "o_recdir"), "--cache-dir", cdir])
row(p.returncode == 0 and "ACCEPTED" in p.stdout and "Traceback" not in p.stderr, "deep-tree/ci-cache-record-dir-set-aside",
    "exit %d (an unusable optional record is set aside)" % p.returncode)
# SIGTERM to bin/fv while fv-ci.sh runs: exit 2, an ERROR record, the previous ACCEPTED retired, fv-ci.sh stopped
p0 = fvcli(CIP + ["--out-dir", od3])
import signal as _sg
import time as _t
pr = subprocess.Popen([os.path.join(fv, "bin", "fv")] + CIP + ["--out-dir", od3], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                      text=True, cwd=A)
sid = None
for _i in range(600):   # fv-ci.sh runs as the leader of its own session, a child of bin/fv's python
    kids = subprocess.run(["pgrep", "-P", str(pr.pid)], capture_output=True, text=True).stdout.split()
    if kids:
        sid = kids[0]
        break
    _t.sleep(0.05)
_t.sleep(2)
pr.send_signal(_sg.SIGTERM)
out, err = pr.communicate(timeout=120)
v, acc = report_state(od3)
_t.sleep(1)
left = subprocess.run(["pgrep", "-s", sid], capture_output=True, text=True).stdout.split() if sid else ["no fv-ci.sh seen"]
row(p0.returncode == 0 and pr.returncode == 2 and v != "ACCEPTED" and not acc and not left, "deep-tree/ci-sigterm-during-run-no-stale-accepted",
    "exit %d, report %r, stale ACCEPTED files %s, processes left %s" % (pr.returncode, v, acc, left))
# every packages directory a consumer reads: a link under .lake/packages with packagesDir "vendor" (triage reads .lake/packages)
w3 = os.path.join(A, "ws_both")
os.makedirs(os.path.join(w3, ".lake", "packages"))
os.makedirs(os.path.join(w3, "vendor"))
manifest(w3, "vendor")
os.symlink(repo, os.path.join(w3, ".lake", "packages", "dep"))
tt = os.path.join(A, "tt.lean")
open(tt, "w").write("theorem t (n : Nat) : n + 0 = n := by sorry\n")
p = fvcli(["triage", *_TX, tt, "--packages", w3, "--json"])
row(p.returncode == 2 and "symlink" in p.stdout + p.stderr, "deep-tree/triage-dotlake-link-with-vendor-refused", "exit %d" % p.returncode)
w4 = os.path.join(A, "ws_lakefile")
os.makedirs(os.path.join(w4, "vendor"))
open(os.path.join(w4, "lakefile.toml"), "w").write('name = "x"\npackagesDir = "vendor"\n')
os.symlink(repo, os.path.join(w4, "vendor", "dep"))
p = fvcli(["verify", pj, "-c", pg, "--packages", w4] + PIN)
row(p.returncode == 2 and "symlink" in p.stdout + p.stderr and head not in p.stdout + p.stderr, "deep-tree/lakefile-packagesdir-link-refused",
    "exit %d" % p.returncode)
# ---- the CI gate is EXPERIMENTAL in v0.1 - refused unless opted in, nothing written
envx = {k: v for k, v in os.environ.items() if k != "FV_EXPERIMENTAL_CI"}
ogate = os.path.join(A, "o_gate")
p = subprocess.run([os.path.join(fv, "bin", "fv"), "ci", "--project", pj, "--challenge", pg, "--challenge-sha256", csha,
                    "--comparator-sha256", cfsha, "--out-dir", ogate], capture_output=True, text=True, timeout=300, cwd=A, env=envx)
row(p.returncode == 2 and "EXPERIMENTAL" in p.stderr and not os.path.exists(ogate), "deep-tree/ci-experimental-gate-fv-ci",
    "exit %d: %s" % (p.returncode, p.stderr.strip()[-100:]))
p = subprocess.run([os.path.join(fv, "tools", "ci-action", "fv-ci.sh"), "--project", pj, "--challenge", pg, "--challenge-sha256", csha,
                    "--out-dir", ogate], capture_output=True, text=True, timeout=300, cwd=A, env=envx)
row(p.returncode == 2 and "EXPERIMENTAL" in p.stderr and not os.path.exists(ogate), "deep-tree/ci-experimental-gate-fv-ci-sh",
    "exit %d: %s" % (p.returncode, p.stderr.strip()[-100:]))
# ---- a package .git must be a repository of its own; the workspace must be the caller's alone
we2 = os.path.join(A, "ws_emptygit")
os.makedirs(os.path.join(we2, ".lake", "packages", "dep", ".git"))
p = fvcli(["verify", pj, "-c", pg, "--packages", we2] + PIN)
row(p.returncode == 2 and "git repository of its own" in p.stdout + p.stderr, "deep-tree/packages-empty-git-refused", "exit %d" % p.returncode)
wow = os.path.join(A, "ws_otherwritable")
os.makedirs(os.path.join(wow, ".lake", "packages"))
os.chmod(os.path.join(wow, ".lake", "packages"), 0o777)
p = fvcli(["verify", pj, "-c", pg, "--packages", wow] + PIN)
row(p.returncode == 2 and "writable by others" in p.stdout + p.stderr, "deep-tree/packages-others-writable-refused", "exit %d" % p.returncode)
# --packages inside --out-dir: refused before anything is retired (the workspace is never deleted)
oo = os.path.join(A, "ci_out_pk")
os.makedirs(os.path.join(oo, "run", ".lake", "packages"))
open(os.path.join(oo, "run", "keep.txt"), "w").write("INPUT\n")
p = fvcli(["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", "0" * 64,
           "--packages", os.path.join(oo, "run"), "--out-dir", oo])
row(p.returncode == 2 and os.path.isfile(os.path.join(oo, "run", "keep.txt")), "deep-tree/ci-packages-inside-out-dir-not-deleted",
    "exit %d, workspace intact %s" % (p.returncode, os.path.isfile(os.path.join(oo, "run", "keep.txt"))))
# ---- deep-tree/*: CI out-dir overlap, stale ACCEPTED reports
# an input reached through a LINK into --out-dir is refused before anything is retired (it was deleted)
on = os.path.join(A, "ci_out_n1")
os.makedirs(os.path.join(on, "run"))
open(os.path.join(on, "run", "keep.txt"), "w").write("INPUT\n")
os.symlink(os.path.join(on, "run"), os.path.join(A, "pklink"))
p = fvcli(["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha,
           "--packages", os.path.join(A, "pklink"), "--out-dir", on])
row(p.returncode == 2 and os.path.isfile(os.path.join(on, "run", "keep.txt")), "deep-tree/ci-input-link-into-out-dir-not-deleted",
    "exit %d, input intact %s" % (p.returncode, os.path.isfile(os.path.join(on, "run", "keep.txt"))))
# the overlap refusal still neutralises the earlier ACCEPTED (result-v1.json ERROR, summary.md removed); the input stays
ol = os.path.join(A, "ci_out_l3")
p0 = fvcli(CIP + ["--out-dir", ol])
open(os.path.join(ol, "run", "keep.txt"), "w").write("INPUT\n")
p = fvcli(CIP + ["--out-dir", ol, "--packages", os.path.join(ol, "run")])
try:
    rv = json.load(open(os.path.join(ol, "result-v1.json"))).get("verdict")
except (OSError, ValueError):
    rv = None
row(p0.returncode == 0 and p.returncode == 2 and rv != "ACCEPTED" and not os.path.exists(os.path.join(ol, "summary.md"))
    and os.path.isfile(os.path.join(ol, "run", "keep.txt")), "deep-tree/ci-overlap-refusal-neutralises-stale-accepted",
    "pass exit %d; refusal exit %d, report %r, summary.md left %s" % (p0.returncode, p.returncode, rv, os.path.exists(os.path.join(ol, "summary.md"))))
# SIGKILL of bin/fv: fv-ci.sh (its own session) is stopped too (PR_SET_PDEATHSIG)
pr = subprocess.Popen([os.path.join(fv, "bin", "fv")] + CIP + ["--out-dir", os.path.join(A, "ci_out_l1")], stdout=subprocess.PIPE,
                      stderr=subprocess.PIPE, text=True, cwd=A)
sid = None
for _i in range(600):
    kids = subprocess.run(["pgrep", "-P", str(pr.pid)], capture_output=True, text=True).stdout.split()
    if kids:
        sid = kids[0]
        break
    _t.sleep(0.05)
_t.sleep(2)
pr.kill()
pr.communicate(timeout=60)
left = ["no fv-ci.sh seen"] if not sid else None
for _i in range(60):
    if sid:
        left = subprocess.run(["pgrep", "-s", sid], capture_output=True, text=True).stdout.split()
        if not left:
            break
    _t.sleep(0.5)
row(not left, "deep-tree/ci-sigkill-stops-fv-ci-sh", "processes of fv-ci.sh's session left: %s" % left)
# triage / the audit probe read the packages directory Lake uses (the manifest's packagesDir)
sys.path.insert(0, os.path.join(fv, "tools", "triage"))
sys.path.insert(0, os.path.join(fv, "schemas"))
import triage as _tr   # noqa: E402
wl = os.path.join(A, "ws_lakedir")
os.makedirs(os.path.join(wl, "vendor"))
manifest(wl, "vendor")
row(_tr.lake_packages_dir(wl) == os.path.join(os.path.realpath(wl), "vendor"), "deep-tree/triage-uses-lake-packages-dir",
    "resolved %s" % _tr.lake_packages_dir(wl))
# ---- a sticky parent owned by ANOTHER account is refused; a root-owned sticky one (/tmp) is not
import importlib.util as _ilu   # noqa: E402
_spec = _ilu.spec_from_file_location("fv_cli_h6", os.path.join(fv, "tools", "cli", "fv_cli.py"))
_fvc = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(_fvc)
_real_lstat = os.lstat


class _St:
    def __init__(self, uid, mode, gid=0):
        self.st_uid, self.st_mode, self.st_gid = uid, mode, gid


def _h6(owner):
    def fake(p, *a, **k):
        return _St(owner, 0o41777) if p == "/fv_h6_parent" else _real_lstat(p, *a, **k)
    _fvc.os.lstat = fake
    try:
        _fvc._check_parents("/fv_h6_parent/leaf")
        return "accepted"
    except Exception as e:  # noqa: BLE001
        return "refused" if "another account" in str(e) else "error %r" % e
    finally:
        _fvc.os.lstat = _real_lstat


r_foreign, r_root = _h6(54321 if os.getuid() != 54321 else 54322), _h6(0)
row(r_foreign == "refused" and r_root == "accepted", "deep-tree/sticky-parent-foreign-owner-refused",
    "foreign-owned sticky parent: %s; root-owned sticky parent: %s" % (r_foreign, r_root))
open(os.path.join(w, "count6f"), "w").write("%d %d\n" % (P, F))
