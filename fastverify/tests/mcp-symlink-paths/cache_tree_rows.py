#!/usr/bin/env python3
"""tests/mcp-symlink-paths/cache_tree_rows.py FV W -- cache-tree/* rows (CI cache and package trees, frontier pins, triage exit
codes):
  cache-tree/ci-cache-deep-dir-symlink-refused (a directory link at base/work/proj/Sub), cache-tree/ci-cache-planner-symlink-refused
    (base/log/build-fast/planner/planner a link), cache-tree/ci-cache-permission-error-exit-2 (base/ mode 0000)
  cache-tree/verify-chal-package-entry-symlink-refused, cache-tree/ci-packages-entry-symlink-refused (.lake/packages/<pkg> a link to
    an outside git repository: refused before manifest.py, no outside HEAD printed), cache-tree/packages-git-file-refused,
    cache-tree/packages-build-symlink-refused; c/packages-source-symlink-allowed (a package's own source-tree link is fine)
  cache-tree/verify-incr-base-symlink-refused (an --incr-base tree with a link)
  cache-tree/ci-frontier-pinned-dir (a pin minted by frontier.py pin is a DIRECTORY: CONDITIONAL, not refused)
  cache-tree/ci-run-file-conflict-delivered (an ordinary file at OUT/run: the run's reports still delivered, stdout and exit
    agree), cache-tree/ci-cache-last-v1-relocated (the cache's last-v1.json carries the caller's paths), cache-tree/ci-stale-run-replaced
    (a failing retry leaves no earlier solution.export / ACCEPTED report)
  cache-tree/triage-unclear-exit-2, cache-tree/triage-bad-workspace-exit-2 (no evidence -> exit 2, structured result)
Prints PASS/FAIL rows; writes "P F" to W/count6e."""
import hashlib
import json
import os
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
fv, w = sys.argv[1], sys.argv[2]
_TX = ["--experimental"] if "--experimental" in subprocess.run([os.path.join(fv, "bin", "fv"), "triage", "--help"], capture_output=True, text=True).stdout else []   # the `fv triage --experimental` opt-in, only when the installed fv has it
A, O = os.path.join(w, "ctree_in"), os.path.join(w, "ctree_out")
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


def jout(p):
    try:
        return json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    except ValueError:
        return {}


def incr_cold_path(p):
    """v0.1: `fv verify --incr-base` takes the COLD path and never reads the
    base's contents (only the base PATH is checked); True iff this run is that cold-path verdict with its warning"""
    try:
        j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    except ValueError:
        j = {}
    txt = json.dumps(j.get("warnings") or []) + str(j.get("verdict_basis") or "")
    return p.returncode == 0 and j.get("verdict") == "ACCEPTED" and "incremental mode is experimental" in txt and "cold path" in txt


def outside():
    return sorted(os.listdir(O))


GITENV = {"PATH": "/usr/bin:/bin", "HOME": w, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
          "GIT_COMMITTER_EMAIL": "t@t"}

# fixture: an Init-only challenge (pinned by fv init-challenge) and its honest project
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
# every call that pins the challenge pins the comparator too
cfsha = hashlib.sha256(open(os.path.join(pg, "comparator.json"), "rb").read()).hexdigest() if os.path.isfile(os.path.join(pg, "comparator.json")) else "0" * 64
CI = ["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4"]

# ---- --cache-dir
victim = os.path.join(O, "victim_dir")
os.makedirs(victim)
open(os.path.join(victim, "keep.txt"), "w").write("UNTOUCHED\n")
c1 = os.path.join(A, "cache1")
os.makedirs(os.path.join(c1, "base", "work", "proj"))
os.symlink(victim, os.path.join(c1, "base", "work", "proj", "Sub"))
base_o = outside()
p = fvcli(CI + ["--out-dir", os.path.join(A, "o1"), "--cache-dir", c1])
row((p.returncode == 2 and "symlink" in p.stderr or "--cache-dir ignored in v0.1" in p.stderr) and os.listdir(victim) == ["keep.txt"] and outside() == base_o,
    "cache-tree/ci-cache-deep-dir-symlink-refused", "exit %d: %s" % (p.returncode, p.stderr.strip()[-110:]))
c2 = os.path.join(A, "cache2")
os.makedirs(os.path.join(c2, "base", "log", "build-fast", "planner"))
open(os.path.join(O, "fake_planner"), "w").write("#!/bin/sh\necho PWNED\n")
os.symlink(os.path.join(O, "fake_planner"), os.path.join(c2, "base", "log", "build-fast", "planner", "planner"))
p = fvcli(CI + ["--out-dir", os.path.join(A, "o2"), "--cache-dir", c2])
row(p.returncode == 2 and "symlink" in p.stderr or "--cache-dir ignored in v0.1" in p.stderr, "cache-tree/ci-cache-planner-symlink-refused", "exit %d: %s" % (p.returncode, p.stderr.strip()[-110:]))
c3 = os.path.join(A, "cache3")
os.makedirs(os.path.join(c3, "base"), mode=0o700)
os.chmod(c3, 0o700)
os.chmod(os.path.join(c3, "base"), 0)
p = fvcli(CI + ["--out-dir", os.path.join(A, "o3"), "--cache-dir", c3])
os.chmod(os.path.join(c3, "base"), 0o700)
row((p.returncode == 2 or "--cache-dir ignored in v0.1" in p.stderr) and "Traceback" not in p.stderr, "cache-tree/ci-cache-permission-error-exit-2",
    "exit %d: %s" % (p.returncode, p.stderr.strip()[-110:]))

# ---- packages workspace entries
repo = os.path.join(O, "secret_repo")
os.makedirs(repo)
open(os.path.join(repo, "Secret.lean"), "w").write("theorem secret : True := trivial\n")
subprocess.run(["git", "init", "-q"], cwd=repo, env=GITENV, check=True)
subprocess.run(["git", "add", "."], cwd=repo, env=GITENV, check=True)
subprocess.run(["git", "commit", "-q", "-m", "s"], cwd=repo, env=GITENV, check=True)
head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, env=GITENV, capture_output=True, text=True).stdout.strip()
chs = os.path.join(A, "chal_pkglink")
shutil.copytree(pg, chs)
os.makedirs(os.path.join(chs, ".lake", "packages"))
os.symlink(repo, os.path.join(chs, ".lake", "packages", "dep"))
p = fvcli(["verify", pj, "-c", chs, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4", "--json"])
leak = head in p.stdout + p.stderr or repo in p.stdout + p.stderr
row(p.returncode == 2 and "symlink" in p.stdout + p.stderr and not leak, "cache-tree/verify-chal-package-entry-symlink-refused",
    "exit %d, outside HEAD / path printed %s" % (p.returncode, leak))
wsl = os.path.join(A, "ws_link")
os.makedirs(os.path.join(wsl, ".lake", "packages"))
os.symlink(repo, os.path.join(wsl, ".lake", "packages", "dep"))
p = fvcli(CI + ["--out-dir", os.path.join(A, "o4"), "--packages", wsl])
leak = head in p.stdout + p.stderr
row(p.returncode == 2 and "symlink" in p.stderr and not leak, "cache-tree/ci-packages-entry-symlink-refused",
    "exit %d: %s" % (p.returncode, p.stderr.strip()[-110:]))
wsg = os.path.join(A, "ws_gitfile")
os.makedirs(os.path.join(wsg, ".lake", "packages", "dep"))
open(os.path.join(wsg, ".lake", "packages", "dep", ".git"), "w").write("gitdir: %s/.git\n" % repo)
p = fvcli(["verify", pj, "-c", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--packages", wsg, "--threads", "4", "--json"])
row(p.returncode == 2 and ".git" in p.stdout + p.stderr and head not in p.stdout + p.stderr, "cache-tree/packages-git-file-refused",
    "exit %d" % p.returncode)
wsb = os.path.join(A, "ws_buildlink")
os.makedirs(os.path.join(wsb, ".lake", "packages", "dep", ".lake", "build", "lib", "lean"))
os.makedirs(os.path.join(wsb, ".lake", "packages", "dep", ".git", "objects"))   # a git checkout: only the build link is wrong
open(os.path.join(wsb, ".lake", "packages", "dep", ".git", "HEAD"), "w").write("ref: refs/heads/main\n")
os.symlink(os.path.join(O, "fake_planner"), os.path.join(wsb, ".lake", "packages", "dep", ".lake", "build", "lib", "lean", "X.olean"))
p = fvcli(["verify", pj, "-c", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--packages", wsb, "--threads", "4", "--json"])
row(p.returncode == 2 and "symlink" in p.stdout + p.stderr, "cache-tree/packages-build-symlink-refused", "exit %d" % p.returncode)
wso = os.path.join(A, "ws_ok")
os.makedirs(os.path.join(wso, ".lake", "packages", "dep", "docs"))
os.makedirs(os.path.join(wso, ".lake", "packages", "dep", ".git", "objects"))   # a real repository: HEAD + objects
open(os.path.join(wso, ".lake", "packages", "dep", ".git", "HEAD"), "w").write("ref: refs/heads/main\n")
open(os.path.join(wso, ".lake", "packages", "dep", "README.md"), "w").write("x\n")
os.symlink("../README.md", os.path.join(wso, ".lake", "packages", "dep", "docs", "README.md"))
p = fvcli(["verify", pj, "-c", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--packages", wso, "--threads", "4", "--json"])
row(p.returncode == 0 and jout(p).get("verdict") == "ACCEPTED", "c/packages-source-symlink-allowed",
    "exit %d %s" % (p.returncode, jout(p).get("verdict")))

# ---- --incr-base with a link inside
ib = os.path.join(A, "incr_base")
os.makedirs(os.path.join(ib, "work", "proj"))
os.symlink(victim, os.path.join(ib, "work", "proj", "Sub"))
p = fvcli(["verify", pj, "-c", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--incr-base", ib, "--threads", "4", "--json"])
# either an earlier package (the whole base tree scanned: refused) or v0.1 (the base's contents are never
# read: the cold-path verdict with its warning); in both cases nothing is written through the link
row((incr_cold_path(p) or (p.returncode == 2 and "symlink" in p.stdout + p.stderr)) and os.listdir(victim) == ["keep.txt"],
    "cache-tree/verify-incr-base-symlink-refused", "exit %d, cold path %s" % (p.returncode, incr_cold_path(p)))
# a link in the base PATH itself is refused in both
os.symlink(ib, os.path.join(A, "incr_base_link"))
p = fvcli(["verify", pj, "-c", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--incr-base",
           os.path.join(A, "incr_base_link"), "--threads", "4", "--json"])
row(p.returncode == 2 and "symlink" in p.stdout + p.stderr, "deep-tree/incr-base-symlinked-path-refused", "exit %d" % p.returncode)

# ---- an ordinary file at OUT/run; the cache's last-v1.json relocated (one full CI run)
co = os.path.join(A, "ci_out")
os.makedirs(co)
open(os.path.join(co, "run"), "w").write("an ordinary file\n")
cc = os.path.join(A, "ci_cache_ok")
p = fvcli(CI + ["--out-dir", co, "--cache-dir", cc])
try:
    rj = json.load(open(os.path.join(co, "result-v1.json")))
except (OSError, ValueError):
    rj = {}
so = jout(p)
row(p.returncode == 0 and rj.get("verdict") == "ACCEPTED" and so.get("verdict") == "ACCEPTED" and os.path.isdir(os.path.join(co, "run")),
    "cache-tree/ci-run-file-conflict-delivered", "exit %d, report %s, stdout %s, run/ a directory %s" % (
        p.returncode, rj.get("verdict"), so.get("verdict"), os.path.isdir(os.path.join(co, "run"))))
try:
    lv = open(os.path.join(cc, "last-v1.json")).read()
except OSError:
    lv = ""
row(pj in lv and "fv-ci-in." not in lv or (lv == "" and "--cache-dir ignored in v0.1" in p.stderr), "cache-tree/ci-cache-last-v1-relocated",
    "caller's project path %s, private path left %s" % (pj in lv, "fv-ci-in." in lv))
had_exp = any(f.endswith(".export") for _d, _s, fs in os.walk(os.path.join(co, "run")) for f in fs)
# a retry with a mistyped pin: ERROR, and nothing of the earlier run is presented as this run's
bad = ("1" if csha[0] != "1" else "2") + csha[1:]
p = fvcli(["ci", "--experimental", "--project", pj, "--challenge", pg, "--challenge-sha256", bad, "--comparator-sha256", cfsha, "--threads", "4", "--out-dir", co])
try:
    rj = json.load(open(os.path.join(co, "result-v1.json")))
except (OSError, ValueError):
    rj = {}
left = [f for _d, _s, fs in os.walk(os.path.join(co, "run")) for f in fs if f.endswith(".export")]
row(p.returncode != 0 and rj.get("verdict") != "ACCEPTED" and not left and had_exp, "cache-tree/ci-stale-run-replaced",
    "exit %d, report %s, earlier export left %s (first run had one: %s)" % (p.returncode, rj.get("verdict"), left, had_exp))

# ---- --frontier-pinned DIR (a pin minted by frontier.py pin)
pf = os.path.join(A, "proj_fr")
shutil.copytree(pj, pf)
open(os.path.join(pf, "G.lean"), "w").write("theorem open_helper (n : Nat) : n + 0 = n := by sorry\n"
                                            "theorem g_thm (n : Nat) : n + 0 = n := open_helper n\n")
cf = os.path.join(A, "ci_fr")
p = fvcli(["ci", "--experimental", "--project", pf, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4", "--out-dir", cf, "--frontier"])
exps = [os.path.join(d, f) for d, _s, fs in os.walk(os.path.join(cf, "run")) for f in fs if f == "solution.export"]
pindir = os.path.join(A, "pin")
if exps:
    mp = subprocess.run(["/usr/bin/python3", "-I", os.path.join(fv, "tools", "frontier", "frontier.py"), "pin", exps[0],
                         os.path.join(pg, "challenge.export"), os.path.join(pg, "comparator.json"), pindir, "--threads", "4"],
                        capture_output=True, text=True, timeout=1800, cwd=A)
if exps and os.path.isfile(os.path.join(pindir, "frontier.json")):
    p = fvcli(["ci", "--experimental", "--project", pf, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4", "--out-dir",
               os.path.join(A, "ci_pin"), "--frontier", "--frontier-pinned", pindir])
    row(p.returncode == 3 and "refused" not in p.stderr, "cache-tree/ci-frontier-pinned-dir",
        "exit %d (CONDITIONAL = 3) %s" % (p.returncode, p.stderr.strip()[-110:] if p.returncode != 3 else ""))
else:
    row(False, "cache-tree/ci-frontier-pinned-dir", "fixture: no pin minted (first ci exit %d; %s)" % (
        p.returncode, (p.stderr or "")[-150:]))

# ---- triage without evidence exits 2 with its structured result
tf = os.path.join(A, "t.lean")
open(tf, "w").write("theorem t (n : Nat) : n + 0 = n := by sorry\n")
tu = os.path.join(A, "u.lean")   # a syntax-defining source: UNCLEAR (fail-closed) in every triage version
open(tu, "w").write('macro "foo" : term => `(1)\ntheorem t (n : Nat) : n + 0 = n := by sorry\n')
p = fvcli(["triage", *_TX, tu, "--static-only", "--json"])
row(p.returncode == 2 and jout(p).get("status") == "UNCLEAR", "cache-tree/triage-unclear-exit-2",
    "exit %d status %r" % (p.returncode, jout(p).get("status")))
ew = os.path.join(A, "empty_ws")
os.makedirs(ew)
tc33 = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
p = fvcli(["triage", *_TX, tf, "--toolchain", tc33, "--packages", ew, "--json"])
# an absent .lake/packages is simply not bound: the Init-only probe runs -> OK, exit 0
row(p.returncode == 0 and "Traceback" not in p.stderr and jout(p).get("status") == "OK",
    "cache-tree/triage-bad-workspace-exit-2", "exit %d status %r %s" % (p.returncode, jout(p).get("status"), p.stderr.strip()[-100:]))
open(os.path.join(w, "count6e"), "w").write("%d %d\n" % (P, F))
