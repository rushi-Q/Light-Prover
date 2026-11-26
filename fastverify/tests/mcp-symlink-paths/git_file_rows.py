#!/usr/bin/env python3
"""tests/mcp-symlink-paths/git_file_rows.py FV W HERE -- git-file/* rows (`.git` files, challenge .lake/packages, `fv ci` paths):
  git-file/copy-tree-git-file-skipped, git-file/scan-tree-git-file-skipped: a regular-FILE `.git` (git worktree / submodule) is skipped
    by copy_client_tree / scan_client_tree (never read: its gitdir pointer is never followed); c/copy-tree-git-symlink-refused
  git-file/verify-project-git-file: `fv verify` of a worktree-style project (`.git` file pointing outside) gives a verdict
  git-file/verify-challenge-lake-packages: a project with a dependency, challenge in the documented layout (its own
    .lake/packages): `fv verify` uses the challenge's packages workspace (in place, read-only) -> ACCEPTED; needs the
    batteries checkout of FV_PACKAGES_SRC (default the verify/challenge workspace), else SKIP
  c/verify-challenge-lake-packages-symlink: a symlinked .lake/packages is not used (no link followed)
  git-file/ci-*: `bin/fv ci` under the local path policy: symlinked --out-dir parent,
    --allowed-frontier, --pins, a symlink in --project, a symlinked named --cache-dir entry refused, --fv-root refused; a
    planted symlink in --out-dir replaced (never written through); git-file/ci-plain-run-accepted-paths-relocated
Prints PASS/FAIL rows; writes "P F" to W/count6d."""
import hashlib
import json
import os
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
fv, w, here = sys.argv[1], sys.argv[2], sys.argv[3]
A, O = os.path.join(w, "gitf_in"), os.path.join(w, "gitf_out")
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


def env_of(p):
    try:
        return json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    except ValueError:
        return {}


sys.path.insert(0, os.path.join(fv, "tools", "mcp"))
import mcp_server as M  # noqa: E402

# unit: copy_client_tree / scan_client_tree and a `.git` FILE
gd = os.path.join(O, "repo", ".git", "worktrees", "proj")
os.makedirs(gd)
open(os.path.join(gd, "SECRET_GITDIR"), "w").write("not to be read\n")
t1 = os.path.join(A, "wt1")
os.makedirs(t1)
open(os.path.join(t1, "A.lean"), "w").write("theorem a : True := trivial\n")
open(os.path.join(t1, ".git"), "w").write("gitdir: %s\n" % gd)
try:
    fd = os.open(t1, os.O_RDONLY | os.O_DIRECTORY)
    M.copy_client_tree(fd, os.path.join(w, "gitf_copy"))
    os.close(fd)
    row(os.path.isfile(os.path.join(w, "gitf_copy", "A.lean")) and not os.path.exists(os.path.join(w, "gitf_copy", ".git")),
        "git-file/copy-tree-git-file-skipped", "copied, .git file skipped")
except (M.ClientPathError, OSError) as e:
    row(False, "git-file/copy-tree-git-file-skipped", "refused: %s" % e)
try:
    fd = os.open(t1, os.O_RDONLY | os.O_DIRECTORY)
    M.scan_client_tree(fd, single_link=True)
    os.close(fd)
    row(True, "git-file/scan-tree-git-file-skipped", "scan ok")
except (M.ClientPathError, OSError) as e:
    row(False, "git-file/scan-tree-git-file-skipped", "refused: %s" % e)
t2 = os.path.join(A, "wt2")
os.makedirs(t2)
os.symlink(gd, os.path.join(t2, ".git"))
try:
    fd = os.open(t2, os.O_RDONLY | os.O_DIRECTORY)
    M.copy_client_tree(fd, os.path.join(w, "gitf_copy2"))
    os.close(fd)
    row(False, "c/copy-tree-git-symlink-refused", "a symlinked .git was accepted")
except (M.ClientPathError, OSError):
    row(True, "c/copy-tree-git-symlink-refused", "refused")

# e2e: fv verify of a worktree-style project (Init-only; the challenge from sources)
ch = os.path.join(A, "chal_g")
os.makedirs(ch)
open(os.path.join(ch, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
open(os.path.join(ch, "lakefile.toml"), "w").write('name = "G"\ndefaultTargets = ["G"]\n[[lean_lib]]\nname = "G"\n')
open(os.path.join(ch, "lake-manifest.json"), "w").write('{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n')
open(os.path.join(ch, "G.lean"), "w").write("theorem g_thm (n : Nat) : n + 0 = n := by sorry\n")
json.dump({"challenge_module": "G", "solution_module": "G", "theorem_names": ["g_thm"], "definition_names": [],
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(os.path.join(ch, "comparator.json"), "w"))
pj = os.path.join(A, "proj_g")
shutil.copytree(ch, pj)
os.unlink(os.path.join(pj, "comparator.json"))
open(os.path.join(pj, "G.lean"), "w").write("theorem g_thm (n : Nat) : n + 0 = n := Nat.add_zero n\n")
open(os.path.join(pj, ".git"), "w").write("gitdir: %s\n" % gd)
p = fvcli(["verify", pj, "-c", ch, "--threads", "4", "--json"])
j = env_of(p)
row(p.returncode == 0 and j.get("verdict") == "ACCEPTED", "git-file/verify-project-git-file",
    "exit %d %s: %s" % (p.returncode, j.get("verdict"), str(j.get("reason") or j.get("verdict_basis"))[:120]))

# `bin/fv ci` under the local path policy (a pinned challenge from fv init-challenge)
pg = os.path.join(A, "pinned_g")
pi = fvcli(["init-challenge", ch, pg, "--threads", "4", "--json"], timeout=900)
try:
    csha = json.loads(pi.stdout)["challenge_sha256"]
except (ValueError, KeyError):
    csha = "0" * 64
    print("SETUP: fv init-challenge failed: %s" % (pi.stdout + pi.stderr)[-300:])
# every call that pins the challenge pins the comparator too
cfsha = hashlib.sha256(open(os.path.join(pg, "comparator.json"), "rb").read()).hexdigest() if os.path.isfile(os.path.join(pg, "comparator.json")) else "0" * 64
pj_ci = os.path.join(A, "proj_ci")
shutil.copytree(pj, pj_ci)
os.unlink(os.path.join(pj_ci, ".git"))
CI = ["ci", "--experimental", "--project", pj_ci, "--challenge", pg, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--threads", "4"]


def outside_entries():
    return sorted(os.listdir(O))


base_out = outside_entries()
os.symlink(O, os.path.join(A, "symdir"))
p = fvcli(CI + ["--out-dir", os.path.join(A, "symdir", "ci_created_outside")], timeout=900)
row(p.returncode == 2 and outside_entries() == base_out, "git-file/ci-out-dir-intermediate-symlink-refused",
    "exit %d, new outside entries: %s" % (p.returncode, sorted(set(outside_entries()) - set(base_out))))
open(os.path.join(O, "mf_secret.txt"), "w").write("SECRET_MF_LINE_GITF not-a-name\n")
os.symlink(os.path.join(O, "mf_secret.txt"), os.path.join(A, "sym_mf.txt"))
p = fvcli(CI + ["--out-dir", os.path.join(A, "ci_mf"), "--frontier", "--allowed-frontier", os.path.join(A, "sym_mf.txt")], timeout=900)
leak = "SECRET_MF_LINE_GITF" in p.stdout + p.stderr or any("SECRET_MF_LINE_GITF" in open(os.path.join(dp, f), errors="replace").read()
                                                           for dp, _d, fs in os.walk(os.path.join(A, "ci_mf")) for f in fs)
row(p.returncode == 2 and not leak, "git-file/ci-allowed-frontier-symlink-refused", "exit %d, outside line leaked %s" % (p.returncode, leak))
os.symlink(os.path.join(fv, "check", "sound", "pins.env"), os.path.join(A, "sym_pins.env"))
p = fvcli(CI + ["--out-dir", os.path.join(A, "ci_pins"), "--pins", os.path.join(A, "sym_pins.env")], timeout=900)
row(p.returncode == 2 and "pins" in p.stderr, "git-file/ci-pins-symlink-refused", "exit %d: %s" % (p.returncode, p.stderr.strip()[-120:]))
p = fvcli(CI + ["--out-dir", os.path.join(A, "ci_fvroot"), "--fv-root", O], timeout=900)
# the earlier reports of --out-dir are retired FIRST and an ERROR record written, so the directory may now exist,
# holding only that ERROR record
_fr = os.path.join(A, "ci_fvroot")
try:
    _frv = json.load(open(os.path.join(_fr, "result-v1.json"))).get("verdict") if os.path.isdir(_fr) else None
except (OSError, ValueError):
    _frv = "unreadable"
row(p.returncode == 2 and (not os.path.exists(_fr) or (_frv not in ("ACCEPTED", "unreadable") and sorted(os.listdir(_fr)) == ["result-v1.json"])),
    "git-file/ci-fv-root-refused", "exit %d, out-dir: %s" % (p.returncode, sorted(os.listdir(_fr)) if os.path.isdir(_fr) else "absent"))
pj_sym = os.path.join(A, "proj_ci_sym")
shutil.copytree(pj_ci, pj_sym)
os.symlink(os.path.join(O, "mf_secret.txt"), os.path.join(pj_sym, "Extra.lean"))
p = fvcli(["ci", "--experimental", "--project", pj_sym] + CI[4:] + ["--out-dir", os.path.join(A, "ci_psym")], timeout=900)
row(p.returncode == 2 and "symlink" in p.stderr, "git-file/ci-project-symlink-entry-refused", "exit %d: %s" % (p.returncode, p.stderr.strip()[-120:]))
cache = os.path.join(A, "ci_cache")
os.makedirs(cache, mode=0o700)
open(os.path.join(O, "victim_v1.json"), "w").write("UNTOUCHED_V1\n")
os.symlink(os.path.join(O, "victim_v1.json"), os.path.join(cache, "last-v1.json"))
p = fvcli(CI + ["--out-dir", os.path.join(A, "ci_cache_out"), "--cache-dir", cache], timeout=900)
row((p.returncode == 2 or "--cache-dir ignored in v0.1" in p.stderr) and open(os.path.join(O, "victim_v1.json")).read() == "UNTOUCHED_V1\n", "git-file/ci-cache-named-symlink-refused",
    "exit %d: %s" % (p.returncode, p.stderr.strip()[-120:]))
# a full CI run on plain paths: the reports land in the caller's --out-dir (a planted symlink there is replaced, never
# written through) with the caller's paths
co = os.path.join(A, "ci_out")
os.makedirs(co)
open(os.path.join(O, "victim_report.json"), "w").write("UNTOUCHED_REPORT\n")
os.symlink(os.path.join(O, "victim_report.json"), os.path.join(co, "result-v1.json"))
p = fvcli(CI + ["--out-dir", co], timeout=1800)
rv = os.path.join(co, "result-v1.json")
try:
    rj = json.load(open(rv)) if not os.path.islink(rv) else {}
except ValueError:
    rj = {}
txt = json.dumps(rj)
row(open(os.path.join(O, "victim_report.json")).read() == "UNTOUCHED_REPORT\n" and os.path.isfile(rv) and not os.path.islink(rv),
    "git-file/ci-planted-report-symlink-replaced", "exit %d, report a regular file: %s" % (p.returncode, os.path.isfile(rv) and not os.path.islink(rv)))
row(p.returncode == 0 and rj.get("verdict") == "ACCEPTED" and pj_ci in txt and "fv-ci-in." not in txt, "git-file/ci-plain-run-accepted-paths-relocated",
    "exit %d %s; caller's project path in the report %s; private path left %s" % (p.returncode, rj.get("verdict"), pj_ci in txt,
                                                                                "fv-ci-in." in txt))

# e2e: a dependency in the documented challenge layout (challenge/.lake/packages)
src = (os.environ.get("FV_PACKAGES_SRC") or os.environ.get("FV_PACKAGES")
       or os.path.join(os.path.dirname(os.path.realpath(fv)), "verify", "challenge"))
bat = os.path.join(src, ".lake", "packages", "batteries")
D = os.path.join(here, "data_git_files")
dsum = subprocess.run(["sha256sum", "-c", "--quiet", "SHA256SUMS"], cwd=D, capture_output=True, text=True)
if dsum.returncode != 0:
    row(False, "git-file/verify-challenge-lake-packages", "data_git_files: SHA256SUMS mismatch %s" % dsum.stdout[-200:])
elif not os.path.isdir(bat):
    print("SKIP git-file/verify-challenge-lake-packages: no batteries checkout at %s" % bat)
else:
    pd, cd = os.path.join(A, "proj_dep"), os.path.join(A, "chal_dep")
    shutil.copytree(os.path.join(D, "proj"), pd)
    shutil.copytree(os.path.join(D, "chal"), cd)
    os.makedirs(os.path.join(cd, ".lake", "packages"))
    subprocess.run(["/bin/cp", "-a", "--reflink=auto", bat, os.path.join(cd, ".lake", "packages", "batteries")], check=True)
    p = fvcli(["verify", pd, "-c", cd, "--threads", "8", "--json"], timeout=3000)
    j = env_of(p)
    row(p.returncode == 0 and j.get("verdict") == "ACCEPTED", "git-file/verify-challenge-lake-packages",
        "exit %d %s: %s" % (p.returncode, j.get("verdict"), str(j.get("reason") or j.get("verdict_basis"))[:140]))
    # control: the same challenge whose .lake/packages is a symlink (to the real copy) is not used
    cd2 = os.path.join(A, "chal_dep_link")
    shutil.copytree(os.path.join(D, "chal"), cd2)
    os.makedirs(os.path.join(cd2, ".lake"))
    os.symlink(os.path.join(cd, ".lake", "packages"), os.path.join(cd2, ".lake", "packages"))
    p = fvcli(["verify", pd, "-c", cd2, "--threads", "8", "--json"], timeout=1800)
    j = env_of(p)
    row(j.get("verdict") != "ACCEPTED" and p.returncode != 0, "c/verify-challenge-lake-packages-symlink",
        "exit %d %s (the linked workspace was not used)" % (p.returncode, j.get("verdict")))
open(os.path.join(w, "count6d"), "w").write("%d %d\n" % (P, F))
