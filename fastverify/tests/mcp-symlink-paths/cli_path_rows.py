#!/usr/bin/env python3
"""tests/mcp-symlink-paths/cli_path_rows.py FV W HERE_PKG -- cli-path/* rows (bin/fv path policy):
  cli-path/verify-modulo-frontier-{symlink,hardlink}: `fv verify --modulo-frontier FILE` with FILE a symlink / hard link to an
    outside file: refused, the outside line never printed (an earlier version passed the raw path: lib/fastverify realpath'ed it)
  cli-path/extra-arg-{build-cache,export-dir}: --extra-arg=--build-cache=... / --export-dir=... refused (no outside dir created);
  cli-path/extra-arg-positional: a bare --extra-arg value that follows no value-taking option is refused; c/extra-arg-threads-value
  cli-path/verify-build-cache-option-symlink: the new first-class `fv verify --build-cache` is checked (intermediate symlink refused)
  cli-path/bcache-check-dir-intermediate-symlink: build/bcache.py check_dir never creates through a symlinked component
  cli-path/pins-symlink: `fv check --pins LINK` (LINK -> check/sound/pins.env) refused, never followed
  cli-path/watch-fvwork-private-tree: `fv watch DIR --fvwork-state S` sends fvwork a private copy, never DIR; a DIR holding a
    symlink is refused
  cli-path/triage-toolchain-symlink: an explicit --toolchain LINK is refused
  cli-path/fv-cli-roots-anchor: FV_CLI_ROOTS=/that/link makes /that/link/p usable through bin/fv; c/fv-cli-roots-unset: refused
Prints PASS/FAIL rows; writes "P F" to W/count6c."""
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
fv, w, here_pkg = sys.argv[1], sys.argv[2], sys.argv[3]
_TX = ["--experimental"] if "--experimental" in subprocess.run([os.path.join(fv, "bin", "fv"), "triage", "--help"], capture_output=True, text=True).stdout else []   # the `fv triage --experimental` opt-in, only when the installed fv has it
A, O = os.path.join(w, "clip_in"), os.path.join(w, "clip_out")
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


def fvcli(args, timeout=600, env=None, cwd=None):
    e = dict(os.environ)
    e.update(env or {})
    return subprocess.run([os.path.join(fv, "bin", "fv")] + args, capture_output=True, text=True, timeout=timeout, env=e,
                          cwd=cwd or A)


S1 = ["propext", "Quot.sound", "Classical.choice"]
# an officially built + pinned challenge (fv init-challenge) and matching projects, so bin/fastverify really reaches the
# frontier preparation / the build cache (the reproduction setup)
ews = os.path.join(A, "empty_ws")
os.makedirs(os.path.join(ews, ".lake", "packages"))
cs = os.path.join(A, "chal_src")
os.makedirs(cs)
open(os.path.join(cs, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
open(os.path.join(cs, "lakefile.toml"), "w").write('name = "ChalP"\ndefaultTargets = ["ChalP"]\n[[lean_lib]]\nname = "ChalP"\n')
open(os.path.join(cs, "lake-manifest.json"), "w").write('{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n')
open(os.path.join(cs, "ChalP.lean"), "w").write("theorem thm_p (n : Nat) : n + 0 = n := by sorry\n")
json.dump({"challenge_module": "ChalP", "solution_module": "ChalP", "theorem_names": ["thm_p"], "definition_names": [],
           "permitted_axioms": S1}, open(os.path.join(cs, "comparator.json"), "w"))
pc = os.path.join(A, "pinned_chal")
pi = fvcli(["init-challenge", cs, pc, "--threads", "4", "--json"], timeout=900)
try:
    csha = json.loads(pi.stdout)["challenge_sha256"]
except (ValueError, KeyError):
    csha = "0" * 64
    print("SETUP: fv init-challenge failed: %s" % (pi.stdout + pi.stderr)[-300:])
# every call that pins the challenge pins the comparator too
cfsha = hashlib.sha256(open(os.path.join(cs, "comparator.json"), "rb").read()).hexdigest()


def mkproj(name, src):
    d = os.path.join(A, name)
    shutil.copytree(cs, d)
    os.unlink(os.path.join(d, "comparator.json"))
    open(os.path.join(d, "ChalP.lean"), "w").write(src)
    return d


proj = mkproj("proj_fr", "theorem open_helper (n : Nat) : n + 0 = n := by sorry\ntheorem thm_p (n : Nat) : n + 0 = n := open_helper n\n")
proj_good = mkproj("proj_good", "theorem thm_p (n : Nat) : n + 0 = n := Nat.add_zero n\n")
VF = ["--preset", "sound", "--build", "B0", "--packages", ews, "--threads", "4"]

# --modulo-frontier FILE through a symlink / a hard link to an outside file
sec = os.path.join(O, "secret_mf.txt")
open(sec, "w").write("SUPER_SECRET_TOKEN_9988=bad!name\n")
os.symlink(sec, os.path.join(A, "sym_mf.txt"))
try:
    os.link(sec, os.path.join(A, "hl_mf.txt"))
    have_hl = True
except OSError:
    have_hl = False
for kind, f in (("symlink", "sym_mf.txt"), ("hardlink", "hl_mf.txt")):
    if kind == "hardlink" and not have_hl:
        print("SKIP cli-path/verify-modulo-frontier-hardlink: cannot hard-link here")
        continue
    p = fvcli(["verify", proj, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfsha] + VF + ["--modulo-frontier", f, "--json"], timeout=900)
    out = p.stdout + p.stderr
    row("SUPER_SECRET_TOKEN_9988" not in out and sec not in out and p.returncode == 2,
        "cli-path/verify-modulo-frontier-%s" % kind, "exit %d, outside line printed: %s" % (p.returncode, "SUPER_SECRET" in out))

# --extra-arg path options
os.makedirs(os.path.join(O, "victim"))
os.symlink(os.path.join(O, "victim"), os.path.join(A, "sym_interm"))
for opt in ("--build-cache", "--export-dir"):
    tgt = os.path.join(A, "sym_interm", "created" + opt.replace("-", "_"))
    p = fvcli(["verify", proj_good, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfsha] + VF + ["--extra-arg=%s=%s" % (opt, tgt), "--json"],
              timeout=900)
    created = os.path.exists(os.path.join(O, "victim", "created" + opt.replace("-", "_")))
    row(p.returncode == 2 and "extra-arg" in p.stdout and not created, "cli-path/extra-arg-%s" % opt.strip("-"),
        "exit %d, refused %s, outside dir created %s" % (p.returncode, "extra-arg" in p.stdout, created))
p = fvcli(["verify", proj_good, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--extra-arg", "/tmp/positional", "--json"])
row(p.returncode == 2 and "extra-arg" in p.stdout, "cli-path/extra-arg-positional", "exit %d" % p.returncode)
spec = importlib.util.spec_from_file_location("fvc6", os.path.join(fv, "tools", "cli", "fv_cli.py"))
fvc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fvc)
row(fvc.unsafe_extra_args(["--threads", "2", "--build=B3", "--extra-kernel", "nanoda"]) == [], "c/extra-arg-threads-value",
    "value-taking options keep their values")
p = fvcli(["verify", proj_good, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfsha, "--build-cache",
           os.path.join(A, "sym_interm", "bc2"), "--json"])
row(p.returncode == 2 and not os.path.exists(os.path.join(O, "victim", "bc2")), "cli-path/verify-build-cache-option-symlink",
    "exit %d, outside dir created %s" % (p.returncode, os.path.exists(os.path.join(O, "victim", "bc2"))))
spec = importlib.util.spec_from_file_location("bcache6", os.path.join(fv, "build", "bcache.py"))
bc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bc)
r = bc.check_dir(os.path.join(A, "sym_interm", "bc3"))
row(r is False and not os.path.exists(os.path.join(O, "victim", "bc3")), "cli-path/bcache-check-dir-intermediate-symlink",
    "check_dir %s, outside dir created %s" % (r, os.path.exists(os.path.join(O, "victim", "bc3"))))
okd = os.path.join(A, "realcache")
row(bc.check_dir(okd) is True and os.path.isdir(okd), "c/bcache-check-dir-plain", "a plain new cache dir is created and usable")

# --pins through a symlink
os.symlink(os.path.join(fv, "check", "sound", "pins.env"), os.path.join(A, "sym_pins.env"))
zd = os.path.join(here_pkg, "tests", "frontier-axiom-scope", "data", "sorry")
pz = os.path.join(A, "pz")
os.makedirs(pz)
shutil.copyfile(os.path.join(zd, "challenge.export"), os.path.join(pz, "challenge.export"))
json.dump({"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["prove_false"],
           "definition_names": [], "permitted_axioms": S1}, open(os.path.join(pz, "comparator.json"), "w"))
zsha = hashlib.sha256(open(os.path.join(pz, "challenge.export"), "rb").read()).hexdigest()
p = fvcli(["check", os.path.join(zd, "solution.export"), "--challenge", pz, "--challenge-sha256", zsha, "--comparator-sha256", hashlib.sha256(open(os.path.join(pz, "comparator.json"), "rb").read()).hexdigest(), "--pins", "sym_pins.env", "--json"])
row(p.returncode == 2 and "Boundary B4" in p.stdout, "cli-path/pins-symlink", "exit %d: %s" % (p.returncode, p.stdout[-160:].replace("\n", " ")))

# fv watch --fvwork-state: the tree sent is a private copy (fvserve.request captured in-process)
wt = os.path.join(A, "wtree")
os.makedirs(wt)
open(os.path.join(wt, "A.lean"), "w").write("theorem a : True := trivial\n")
st_dir = os.path.join(A, "fvwork_state")
os.makedirs(st_dir)
sent = []
fvc.fvserve.request = lambda state, req, timeout=None: (sent.append(req.get("tree")), {"verdict": "REJECTED", "exit": 1})[1]
sys.argv = ["fv", "watch", wt, "--fvwork-state", st_dir, "--once"]
cwd0 = os.getcwd()
os.chdir(A)
try:
    rc0 = fvc.main()
except SystemExit as e:  # noqa: BLE001
    rc0 = e.code
except BaseException:  # noqa: BLE001
    rc0 = None
# v0.1 refuses daemon-backed watch (`fv watch --fvwork-state`) in v0.1 with exit 2: either behaviour passes -
# a private copy is sent (a package without the refusal), or the command is refused with exit 2 and nothing is sent (v0.1)
priv_sent = bool(sent) and sent[0] and os.path.realpath(sent[0]) != os.path.realpath(wt)
refused = False
if not priv_sent and not sent:   # the v0.1 refusal is checked as the real command: bin/fv watch ... exits 2
    pw = subprocess.run([os.path.join(fv, "bin", "fv"), "watch", wt, "--fvwork-state", st_dir, "--once"], capture_output=True,
                        text=True, timeout=300, cwd=A)
    refused = pw.returncode == 2
    rc0 = "%s; bin/fv watch exit %d" % (str(rc0)[:60], pw.returncode)
row(priv_sent or (refused and not sent), "cli-path/watch-fvwork-private-tree",
    "tree sent: %s (rc %s)" % ("a private copy" if priv_sent else sent, rc0))
os.symlink(sec, os.path.join(wt, "Leak.lean"))
sent.clear()
try:
    rc = fvc.main()
except BaseException:  # noqa: BLE001
    rc = None
os.chdir(cwd0)
row(not sent, "cli-path/watch-fvwork-symlink-in-tree-refused", "request sent: %s (rc %s)" % (bool(sent), rc))

# explicit --toolchain through a symlink
tc33 = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
os.symlink(tc33, os.path.join(A, "sym_tc"))
open(os.path.join(A, "t.lean"), "w").write("theorem t (n : Nat) : n + 0 = n := by sorry\n")
p = fvcli(["triage", *_TX, "t.lean", "--toolchain", "sym_tc", "--static-only", "--json"], timeout=60)
row(p.returncode == 2 and "refused" in (p.stdout + p.stderr), "cli-path/triage-toolchain-symlink", "exit %d" % p.returncode)

# FV_CLI_ROOTS: a workspace reached through the user's own symlink
real = os.path.join(O, "realws")
os.makedirs(os.path.join(real, "p"))
open(os.path.join(real, "p", "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
link = os.path.join(A, "linkws")
os.symlink(real, link)
p = fvcli(["doctor", "--project", os.path.join(link, "p"), "--json"], env={"FV_CLI_ROOTS": link})
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row(p.returncode in (0, 2) and (j.get("project") or {}).get("path") is not None and not j.get("error"), "cli-path/fv-cli-roots-anchor",
    "exit %d, project inspected: %s" % (p.returncode, (j.get("project") or {}).get("path") is not None))
p = fvcli(["doctor", "--project", os.path.join(link, "p"), "--json"], env={"FV_CLI_ROOTS": ""})
row("is a symlink" in p.stdout, "c/fv-cli-roots-unset", "without the anchor the link is refused")
open(os.path.join(w, "count6c"), "w").write("%d %d\n" % (P, F))
