#!/bin/bash
# tests/no-run-user/run.sh [WORKBASE] -- regression test: builds from sources work on hosts without /run/user:
# every build-from-source sandbox bound `--tmpfs /run/user` over the read-only `/`; on a host without /run/user
# (containers, CI runner images, non-systemd hosts) bwrap failed ("Can't mkdir /run/user: Read-only file system") and every
# run from sources was refused. Fix: the separate /run/user mask is dropped - the `--tmpfs /run` that
# follows in every sandbox already hides all of /run (masking rule unchanged).
# The rows run the package inside an outer `bwrap --dev-bind / / --tmpfs /run`, i.e. on a view of this host WITHOUT
# /run/user: build/official-build.sh, build/build.sh (B1), bin/fastverify --preset sound (ACCEPTED) and --preset reference
# (its build B0 + export E0 stages succeed; its C0 judge is the upstream lake comparator, whose OWN sandbox needs /run/user:
# printed as a NOTE, owned by check/official/check.sh), on a tiny official 4.33.1 project with a source-only challenge, and
# tools/batchverify.py (attempt compile sandbox). setup/run-user-absent: the outer view really lacks /run/user.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
DATA=$HERE/../build-guard-data
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/no-run-user.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
NORUN=(/usr/bin/bwrap --dev-bind / / --tmpfs /run --)
python3 -I -B - "$FV" "$W" "$DATA" "${NORUN[@]}" <<'PY'
import hashlib, json, os, shutil, subprocess, sys
fv, w, data = sys.argv[1:4]
norun = sys.argv[4:]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, "w").write(s)
def run(argv, **kw):
    return subprocess.run(norun + argv, capture_output=True, text=True, **kw)
r = run(["/bin/sh", "-c", "test ! -e /run/user && echo ABSENT"])
row("ABSENT" in r.stdout, "setup/run-user-absent", r.stdout.strip() or r.stderr.strip()[-200:])
tcid = "leanprover/lean4:v4.33.1"
tc = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"][tcid]["prefix"]
chal, proj = os.path.join(w, "chal"), os.path.join(w, "proj")
for d, mod, proof in ((chal, "Challenge", "sorry"), (proj, "Main", "rfl")):
    write(f"{d}/lean-toolchain", tcid + "\n")
    write(f"{d}/lakefile.toml", f'name = "{mod}"\ndefaultTargets = ["{mod}"]\n[[lean_lib]]\nname = "{mod}"\n')
    write(f"{d}/{mod}.lean", f"theorem qaTheorem : 2 + 2 = 4 := {proof}\n")
write(f"{chal}/comparator.json", json.dumps({"challenge_module": "Challenge", "solution_module": "Main",
      "theorem_names": ["qaTheorem"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}))
for name, script, extra in (("official-build", "official-build.sh", []), ("fast-build-b1", "build.sh", ["--preset", "B1"])):
    pj = os.path.join(w, name)
    shutil.copytree(proj, pj)
    r = run([os.path.join(fv, "build", script), pj, "/nonexistent", tc, "--log", pj + ".log", "--threads", "4"] + extra,
            timeout=1800)
    row(r.returncode == 0, name, f"exit {r.returncode}: {(r.stdout + r.stderr).strip()[-200:]}")
for preset in ("reference", "sound"):
    out = os.path.join(w, "out-" + preset)
    # a sound run on a built challenge needs the comparator pin; reference takes it too
    cpin = hashlib.sha256(open(os.path.join(chal, "comparator.json"), "rb").read()).hexdigest()
    r = run([os.path.join(fv, "bin", "fastverify"), proj, chal, out, "--preset", preset, "--threads", "4",
             "--comparator-sha256", cpin], timeout=3600)
    try:
        res = json.load(open(os.path.join(out, "result.json")))
    except (OSError, ValueError):
        res = {}
    v = res.get("verdict")
    if preset == "sound":
        row(v == "ACCEPTED", "fastverify-sound", f"verdict {v}, exit {r.returncode}: {(r.stdout + r.stderr).strip()[-160:]}")
    else:
        # the package's own stages (the challenge build, B0, E0 in lib/fastverify.py sandbox_argv) must work without
        # /run/user; the C0 judge is the UPSTREAM `lake comparator`, whose own sandbox (Lake/CLI/Check.lean:173) binds
        # --tmpfs /run/user - its outcome is reported, not counted here (check/official/check.sh, not this package)
        b, e = res.get("build") or {}, res.get("export") or {}
        row(b.get("exit") == 0 and e.get("exit") == 0, "fastverify-reference-build-export",
            f"build {b.get('option')} exit {b.get('exit')}, export {e.get('option')} exit {e.get('exit')}")
        c0 = json.dumps(res.get("checks") or {})
        print(f"NOTE fastverify-reference C0 judge: verdict {v}" + (" (the upstream lake comparator sandbox needs /run/user: "
              "check/official/check.sh, reported to its owner)" if "/run/user" in c0 else ""), flush=True)
pset = os.path.join(w, "pset"); shutil.copytree(os.path.join(data, "pset"), pset)
chsha = hashlib.sha256(open(os.path.join(pset, "challenge.export"), "rb").read()).hexdigest()
ws = os.path.join(w, "ws"); os.makedirs(os.path.join(ws, ".lake", "packages", "dummy", ".lake", "build", "lib", "lean"))
att = os.path.join(w, "att"); os.makedirs(att)
write(os.path.join(att, "thmA.lean"), "theorem thmA : True := trivial\n")
r = run(["python3", "-I", os.path.join(fv, "tools", "batchverify.py"), "--pset", pset, "--attempts", att, "--out",
         os.path.join(w, "bv"), "--challenge-sha256", chsha, "--toolchain", tc, "--packages", ws, "--threads", "2",
         "--jobs", "1", "--snapshot-header", ""], timeout=1800)
try:
    v = json.load(open(os.path.join(w, "bv", "batch.json")))["attempts"]["thmA"].get("verdict")
except (OSError, ValueError, KeyError):
    v = None
row(v == "ACCEPTED", "batchverify", f"verdict {v}, exit {r.returncode}: {(r.stdout + r.stderr).strip()[-160:]}")
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
