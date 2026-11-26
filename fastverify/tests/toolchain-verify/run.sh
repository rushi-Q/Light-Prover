#!/bin/bash
# tests/toolchain-verify/run.sh [WORKBASE] -- regression test: batchverify and fvserve verify --toolchain (MEDIUM):
# tools/batchverify.py and tools/fvserve/fvserve.py never verified --toolchain with lib/toolchain.py verify (bin/fastverify
# does, docs/getting-started.md promises it) and mapped a bwrap start failure (missing toolchain / packages) of a VALID
# attempt to REJECTED.
# Rows:
#   batchverify/{fake,missing}-toolchain, batchverify/missing-packages: no batch, exit 2, never a verdict
#   batchverify/sandbox-start-failure: a compile whose bwrap cannot start (packages dir gone after the start) -> NO-VERDICT
#   batchverify/control-valid: the verified official toolchain still ACCEPTS a valid attempt
#   fvserve/fake-toolchain: the service refuses to start (exit 2, no socket)
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
DATA=$HERE/../build-guard-data
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/toolchain-verify.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
(cd "$DATA" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
python3 -I -B - "$FV" "$W" "$DATA" <<'PY'
import hashlib, json, os, shutil, subprocess, sys, time
sys.dont_write_bytecode = True
fv, w, data = sys.argv[1:4]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
tc = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
pset = os.path.join(w, "pset"); shutil.copytree(os.path.join(data, "pset"), pset)
chsha = hashlib.sha256(open(os.path.join(pset, "challenge.export"), "rb").read()).hexdigest()
ws = os.path.join(w, "ws"); os.makedirs(os.path.join(ws, ".lake", "packages", "dummy", ".lake", "build", "lib", "lean"))
att = os.path.join(w, "att"); os.makedirs(att)
open(os.path.join(att, "thmA.lean"), "w").write("theorem thmA : True := trivial\n")
fake = os.path.join(w, "fake", "leanprover--lean4---v4.33.1"); os.makedirs(os.path.join(fake, "bin"))
open(os.path.join(fake, "bin", "lean"), "w").write("#!/bin/sh\necho 'error: unofficial lean' >&2\nexit 1\n")
os.chmod(os.path.join(fake, "bin", "lean"), 0o755)
def bv(name, toolchain, packages):
    out = os.path.join(w, "bv-" + name)
    p = subprocess.run(["python3", "-I", os.path.join(fv, "tools", "batchverify.py"), "--pset", pset, "--attempts", att,
                        "--out", out, "--challenge-sha256", chsha, "--toolchain", toolchain, "--packages", packages,
                        "--threads", "2", "--jobs", "1", "--snapshot-header", ""], capture_output=True, text=True, timeout=900)
    try:
        v = json.load(open(os.path.join(out, "batch.json")))["attempts"]["thmA"].get("verdict")
    except (OSError, ValueError, KeyError):
        v = None
    return p.returncode, v, p.stderr[-300:]
for name, t, pk in (("fake-toolchain", fake, ws), ("missing-toolchain", os.path.join(w, "nonexistent_toolchain"), ws),
                    ("missing-packages", tc, os.path.join(w, "nonexistent_ws"))):
    rc, v, err = bv(name, t, pk)
    row(rc == 2 and v is None, "batchverify/" + name, f"exit {rc}, verdict {v}" + ("" if rc == 2 and v is None else f" ({err.strip()[-160:]})"))
rc, v, err = bv("control", tc, ws)
row(rc == 0 and v == "ACCEPTED", "batchverify/control-valid", f"exit {rc}, verdict {v}")
# a compile whose sandbox cannot start (the packages dir disappears after the batch started)
code = r'''
import argparse, json, os, shutil, sys
sys.path.insert(0, os.path.join(sys.argv[1], "tools")); import batchverify as bv
fv, w, pset, att, tc, ws, chsha = sys.argv[1:8]
a = argparse.Namespace(pset=pset, attempts=att, out=os.path.join(w, "bv-unit"), challenge_sha256=chsha, threads=2, jobs=1,
                       packages=ws, toolchain=tc, fv=fv, export_dir=None, skip_kernel_tc=False, snapshot_cache=None,
                       snapshot_header="", root_module=False, confirm_failures="errors", attempt_timeout=300, par=1, split=2,
                       limits=None, pins=None)
b = bv.Batch(a)
os.rename(os.path.join(ws, ".lake", "packages"), os.path.join(ws, ".lake", "packages.gone"))
try:
    b.build_attempts(["thmA"])
finally:
    os.rename(os.path.join(ws, ".lake", "packages.gone"), os.path.join(ws, ".lake", "packages"))
print("RESULT " + json.dumps(b.res["attempts"]["thmA"]))
'''
p = subprocess.run(["python3", "-I", "-c", code, fv, w, pset, att, tc, ws, chsha], capture_output=True, text=True, timeout=600)
try:
    r = json.loads(p.stdout.split("RESULT ", 1)[1])
except (IndexError, ValueError):
    r = {"verdict": None, "why": p.stderr[-200:]}
row(r.get("verdict") == "NO-VERDICT", "batchverify/sandbox-start-failure", f"verdict {r.get('verdict')}: {str(r.get('why'))[:160]}")
# fvserve with an unverified toolchain
state = os.path.join(w, "fvs")
srv = subprocess.Popen(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "serve", "--state", state,
                        "--pset", f"demo={pset}:{chsha}", "--toolchain", fake, "--packages", ws, "--threads", "2",
                        "--snapshot-header", "import Init"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
for _ in range(240):
    if os.path.exists(os.path.join(state, "sock")) or srv.poll() is not None:
        break
    time.sleep(0.5)
sock = os.path.exists(os.path.join(state, "sock"))
if srv.poll() is None:
    subprocess.run(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "stop", "--state", state], capture_output=True)
    try:
        srv.wait(30)
    except subprocess.TimeoutExpired:
        srv.kill()
row(not sock and srv.returncode == 2, "fvserve/fake-toolchain", f"socket {'created (service started)' if sock else 'absent'}, exit {srv.returncode}")
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
