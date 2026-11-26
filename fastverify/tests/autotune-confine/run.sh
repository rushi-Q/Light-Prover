#!/bin/bash
# tests/autotune-confine/run.sh [WORKBASE] -- regression test: lib/autotune.py never reads outside the project (MEDIUM; see also
# tests/lakefile-escape; the same class via MCP
# fv_doctor / fv_verify_project): lib/autotune.py runs on the HOST before any sandbox (bin/fastverify --preset sound-auto at
# CLI parse time, MCP fv_doctor, bin/fv verify, fv-ci.sh) and walked / read / grepped the UNTRUSTED lakefile.toml srcDir
# outside the project (absolute, '../', a symlinked srcDir directory), followed a lean-toolchain / lakefile.toml symlink
# out of the project, and hung on a FIFO named *.lean. The rows follow the
# reproduction steps.
# Rows: autotune/* (lib/autotune.py PROJECT --json), e2e/fastverify-preflight (bin/fastverify --preset sound-auto
#   --preflight-only: result.json autotune), e2e/mcp-doctor (tools/mcp/mcp_server.run_host_doctor, as fv_doctor runs it);
#   control/*: an honest project with srcDir = "src" and a file symlink inside the project is still scanned as before.
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/autotune-confine.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
python3 -I -B - "$FV" "$W" <<'PY'
import json, os, subprocess, sys
sys.dont_write_bytecode = True
fv, w = sys.argv[1:3]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, "w").write(s)
out = os.path.join(w, "outside")
write(f"{out}/secret_dir/SecretAlpha.lean", "@[to_additive]\ndef alpha : Nat := 1\n")
write(f"{out}/secret_dir/SecretBeta.lean", "import Mathlib\n@[to_dual]\ndef beta : Nat := 2\n")
write(f"{out}/toolchain_secret.txt", "TOOLCHAIN_SECRET_Z04_8\n")
write(f"{out}/lakefile_secret.toml", f'name = "x"\nsrcDir = "{out}"\n[[lean_lib]]\nname = "secret_dir"\nglobs = ["secret_dir.*"]\n')
os.makedirs(f"{out}/fifo_dir"); os.mkfifo(f"{out}/fifo_dir/HangOutside.lean")
SECRETS = ("SecretAlpha", "SecretBeta", "secret_dir", "TOOLCHAIN_SECRET", "HangOutside")
def proj(name, lakefile=None, files=None):
    pj = os.path.join(w, "allowed", name)
    write(f"{pj}/lean-toolchain", "leanprover/lean4:v4.36.0\n")
    if lakefile is not None:
        write(f"{pj}/lakefile.toml", lakefile)
    for k, v in (files or {}).items():
        write(f"{pj}/{k}", v)
    return pj
def autotune(pj, timeout=40):
    try:
        p = subprocess.run(["python3", "-I", os.path.join(fv, "lib", "autotune.py"), pj, "--json"], capture_output=True,
                           text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", "timeout"
def leaked(txt):
    return [s for s in SECRETS if s in txt]

lib = '[[lean_lib]]\nname = "secret_dir"\nglobs = ["secret_dir.*"]\n'
cases = {
    "abs-srcdir-globs": proj("abs", f'name = "p"\nsrcDir = "{out}"\n' + lib),
    "lib-srcdir-dotdot": proj("dotdot", 'name = "p"\n[[lean_lib]]\nname = "secret_dir"\nsrcDir = "../../outside"\nglobs = ["secret_dir.*"]\n'),
    "srcdir-tilde": proj("tilde", 'name = "p"\nsrcDir = "~/"\n' + lib),
    "abs-srcdir-fifo": proj("fifo", f'name = "p"\nsrcDir = "{out}"\n[[lean_lib]]\nname = "fifo_dir"\nglobs = ["fifo_dir.*"]\n'),
}
pj = proj("dirlink", 'name = "p"\nsrcDir = "sub"\n' + lib); os.symlink(out, os.path.join(pj, "sub")); cases["srcdir-dir-symlink"] = pj
for name, pj in cases.items():
    rc, so, se = autotune(pj)
    row(rc == 2 and not leaked(so + se), "autotune/" + name,
        f"exit {rc}, nothing outside reported" if rc == 2 and not leaked(so + se) else f"exit {rc}, leaked {leaked(so + se)} {se[-120:]}")
# links / special files INSIDE the project: never followed out, never block
pj = proj("links", 'name = "p"\n[[lean_lib]]\nname = "Main"\nglobs = ["Main.*"]\n', {"Main.lean": "theorem t : True := trivial\n"})
os.symlink(f"{out}/secret_dir/SecretAlpha.lean", os.path.join(pj, "Main", "SecretLink.lean") if os.path.isdir(os.path.join(pj, "Main")) else os.path.join(pj, "SecretLink.lean"))
os.unlink(os.path.join(pj, "lean-toolchain")); os.symlink(f"{out}/toolchain_secret.txt", os.path.join(pj, "lean-toolchain"))
os.makedirs(os.path.join(pj, "Main")); os.mkfifo(os.path.join(pj, "Main", "Fifo.lean"))
os.symlink(f"{out}/secret_dir/SecretBeta.lean", os.path.join(pj, "Main", "Beta.lean"))
rc, so, se = autotune(pj)
row(rc == 0 and not leaked(so + se), "autotune/inside-links-and-fifo",
    f"exit {rc}, no hang, nothing outside read" if rc == 0 and not leaked(so + se) else f"exit {rc}, leaked {leaked(so + se)} {se[-160:]}")
pj = proj("lakelink", None, {"Main.lean": "theorem t : True := trivial\n"})
os.symlink(f"{out}/lakefile_secret.toml", os.path.join(pj, "lakefile.toml"))
rc, so, se = autotune(pj)
row(rc == 0 and not leaked(so + se), "autotune/lakefile-symlink-out",
    f"exit {rc}, the outside lakefile is not read" if rc == 0 and not leaked(so + se) else f"exit {rc}, leaked {leaked(so + se)}")
# controls: honest layouts unchanged
pj = proj("honest", 'name = "p"\nsrcDir = "src"\ndefaultTargets = ["Hon"]\n[[lean_lib]]\nname = "Hon"\nglobs = ["Hon.*"]\n',
          {"src/Hon/A.lean": "@[to_additive]\ndef a : Nat := 1\n", "src/Hon/B.lean": "import Hon.A\ndef b : Nat := 2\n",
           "src/Real.lean": "def r : Nat := 3\n"})
os.symlink("../Real.lean", os.path.join(pj, "src", "Hon", "C.lean"))
rc, so, se = autotune(pj)
try:
    f = json.loads(so)["features"]
except ValueError:
    f = {}
row(rc == 0 and f.get("modules") == 3 and f.get("translate_examples") == ["Hon.A"] and f.get("toolchain") == "leanprover/lean4:v4.36.0",
    "control/honest-srcdir", f"exit {rc}, modules {f.get('modules')}, translate {f.get('translate_examples')}, toolchain {f.get('toolchain')!r}")

# e2e: bin/fastverify --preset sound-auto --preflight-only (reproduction step 4)
chal = os.path.join(w, "allowed", "chal")
write(f"{chal}/Chal.lean", "theorem goal : True := trivial\n")
write(f"{chal}/lakefile.toml", 'name = "chal"\n[[lean_lib]]\nname = "Chal"\n')
write(f"{chal}/lean-toolchain", "leanprover/lean4:v4.36.0\n")
write(f"{chal}/comparator.json", json.dumps({"challenge_module": "Chal", "solution_module": "Sol", "theorem_names": ["goal"],
      "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}))
pj = proj("e2e", f'name = "sol"\nsrcDir = "{out}"\n' + lib, {"Sol.lean": "theorem goal : True := trivial\n"})
o = os.path.join(w, "fv_out")
try:
    p = subprocess.run([os.path.join(fv, "bin", "fastverify"), "--preset", "sound-auto", "--preflight-only", pj, chal, o],
                       capture_output=True, text=True, timeout=600)
    r = json.load(open(os.path.join(o, "result.json")))
    at = json.dumps(r.get("autotune"))
except (OSError, ValueError, subprocess.TimeoutExpired) as e:
    at = f"no result.json ({e})"
row(not leaked(at) and "no result.json" not in at, "e2e/fastverify-preflight",
    "result.json autotune holds nothing from outside" if not leaked(at) else f"leaked {leaked(at)}: {at[:200]}")
# e2e: MCP fv_doctor's host doctor on the project, incl. the FIFO variant (must not hang)
for name, key in (("mcp-doctor", "abs-srcdir-globs"), ("mcp-doctor-fifo", "abs-srcdir-fifo")):
    code = ("import json,sys,time; sys.path.insert(0, sys.argv[1] + '/tools/mcp'); import mcp_server as m; t=time.time(); "
            "r = m.run_host_doctor(sys.argv[1], sys.argv[2]); print(json.dumps(r, default=str)); print('SECONDS', time.time()-t)")
    try:
        p = subprocess.run(["python3", "-I", "-c", code, fv, cases[key]], capture_output=True, text=True, timeout=60)
        txt = p.stdout
        secs = float(txt.rsplit("SECONDS", 1)[1]) if "SECONDS" in txt else 99
    except subprocess.TimeoutExpired:
        txt, secs = "timeout", 99
    row(not leaked(txt) and secs < 10, "e2e/" + name, f"no outside names, {secs:.1f} s" if not leaked(txt) and secs < 10
        else f"leaked {leaked(txt)}, {secs:.1f} s")
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
