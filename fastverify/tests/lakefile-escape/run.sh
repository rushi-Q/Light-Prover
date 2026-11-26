#!/bin/bash
# tests/lakefile-escape/run.sh [WORKBASE] -- regression test: an untrusted lakefile.toml cannot make the host act outside the project (HIGH; see also tests/autotune-confine):
# an UNTRUSTED lakefile.toml (no symlinks, no special flags) made the HOST act outside the project: (1) build/build.sh
# premise-off (default in --preset sound and sound-auto) read the root leanLibDir (Planner: buildDir / leanLibDir) from the
# plan and ran host-side `mkdir -p` + `cp FastverifyPremiseOff.olean` there; (2) lib/autotune.py walked / grepped srcDir
# outside the project. The inputs are those of the reproduction.
# Rows:
#   sound/no-outside-write, sound-auto/no-outside-write: bin/fastverify --preset sound / sound-auto with buildDir = a path
#     outside PROJECT and OUT, leanLibDir = "." -> that directory is never created (and no verdict ACCEPTED)
#   lean-path/*: build/official-build.sh with buildDir under /tmp (writable inside the sandbox) -> no LEAN_PATH outside the
#     project is handed to the export stage (exit 2, --lean-path-out not written)
#   autotune/*: lib/autotune.py with srcDir = an absolute outside dir / '../' traversal -> refused (exit 2), the outside
#     module name never printed
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/lakefile-escape.XXXXXX") || exit 2
TMPB=$(mktemp -u /tmp/fvz0317.XXXXXX)
trap 'rm -rf "$W" "$TMPB"' EXIT
python3 -I -B - "$FV" "$W" "$TMPB" <<'PY'
import json, os, shutil, subprocess, sys
sys.dont_write_bytecode = True
fv, w, tmpb = sys.argv[1:4]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
tc = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, "w").write(s)
chal = os.path.join(w, "Chal")
write(f"{chal}/lean-toolchain", "leanprover/lean4:v4.33.1\n")
write(f"{chal}/lakefile.toml", 'name = "EscapeChal"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n')
write(f"{chal}/Main.lean", "theorem ok : True := trivial\n")
write(f"{chal}/comparator.json", json.dumps({"challenge_module": "Main", "solution_module": "Main", "theorem_names": ["ok"],
      "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": False}))
for preset in ("sound", "sound-auto"):
    outside = os.path.join(w, "outside_write_" + preset)
    pj = os.path.join(w, "Proj-" + preset)
    write(f"{pj}/lean-toolchain", "leanprover/lean4:v4.33.1\n")
    write(f"{pj}/lakefile.toml", f'name = "EscapeChal"\nbuildDir = "{outside}"\nleanLibDir = "."\ndefaultTargets = ["Main"]\n'
          '[[lean_lib]]\nname = "Main"\n')
    write(f"{pj}/Main.lean", "theorem ok : True := by decide!\n")
    out = os.path.join(w, "Out-" + preset)
    p = subprocess.run([os.path.join(fv, "bin", "fastverify"), pj, chal, out, "--preset", preset, "--threads", "4"],
                       capture_output=True, text=True, timeout=3600)
    try:
        v = json.load(open(os.path.join(out, "result.json"))).get("verdict")
    except (OSError, ValueError):
        v = None
    row(not os.path.exists(outside), preset + "/no-outside-write",
        f"{outside} not created (verdict {v}, exit {p.returncode})" if not os.path.exists(outside)
        else f"{outside} created on the host: {os.listdir(outside)}")
    row(v != "ACCEPTED", preset + "/no-accept", f"verdict {v}")

# LEAN_PATH outside the project (buildDir under /tmp: writable tmpfs inside the sandbox, the HOST's /tmp outside)
pj = os.path.join(w, "ProjLP")
write(f"{pj}/lean-toolchain", "leanprover/lean4:v4.33.1\n")
write(f"{pj}/lakefile.toml", f'name = "lp"\nbuildDir = "{tmpb}"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n')
write(f"{pj}/Main.lean", "theorem ok : True := trivial\n")
lpo = os.path.join(w, "lp.out")
p = subprocess.run([os.path.join(fv, "build", "official-build.sh"), pj, "/nonexistent", tc, "--log", os.path.join(w, "lp-log"),
                    "--lean-path-out", lpo, "--threads", "2"], capture_output=True, text=True, timeout=1200)
lp = open(lpo).read() if os.path.exists(lpo) else ""
row(tmpb not in lp, "lean-path/no-outside-entry-handed-on",
    f"exit {p.returncode}, no LEAN_PATH outside the project written" if tmpb not in lp else f"LEAN_PATH handed on: {lp[:200]}")
row(p.returncode == 2, "lean-path/no-verdict", f"exit {p.returncode}")

# autotune (part 2): absolute / ../ srcDir
sec = os.path.join(w, "OutsideScan")
write(f"{sec}/ExternalSecret.lean", "@[to_additive]\ndef external_marker : Nat := 1\n")
for name, src in (("absolute", sec), ("dotdot", "../OutsideScan")):
    pj = os.path.join(w, "ProjAuto-" + name)
    write(f"{pj}/lean-toolchain", "leanprover/lean4:v4.33.1\n")
    write(f"{pj}/lakefile.toml", f'name = "AutoEscape"\nsrcDir = "{src}"\ndefaultTargets = ["ExternalSecret"]\n'
          '[[lean_lib]]\nname = "ExternalSecret"\n')
    p = subprocess.run(["python3", "-I", os.path.join(fv, "lib", "autotune.py"), pj, "--json"], capture_output=True, text=True,
                       timeout=120)
    row("ExternalSecret" not in p.stdout and p.returncode == 2, "autotune/srcdir-" + name,
        f"exit {p.returncode}, outside module not reported" if "ExternalSecret" not in p.stdout else "outside module reported: "
        + p.stdout[p.stdout.find("ExternalSecret") - 60:][:160])
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
