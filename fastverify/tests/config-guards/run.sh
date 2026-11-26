#!/bin/bash
# tests/config-guards/run.sh [WORKBASE] -- regression test of the package-configuration guards:
# no Lean-language package configuration may reach Lake's planner, whatever its name, and incr-build.py's host-side writes
# can never follow a symlink planted in WORK/log.
#   F1-buildsh  build.sh --plan-only (no --require-modules): a path dependency whose manifest configFile is ".toml" (Lean's
#               FilePath.extension is none for it, so Lake loads dep/.toml.lean) -> DECLINED before planning, no marker
#   F2-buildsh  no root lake-manifest.json, the root requires a path dependency whose OWN manifest names a "build.lean"
#               config for its dependency -> DECLINED, no marker
#   F3-incr     incr-build.py on a base build, new sources = the F1-buildsh layout whose .toml.lean, if it ran in the planner, would
#               write markers into WORK/log and plant symlinks there (lean_path.txt, plan-incr.jsonl, sched.out) aimed
#               outside every sandbox -> exit 2, no marker, no outside file
#   F4-incr     incr-build.py, new sources with lake-manifest.json {"packages": 5} -> exit 2 (a refusal), never 1
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/config-guards.XXXXXX") || exit 2
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
python3 -I -B - "$FV" "$W" <<'PY'
import json, os, shutil, subprocess, sys
fv, w = sys.argv[1:3]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
def write(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, "w").write(s)
tcid = "leanprover/lean4:v4.33.1"
tc = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"][tcid]["prefix"]
OUTSIDE = os.path.join(w, "outside")
os.makedirs(OUTSIDE)
# Lean config code that, if it ever runs in the planner, finds the plan path in /proc/self/cmdline and writes a marker
# next to it, and replaces the host-side output names there with symlinks to files outside every sandbox
EVIL = ("import Lake\nopen Lake DSL\npackage dep\n#eval show IO Unit from do\n"
        "  let cmd \u2190 IO.FS.readFile \"/proc/self/cmdline\"\n"
        "  for a in cmd.splitOn \"\\x00\" do\n    if a.endsWith \"plan.jsonl\" then\n"
        "      let d := (System.FilePath.mk a).parent.getD \".\"\n"
        "      for t in [d, d / \"..\"] do\n"
        "        try IO.FS.writeFile (t / \"F1-ESCAPE-MARKER\") \"x\" catch _ => pure ()\n"
        f"        for n in [\"lean_path.txt\", \"plan-incr.jsonl\", \"sched.out\"] do\n"
        "          try\n            discard <| IO.Process.output {cmd := \"ln\", args := #[\"-sfn\", "
        f"\"{OUTSIDE}/OUTSIDE-\" ++ n, (t / n).toString]}}\n"
        "          catch _ => pure ()\n")
def proj(d, files):
    write(f"{d}/lean-toolchain", tcid + "\n")
    for k, v in files.items():
        write(f"{d}/{k}", v)
    return d
MAIN = "theorem qaTheorem : 2 + 2 = 4 := rfl\n"
def manifest(entries):
    return json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "name": "Example", "lakeDir": ".lake", "packages": entries})
def pathentry(name, d, cf):
    return {"type": "path", "scope": "", "name": name, "manifestFile": "lake-manifest.json", "inherited": False, "dir": d, "configFile": cf}
REQ = 'name = "Example"\ndefaultTargets = ["Main"]\n[[require]]\nname = "dep"\npath = "dep"\n[[lean_lib]]\nname = "Main"\n'
def markers(root):
    return [os.path.join(dp, f) for dp, dn, fn in os.walk(root) for f in fn if f == "F1-ESCAPE-MARKER"]
def outside():
    return sorted(os.listdir(OUTSIDE))
def buildsh(pj, lg, *extra):
    p = subprocess.run(["bash", os.path.join(fv, "build", "build.sh"), pj, "/nonexistent", tc, "--log", lg, "--threads", "4"] + list(extra),
                       capture_output=True, text=True, timeout=1800)
    try:
        return json.loads(p.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        return {"status": None, "detail": (p.stdout + p.stderr)[-200:]}
# F1
f1 = proj(os.path.join(w, "F1"), {"lakefile.toml": REQ, "Main.lean": MAIN, "lake-manifest.json": manifest([pathentry("dep", "dep", ".toml")]),
                                  "dep/.toml.lean": EVIL, "dep/lean-toolchain": tcid + "\n"})
st = buildsh(f1, os.path.join(w, "F1-log"), "--plan-only")
row(st.get("status") == "DECLINED" and ".toml" in str(st.get("detail")) and not markers(w) and not outside(), "F1-buildsh-config-dot-toml",
    f"status {st.get('status')}, markers {markers(w)[:2]}, outside {outside()}: {str(st.get('detail'))[:140]}")
# F2
f2 = proj(os.path.join(w, "F2"), {"lakefile.toml": REQ, "Main.lean": MAIN, "dep/lean-toolchain": tcid + "\n",
                                  "dep/lakefile.toml": 'name = "dep"\n[[require]]\nname = "dep2"\npath = "sub"\n',
                                  "dep/lake-manifest.json": manifest([pathentry("dep2", "sub", "build.lean")]),
                                  "dep/sub/build.lean": EVIL.replace("package dep", "package dep2"), "dep/sub/lean-toolchain": tcid + "\n"})
st = buildsh(f2, os.path.join(w, "F2-log"), "--plan-only")
row(st.get("status") == "DECLINED" and not markers(w) and not outside(), "F2-buildsh-no-root-manifest",
    f"status {st.get('status')}, markers {markers(w)[:2]}, outside {outside()}: {str(st.get('detail'))[:140]}")
# base build for incr-build
b = proj(os.path.join(w, "base"), {"lakefile.toml": 'name = "Example"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n', "Main.lean": MAIN})
blog = os.path.join(w, "base-log")
st = buildsh(b, blog)
row(st.get("status") == "BUILT", "F3F4-setup-base-build", f"status {st.get('status')}: {str(st.get('detail'))[:120]}")
def incr(src, wk):
    p = subprocess.run(["/usr/bin/python3", "-I", os.path.join(fv, "tools", "incr", "incr-build.py"), "--base", b, "--base-plan",
                        os.path.join(blog, "plan.jsonl"), "--src", src, "--work", wk, "--packages", "/nonexistent", "--tc", tc,
                        "--threads", "4"], capture_output=True, text=True, timeout=1800)
    try:
        d = json.loads(p.stdout.strip().splitlines()[-1]).get("detail")
    except (ValueError, IndexError):
        d = (p.stdout + p.stderr)[-200:]
    return p.returncode, d
# F3
f3 = os.path.join(w, "F3src")
shutil.copytree(f1, f3)
rc, d = incr(f3, os.path.join(w, "F3work"))
row(rc == 2 and not markers(w) and not outside(), "F3-incr-planner-writes",
    f"exit {rc}, markers {markers(w)[:2]}, outside {outside()}: {str(d)[:140]}")
# F4
f4 = os.path.join(w, "F4src")
shutil.copytree(b, f4, ignore=shutil.ignore_patterns(".lake"))
write(os.path.join(f4, "lake-manifest.json"), json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "name": "Example", "packages": 5}))
rc, d = incr(f4, os.path.join(w, "F4work"))
row(rc == 2, "F4-incr-malformed-manifest", f"exit {rc} (want 2): {str(d)[:140]}")
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
