#!/bin/bash
# tests/manifest-binds/run.sh [WORKBASE] -- regression test: packagesDir of an untrusted manifest cannot inject sandbox binds (HIGH, lib/manifest.py
# + build/official-build.sh, build/build.sh, build/native.sh): packagesDir of the UNTRUSTED lake-manifest.json was checked
# only with isabs / '..', so a newline / TAB in it added binds.tsv lines: host-side `mkdir -p DST` outside the project and
# `bwrap --ro-bind SRC DST` of any host directory (incl. ones the sandbox hides) into the untrusted build.
# This test rebuilds the reproduction's marker scenario with a
# self-made git packages workspace: no network, no Mathlib).
# Rows:
#   manifest/*: lib/manifest.py refuses (exit 2, nothing printed) packagesDir with newline/TAB/other control characters,
#     absolute, '..', '.', empty components, non-string, a symlinked component leaving the project; control: a plain
#     manifest gives exactly 'SRC<TAB>PROJ/.lake/packages/dep'
#   official-build/*, fast-build/*: the injected manifest -> no host directory created outside the project, no injected
#     bind visible to the build (the marker of the injected source is not printed), no verdict (exit 2)
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/manifest-binds.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
python3 -I -B - "$FV" "$W" <<'PY'
import json, os, shutil, subprocess, sys
sys.dont_write_bytecode = True
fv, w = sys.argv[1:3]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
tc = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
genv = {"PATH": "/usr/bin:/bin", "HOME": w, "GIT_CONFIG_NOSYSTEM": "1", "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
ws = os.path.join(w, "ws"); dep = os.path.join(ws, ".lake", "packages", "dep"); os.makedirs(dep)
open(os.path.join(dep, "lakefile.toml"), "w").write('name = "dep"\n')
for c in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "x"]):
    subprocess.run(["git"] + c, cwd=dep, env=genv, check=True, capture_output=True)
rev = subprocess.run(["git", "rev-parse", "HEAD"], cwd=dep, env=genv, capture_output=True, text=True).stdout.strip()
ent = {"type": "git", "name": "dep", "url": "https://example.invalid/dep", "rev": rev, "inputRev": "main", "subDir": None,
       "scope": "", "manifestFile": "lake-manifest.json", "configFile": "lakefile.toml", "inherited": False}
json.dump({"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [ent], "name": "ws", "lakeDir": ".lake"},
          open(os.path.join(ws, "lake-manifest.json"), "w"))
hidden = os.path.join(w, "hidden"); os.makedirs(hidden)
open(os.path.join(hidden, "marker.txt"), "w").write("HIDDEN_MARKER_Z03_15\n")
outside = os.path.join(w, "outside_mkdir")

def mkproj(name, pdir):
    pj = os.path.join(w, name); os.makedirs(pj)
    open(os.path.join(pj, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
    open(os.path.join(pj, "lakefile.toml"), "w").write('name = "p"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n')
    open(os.path.join(pj, "Main.lean"), "w").write(
        f'#eval do\n  let s ← IO.FS.readFile "{outside}/inj/marker.txt"\n  IO.println s\ntheorem t : True := trivial\n')
    if pdir is not None:
        json.dump({"version": "1.1.0", "packagesDir": pdir, "packages": [ent], "name": "p", "lakeDir": ".lake"},
                  open(os.path.join(pj, "lake-manifest.json"), "w"))
    return pj

def manifest(pj):
    return subprocess.run(["python3", "-I", os.path.join(fv, "lib", "manifest.py"), pj, ws], capture_output=True, text=True)

inj = f"x\n{hidden}\t{outside}/inj\n{dep}\t{outside}/third"
cases = [("newline-tab", inj), ("tab-only", "a\tb"), ("carriage-return", "a\rb"), ("nul", "a\x00b"), ("del", "a\x7fb"),
         ("absolute", "/etc"), ("dotdot", "../x"), ("dot-component", "./.lake/packages"), ("empty-component", "a//b"),
         ("trailing-slash", "a/"), ("non-string", ["a"])]
for i, (name, pdir) in enumerate(cases):
    r = manifest(mkproj(f"m{i}", pdir))
    row(r.returncode == 2 and not r.stdout, "manifest/" + name, f"exit {r.returncode}, stdout {r.stdout[:120]!r}")
pj = mkproj("msym", "lnk/pk"); os.makedirs(os.path.join(w, "elsewhere")); os.symlink(os.path.join(w, "elsewhere"), os.path.join(pj, "lnk"))
r = manifest(pj)
row(r.returncode == 2 and not r.stdout, "manifest/symlink-component-leaving-project", f"exit {r.returncode}, stdout {r.stdout[:120]!r}")
pj = mkproj("mok", ".lake/packages")
r = manifest(pj)
want = f"{os.path.realpath(dep)}\t{os.path.realpath(pj)}/.lake/packages/dep\n"
row(r.returncode == 0 and r.stdout == want, "manifest/control-plain", f"exit {r.returncode}, stdout {r.stdout!r}")
row(not os.path.exists(outside), "manifest/no-side-effect", "nothing created outside")

for name, script, extra in (("official-build", "official-build.sh", []), ("fast-build", "build.sh", ["--preset", "B1"])):
    shutil.rmtree(outside, ignore_errors=True)
    pj = mkproj(name + "-proj", inj)
    log = os.path.join(w, name + "-log")
    p = subprocess.run([os.path.join(fv, "build", script), pj, ws, tc, "--log", log, "--threads", "2"] + extra,
                       capture_output=True, text=True, timeout=1200)
    text = p.stdout + p.stderr
    for r_, _, fs in os.walk(log):
        for fn in fs:
            try:
                text += open(os.path.join(r_, fn), errors="replace").read()[-100000:]
            except OSError:
                pass
    row(not os.path.exists(outside), name + "/no-host-mkdir-outside-project",
        "no directory created outside the project" if not os.path.exists(outside) else f"{outside} created on the host")
    row("HIDDEN_MARKER_Z03_15" not in text, name + "/no-injected-bind", "the injected source is not visible to the build"
        if "HIDDEN_MARKER_Z03_15" not in text else "the build read the injected bind's marker")
    row(p.returncode == 2, name + "/no-verdict", f"exit {p.returncode} (2 = could not run / declined)")
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
