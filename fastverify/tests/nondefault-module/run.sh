#!/bin/bash
# tests/nondefault-module/run.sh [WORKBASE] -- regression test: the official build builds the configured module,
# not the project's default targets (HIGH false reject; MEDIUM for the challenge side): the official build B0
# (build/official-build.sh) ran a bare `lake build` = the project's DEFAULT targets,
# while the official comparator builds the configured module (Lake.Check: safeLakeBuild of the solution / challenge
# module). A valid solution module outside the default targets was then never built and the run ended REJECTED (export:
# module not found); a source-only challenge whose challenge module is outside its default targets failed the same way.
# Fix: official-build.sh --targets MOD (lake build +MOD), passed by bin/fastverify for the solution and
# the challenge module; build.sh --require-modules MOD declines to the official build when Lake's plan lacks the module.
# Rows (official 4.33.1; the project's default target is an unrelated library; the challenge's default target is unrelated
# too): source-challenge/* (source-only challenge: --preset reference, sound-auto, sound, --build B1 --check C0) and
# given-challenge/* (its official export given: the B0 solution path alone, --preset reference and sound-auto) must be
# ACCEPTED; control: a sorry proof is REJECTED.
# broken-default/* (default targets [Main, Broken], Broken broken, not imported) -> ACCEPTED in every
# preset; lib-extra-broken/* (lean_lib Main roots [Main, Extra], Extra broken: the official `lake build Main` fails) ->
# REJECTED in every preset.
# P4 (an imported module that fails under the build transforms and succeeds on the exact
# retry + a broken unimported default target) -> ACCEPTED in sound-auto / sound / reference; P1 (non-default lean_lib with
# globs and a broken glob member), P2a (single-quoted roots), P2b (lean_exe header with a quoted comment), P2c (multi-line
# roots array with a comment), P3a (defaultFacets = []), P3b ([[input_file]] named Main) -> REJECTED like the official
# `lake build Main`, in reference / sound-auto / sound.
# N4*: Lake resolves the bare name across the whole workspace (root first, then the dependencies).
# N4a: a local `[[require]] path` dependency declares lean_lib Main (roots [DepMain]) -> the official `lake build Main`
# builds the dependency's library, never the root's Main -> reference REJECTED (or no verdict, see P3a) and
# sound-auto / sound the same (earlier versions took the fast path and said ACCEPTED). N4b: the path dependency is a
# package named Main -> the fast build hands off; sound-auto / sound must give the verdict of reference (Lake 4.33.1's
# official `lake build Main` was observed to build the root's Main here: ACCEPTED). N4c (control): a harmless path
# dependency -> the fast build hands off, the official `lake build Main` builds the root's Main -> ACCEPTED everywhere.
# NONDEFAULT_ONLY=REGEX runs only the rows whose name matches.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/nondefault-module.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
python3 -I -B - "$FV" "$W" <<'PY'
import json, os, subprocess, sys
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
chal = os.path.join(w, "chal")
write(f"{chal}/lean-toolchain", tcid + "\n")
write(f"{chal}/lakefile.toml", 'name = "Chal"\ndefaultTargets = ["Other"]\n[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Other"\n')
write(f"{chal}/Challenge.lean", "theorem qaTheorem : 2 + 2 = 4 := sorry\n")
write(f"{chal}/Other.lean", "theorem otherOk : True := True.intro\n")
write(f"{chal}/comparator.json", json.dumps({"challenge_module": "Challenge", "solution_module": "Main",
      "theorem_names": ["qaTheorem"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}))
def proj(name, proof):
    pj = os.path.join(w, name)
    write(f"{pj}/lean-toolchain", tcid + "\n")
    write(f"{pj}/lakefile.toml", 'name = "Main"\ndefaultTargets = ["Support"]\n[[lean_lib]]\nname = "Main"\n[[lean_lib]]\nname = "Support"\n')
    write(f"{pj}/Main.lean", f"theorem qaTheorem : 2 + 2 = 4 := {proof}\n")
    write(f"{pj}/Support.lean", "theorem auxOk : True := True.intro\n")
    return pj
good, bad = proj("good", "rfl"), proj("bad", "sorry")
# the same challenge with its OFFICIAL export given (lake build of the challenge module + the official lean4export of
# this release, made here from the fixture): isolates the B0 solution path from the source-only challenge path
comp = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"][tcid]
tc, l4e = comp["prefix"], comp["official_lean4export"]["path"]
chal2 = os.path.join(w, "chal-given")
subprocess.run(["cp", "-a", chal, chal2], check=True)
env = {"PATH": f"{tc}/bin:/usr/bin:/bin", "HOME": w, "LANG": "C.UTF-8"}
subprocess.run([f"{tc}/bin/lake", "build", "Challenge"], cwd=chal2, env=env, capture_output=True)
builtins = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land",
            "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
            "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam", "Quot", "Quot.mk",
            "Quot.lift", "Quot.ind", "propext", "Quot.sound", "Classical.choice", "qaTheorem"]
with open(os.path.join(chal2, "challenge.export"), "w") as f:
    subprocess.run([l4e, "Challenge", "--"] + builtins, cwd=chal2, stdout=f, stderr=subprocess.DEVNULL,
                   env=dict(env, LEAN_PATH=f"{chal2}/.lake/build/lib/lean:{tc}/lib/lean"))
subprocess.run(["rm", "-rf", os.path.join(chal2, ".lake")])
import hashlib
pin = ["--challenge-sha256", hashlib.sha256(open(os.path.join(chal2, "challenge.export"), "rb").read()).hexdigest(),
       # a given challenge pin goes with the comparator config pin
       "--comparator-sha256", hashlib.sha256(open(os.path.join(chal2, "comparator.json"), "rb").read()).hexdigest()]
# a sound run on a BUILT challenge needs the comparator pin too
spin = ["--comparator-sha256", hashlib.sha256(open(os.path.join(chal, "comparator.json"), "rb").read()).hexdigest()]
runs = [("source-challenge/reference", ["--preset", "reference"] + spin, good, chal, "ACCEPTED"),
        ("source-challenge/sound-auto", ["--preset", "sound-auto"] + spin, good, chal, "ACCEPTED"),
        ("source-challenge/sound", ["--preset", "sound"] + spin, good, chal, "ACCEPTED"),
        ("source-challenge/b1-c0", ["--build", "B1", "--check", "C0"] + spin, good, chal, "ACCEPTED"),
        ("given-challenge/reference-b0", ["--preset", "reference"] + pin, good, chal2, "ACCEPTED"),
        ("given-challenge/sound-auto-b0", ["--preset", "sound-auto"] + pin, good, chal2, "ACCEPTED"),
        ("control/sorry-rejected", ["--preset", "reference"] + pin, bad, chal2, "REJECTED")]
# default targets [Main, Broken]: Broken does not compile and Main does not import it -> the official
# `lake build Main` builds lean_lib Main only -> ACCEPTED (the fast builds' failure outside Main's closure is no verdict)
bd = os.path.join(w, "broken-default")
write(f"{bd}/lean-toolchain", tcid + "\n")
write(f"{bd}/lakefile.toml", 'name = "Main"\ndefaultTargets = ["Main", "Broken"]\n[[lean_lib]]\nname = "Main"\n'
      '[[lean_lib]]\nname = "Broken"\n')
write(f"{bd}/Main.lean", "theorem qaTheorem : 2 + 2 = 4 := rfl\n")
write(f"{bd}/Broken.lean", "theorem broken : 1 = 2 := rfl\n")
# lean_lib Main with roots [Main, Extra], Extra broken: the official `lake build Main` builds the whole
# library and fails -> REJECTED, whatever the preset (the verdict follows the official flow)
le = os.path.join(w, "lib-extra-broken")
write(f"{le}/lean-toolchain", tcid + "\n")
write(f"{le}/lakefile.toml", 'name = "Main"\n[[lean_lib]]\nname = "Main"\nroots = ["Main", "Extra"]\n')
write(f"{le}/Main.lean", "theorem qaTheorem : 2 + 2 = 4 := rfl\n")
write(f"{le}/Extra.lean", "theorem extra : 1 = 2 := rfl\n")
for pr in ("sound", "reference", "sound-auto"):
    runs.append((f"broken-default/{pr}", ["--preset", pr] + pin, bd, chal2, "ACCEPTED"))
runs.append(("broken-default/b1-c0", ["--build", "B1", "--check", "C0"] + pin, bd, chal2, "ACCEPTED"))
for pr in ("sound", "reference", "sound-auto"):
    runs.append((f"lib-extra-broken/{pr}", ["--preset", pr] + pin, le, chal2, "REJECTED"))
# target shapes the fast build does not reproduce must follow the official `lake build Main`
# (they hand off to it); the `decide +kernel` proof makes sound-auto choose its B3 + closure path
def gproj(name, lakefile, files):
    d = os.path.join(w, name)
    write(f"{d}/lean-toolchain", tcid + "\n")
    write(f"{d}/lakefile.toml", lakefile)
    for k, v in files.items():
        write(f"{d}/{k}", v)
    return d
KP = "theorem qaTheorem : 2 + 2 = 4 := by decide +kernel\n"
BAD = "theorem bad : 1 = 2 := rfl\n"
p4 = gproj("P4", 'name = "Main"\ndefaultTargets = ["Main", "Broken"]\n[[lean_lib]]\nname = "Main"\nglobs = ["Main.*"]\n'
           '[[lean_lib]]\nname = "Broken"\n',
           {"Main.lean": "import Main.A\n" + KP, "Broken.lean": BAD,
            "Main/A.lean": "import Lean\n#eval show Lean.Elab.Command.CommandElabM Unit from do\n"
                           "  if (\u2190 Lean.getOptions).getBool `linter.all true == false then\n"
                           "    throwError \"linter.all disabled\"\ndef aVal : Nat := 1\n"})
p1 = gproj("P1", 'name = "Pkg"\ndefaultTargets = ["Quick"]\n[[lean_lib]]\nname = "Quick"\nroots = ["Quick"]\n'
           '[[lean_lib]]\nname = "Main"\nglobs = ["Main.*"]\n',
           {"Quick.lean": "import Main\n", "Main.lean": KP, "Main/Broken.lean": BAD})
p2a = gproj("P2a", "name = \"Main\"\ndefaultTargets = [\"Main\"]\n[[lean_lib]]\nname = \"Main\"\nroots = ['Main', 'Extra']\n",
            {"Main.lean": KP, "Extra.lean": BAD})
p2b = gproj("P2b", 'name = "p"\ndefaultTargets = ["Main"]\n[[lean_exe]] # "executable"\nname = "Main"\n', {"Main.lean": KP})
p2c = gproj("P2c", 'name = "Main"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\nroots = [ # see [1]\n  "Main",\n  "Extra"\n]\n',
            {"Main.lean": KP, "Extra.lean": BAD})
p3a = gproj("P3a", 'name = "Main"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\ndefaultFacets = []\n', {"Main.lean": KP})
p3b = gproj("P3b", 'name = "p"\ndefaultTargets = ["Lib"]\n[[input_file]]\nname = "Main"\npath = "Main.lean"\n'
            '[[lean_lib]]\nname = "Lib"\nroots = ["Main"]\n', {"Main.lean": KP})
for pr in ("sound-auto", "sound", "reference"):
    runs.append((f"P4-retry-plus-broken-default/{pr}", ["--preset", pr] + pin, p4, chal2, "ACCEPTED"))
# P3a / P3b (and N4a below): the official `lake build Main` succeeds without building the root's Main, so the official
# export of Main fails: REJECTED in earlier packages, no verdict (ERROR: "the official exporter failed") in the current
# one -> reference must be REJECTED or ERROR, sound-auto / sound must give reference's verdict
NOMOD = ("REJECTED", "ERROR")
for nm, d in (("P1-nondefault-glob-broken", p1), ("P2a-single-quoted-roots", p2a), ("P2b-exe-header-comment", p2b),
              ("P2c-multiline-array-comment", p2c), ("P3a-empty-defaultFacets", p3a), ("P3b-input-file-shadow", p3b)):
    for pr in ("reference", "sound-auto", "sound"):
        want = "REJECTED" if not nm.startswith("P3") else NOMOD if pr == "reference" else "=reference"
        runs.append((f"{nm}/{pr}", ["--preset", pr] + pin, d, chal2, want))
# N4*: path dependencies whose targets / package name claim the bare name Main
def dproj(name, rootreq, deplake, depfiles):
    d = gproj(name, 'name = "Pkg"\ndefaultTargets = ["Lib"]\n[[require]]\n' + rootreq + '[[lean_lib]]\nname = "Lib"\nroots = ["Main"]\n',
              {"Main.lean": KP})
    for k, v in dict(depfiles, **{"lakefile.toml": deplake}).items():
        write(f"{d}/dep/{k}", v)
    return d
n4a = dproj("N4a", 'name = "dep"\npath = "dep"\n', 'name = "dep"\n[[lean_lib]]\nname = "Main"\nroots = ["DepMain"]\n',
            {"DepMain.lean": "theorem depOk : True := True.intro\n"})
n4b = dproj("N4b", 'name = "Main"\npath = "dep"\n', 'name = "Main"\n[[lean_lib]]\nname = "DepLib"\n',
            {"DepLib.lean": "theorem depOk : True := True.intro\n"})
n4c = dproj("N4c", 'name = "dep"\npath = "dep"\n', 'name = "dep"\n[[lean_lib]]\nname = "DepLib"\n',
            {"DepLib.lean": "theorem depOk : True := True.intro\n"})
for nm, d, ref in (("N4a-path-dep-lean_lib-Main", n4a, NOMOD), ("N4b-path-dep-package-Main", n4b, ("ACCEPTED", "REJECTED")),
                   ("N4c-path-dep-harmless", n4c, ("ACCEPTED",))):
    for pr in ("reference", "sound-auto", "sound"):
        runs.append((f"{nm}/{pr}", ["--preset", pr] + pin, d, chal2, ref if pr == "reference" else "=reference"))
# further project layouts. Each row's verdict must equal the official
# flow's (reference); `check` asserts more on result.json / the logs
R = {}
R["separate-roots"] = gproj("R1", 'name = "Example"\ndefaultTargets = ["Main", "Library"]\n[[lean_lib]]\nname = "Main"\n'
                               'roots = ["Support"]\n[[lean_lib]]\nname = "Library"\nroots = ["Main"]\n',
                               {"Main.lean": KP, "Support.lean": "def version : Nat := 1\n"})
R["quoted-library"] = gproj("R2", 'name = "Example"\ndefaultTargets = ["Tools"]\n[[lean_lib]]\nname = "Tools"\n[[lean_lib]]\n'
                               'name = "\u00abMain\u00bb"\nroots = ["Main", "Draft"]\n',
                               {"Main.lean": KP, "Draft.lean": "example : 1 = 2 := rfl\n",
                                "Tools.lean": "import Main\nexample : 2 + 2 = 4 := by decide +kernel\n"})
EXE = ('name = "Example"\ndefaultTargets = ["{d}"]\n[[lean_lib]]\nname = "Library"\nroots = ["Main"]\nsrcDir = "lib"\n'
       '[[lean_exe]]\nname = "demo"\nroot = "Main"\nsrcDir = "app"\n')
R["exe-provider"] = gproj("R3", EXE.format(d="Library"),
                             {"app/Main.lean": "theorem qaTheorem : 2 + 2 = 4 := rfl\ndef main : IO Unit := pure ()\n",
                              "lib/Main.lean": "example : 2 + 2 = 4 := by decide +kernel\ndef libraryVersion : Nat := 1\n"})
R["confirm-exe"] = gproj("R4", EXE.format(d="Tools") + '[[lean_lib]]\nname = "Tools"\n',
                            {"app/Main.lean": "theorem qaTheorem : 2 + 2 = 4 := rfl\ndef main : IO Unit := pure ()\n",
                             "lib/Main.lean": "theorem qaTheorem : True := trivial\n",
                             "Tools.lean": "example : 2 + 2 = 4 := by decide +kernel\nexample : 1 = 2 := rfl\n"})
R["unicode-module"] = gproj("R5", 'name = "Exemple"\ndefaultTargets = ["R\u00e9sultat"]\n[[lean_lib]]\nname = "R\u00e9sultat"\n',
                               {"R\u00e9sultat.lean": KP})
R["retry-outside-closure"] = gproj("R6", 'name = "Main"\ndefaultTargets = ["Main", "Broken"]\n[[lean_lib]]\nname = "Main"\n'
                                      '[[lean_lib]]\nname = "Broken"\n',
                                      {"Main.lean": "import Main.A\n" + KP, "Main/A.lean": open(os.path.join(p4, "Main/A.lean")).read(),
                                       "Broken.lean": "import Main\n" + BAD})
FACTS = "import Lean\n{imp}namespace Tickets\ninductive Issued : Nat \u2192 Prop where\n  | make (n : Nat) : Issued n\n" \
        "theorem issue (n : Nat) : Issued n := Issued.make n\nend Tickets\n"
R["suggestions-import"] = gproj("R7", 'name = "Example"\ndefaultTargets = ["Quick"]\n[[lean_lib]]\nname = "Quick"\n[[lean_lib]]\nname = "Main"\n',
                                   {"Main/Facts.lean": FACTS.format(imp="import Lean.LibrarySuggestions.Default\n"),
                                    "Main.lean": "import Main.Facts\nexample (n : Nat) : Tickets.Issued n := by grind +suggestions\n"
                                                 "theorem qaTheorem : 2 + 2 = 4 := rfl\n",
                                    "Quick.lean": "example : 1 = 1 := by decide +kernel\n"})
R["suggestions-multiline"] = gproj("R8", 'name = "Example"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Quick"\n[[lean_lib]]\nname = "Main"\n',
                                      {"Main/Facts.lean": FACTS.format(imp=""),
                                       "Main.lean": "import Main.Facts\nexample (n : Nat) : Tickets.Issued n := by grind (suggestions :=\n  true)\n" + KP,
                                       "Quick.lean": "example : 1 = 1 := by decide +kernel\n"})
# R9 (the confirm path): a valid proof of a DIFFERENT statement (CS rejects it, rightly) + a broken default target outside
# its closure: the --confirm-reject B1 (with --require-modules) declines on Broken, the confirmation falls back to the
# official `lake build Main` (B0), whose export CS rejects again -> REJECTED, like reference
R["confirm-b0-fallback"] = gproj("R9", 'name = "Main"\ndefaultTargets = ["Main", "Broken"]\n[[lean_lib]]\nname = "Main"\n'
                                    '[[lean_lib]]\nname = "Broken"\n',
                                    {"Main.lean": "theorem qaTheorem : 2 + 2 = 4 + 0 := by decide +kernel\n", "Broken.lean": BAD})
def chk_confirm_b0(out, r):
    c = r.get("confirm_reject") or {}
    b1, b = (c.get("build_b1") or {}), (c.get("build") or {})
    ok = b1.get("exit") == 2 and b.get("option") == "B0" and b.get("exit") == 0
    return ok, f"confirm: B1 exit {b1.get('exit')}, then {b.get('option')} exit {b.get('exit')}: {str(c.get('result'))[:80]}"
ucfg = os.path.join(w, "unicode-comparator.json")
cc = json.load(open(os.path.join(chal2, "comparator.json"))); cc["solution_module"] = "R\u00e9sultat"
write(ucfg, json.dumps(cc))
upin = pin[:2] + ["--comparator-config", ucfg, "--comparator-sha256", hashlib.sha256(open(ucfg, "rb").read()).hexdigest()]
def sched_events(out, sub):
    ev = []
    try:
        for ln in open(os.path.join(out, "log", sub, "sched.out"), errors="replace"):
            if ln.startswith("{"):
                try:
                    ev.append(json.loads(ln))
                except ValueError:
                    pass
    except OSError:
        pass
    return [(e.get("event"), e.get("module"), e.get("rc")) for e in ev if e.get("event") in ("module", "retry-exact")]
def chk_retry(out, r):   # the exact retry really ran: Main.A failed, was retried exactly and succeeded; only Broken failed
    ev = sched_events(out, "build-fast")
    a = [x for x in ev if x[1] == "Main.A"]
    det = " ".join(str((at.get("stage") or {}).get("detail")) for at in (r.get("build") or {}).get("attempts") or [])
    ok = a[:3] == [("module", "Main.A", 1), ("retry-exact", "Main.A", None), ("module", "Main.A", 0)] and \
        "outside the import closure of Main failed (Broken)" in det
    return ok, f"Main.A events {a[:3]}; decline: {det[:120]}"
def chk_nopremoff(out, r):   # autotune saw the library suggestions and dropped premise-off
    d = ((r.get("autotune") or {}).get("dropped") or {})
    return "premise-off" in d, f"autotune dropped premise-off: {str(d.get('premise-off'))[:80]}"
CHECKS = {}
for nm, pr, opts, ref in (("separate-roots", "reference", [], NOMOD), ("separate-roots", "sound-auto", [], None),
                          ("separate-roots", "sound", [], None), ("separate-roots", "b1-c0", ["--build", "B1", "--check", "C0"], None),
                          ("quoted-library", "reference", [], ("REJECTED",)), ("quoted-library", "sound-auto", [], None),
                          ("quoted-library", "sound", [], None),
                          ("exe-provider", "reference", [], ("ACCEPTED",)), ("exe-provider", "sound-auto", [], None),
                          ("exe-provider", "sound", [], None),
                          ("confirm-exe", "reference", [], ("ACCEPTED",)),
                          ("confirm-exe", "confirm", ["--preset", "sound-auto", "--confirm-reject"], None),
                          ("unicode-module", "reference", [], ("ACCEPTED",)), ("unicode-module", "sound-auto", [], None),
                          ("retry-outside-closure", "sound", ["--preset", "sound", "--unsafe", "linter-off,retries"], ("ACCEPTED",)),
                          ("suggestions-import", "sound-auto", [], ("ACCEPTED",)),
                          ("suggestions-multiline", "sound-auto", [], ("ACCEPTED",)),
                          ("confirm-b0-fallback", "reference", [], ("REJECTED",)),
                          ("confirm-b0-fallback", "confirm", ["--preset", "sound-auto", "--confirm-reject"], None)):
    o = (opts or ["--preset", pr]) + (upin if nm.startswith("R5") else pin)
    runs.append((f"{nm}/{pr}", o, R[nm], chal2, ref or "=reference"))
CHECKS["retry-outside-closure/sound"] = chk_retry
CHECKS["suggestions-import/sound-auto"] = chk_nopremoff
CHECKS["suggestions-multiline/sound-auto"] = chk_nopremoff
CHECKS["confirm-b0-fallback/confirm"] = chk_confirm_b0
# S1/S2 a U+2028 / U+0085 inside a TOML
# comment (Lake: one comment line; str.splitlines(): a phantom `[zzz]` table eats `roots`); S3 the same hiding an exe
# `root`; S4/S5 a project symlink Main -> Draft.lean (Lake resolves `lake build Main` as that PATH); G1 a configured
# module `Book.lean` that is also a source file; G2/G3 a scheduler exception from an unrelated default target's
# moreLeanArgs (no module event); G4/G5 «Final Result» / «Answer..Final» (one Lake argument each); G6 a checked-in
# manifest with a project-local path dependency; G7 library suggestions under a dot srcDir; C1 (4.36, an
# unimported broken default target). Every optimized row must give reference's verdict; references as the
# official runs gave.
ROOTS2 = 'name = "Example"\ndefaultTargets = ["Tools"]\n[[lean_lib]]\nname = "Tools"\n[[lean_lib]]\nname = "Main"\n# note{sep}[zzz]\nroots = ["Main", "Draft"]\n'
DRAFT = "example : 1 = 2 := rfl\n"
TOOLS = "import Main\nexample : 2 + 2 = 4 := by decide +kernel\n"
R["S1-u2028-roots"] = gproj("S1", ROOTS2.format(sep="\u2028"), {"Main.lean": KP, "Draft.lean": DRAFT, "Tools.lean": TOOLS})
R["S2-nel-roots"] = gproj("S2", ROOTS2.format(sep="\u0085"), {"Main.lean": KP, "Draft.lean": DRAFT, "Tools.lean": TOOLS})
R["S3-u2028-exe"] = gproj("S3", 'name = "Example"\ndefaultTargets = ["Lib"]\n[[lean_lib]]\nname = "Lib"\nsrcDir = "lib"\nroots = ["Main"]\n'
                          '[[lean_exe]]\nname = "demo"\n# x\u2028[zzz]\nroot = "Main"\nsrcDir = "app"\n',
                          {"app/Main.lean": KP + "def main : IO Unit := pure ()\n", "lib/Main.lean": "theorem other : 1 = 1 := rfl\n"})
R["S4-symlink-target"] = gproj("S4", 'name = "Example"\ndefaultTargets = ["Lib"]\n[[lean_lib]]\nname = "Lib"\nroots = ["Main", "Draft"]\n',
                               {"Main.lean": KP, "Draft.lean": DRAFT})
R["S5-symlink-b1"] = gproj("S5", 'name = "Example"\ndefaultTargets = ["Lib"]\n[[lean_lib]]\nname = "Lib"\nroots = ["Main"]\n'
                           '[[lean_lib]]\nname = "Extra"\nroots = ["Draft"]\n', {"Main.lean": KP, "Draft.lean": DRAFT})
for k in ("S4", "S5"):
    os.symlink("Draft.lean", os.path.join(w, k, "Main"))
R["G1-source-name"] = gproj("G1", 'name = "Exercises"\ndefaultTargets = ["Book.lean"]\n[[lean_lib]]\nname = "Book.lean"\n'
                            'roots = ["Book.lean", "Book", "Appendix"]\n',
                            {"Appendix.lean": DRAFT, "Book/lean.lean": KP, "Book.lean": "import Book.lean\n"})
R["G2-unrelated-stack"] = gproj("G2", 'name = "Examples"\ndefaultTargets = ["Main", "Bench"]\n[[lean_lib]]\nname = "Main"\n'
                                '[[lean_lib]]\nname = "Bench"\nmoreLeanArgs = ["--tstack=8M"]\n',
                                {"Main.lean": KP, "Bench.lean": "example : True := trivial\n"})
HFACTS = FACTS.format(imp="import Lean.LibrarySuggestions.Default\n")
HMAIN = "import Main.Facts\nexample (n : Nat) : Tickets.Issued n := by grind +suggestions\ntheorem qaTheorem : 2 + 2 = 4 := rfl\n"
R["G3-hidden-and-bench"] = gproj("G3", 'name = "Example"\ndefaultTargets = ["Quick", "Main", "Bench"]\n[[lean_lib]]\nname = "Quick"\n'
                                 '[[lean_lib]]\nname = "Main"\nsrcDir = ".proofs"\n[[lean_lib]]\nname = "Bench"\nmoreLeanArgs = ["--tstack=8M"]\n',
                                 {".proofs/Main/Facts.lean": HFACTS, ".proofs/Main.lean": HMAIN, "Bench.lean": "example : True := trivial\n",
                                  "Quick.lean": "example : 1 = 1 := by decide +kernel\n"})
R["G4-space-module"] = gproj("G4", 'name = "Exercises"\ndefaultTargets = ["\u00abFinal Result\u00bb"]\n[[lean_lib]]\nname = "\u00abFinal Result\u00bb"\n',
                             {"Final Result.lean": KP})
R["G5-dots-module"] = gproj("G5", 'name = "Exercises"\ndefaultTargets = ["\u00abAnswer..Final\u00bb"]\n[[lean_lib]]\nname = "\u00abAnswer..Final\u00bb"\n',
                            {"Answer..Final.lean": KP})
R["G6-local-locked"] = gproj("G6", 'name = "Example"\ndefaultTargets = ["Docs"]\n[[require]]\nname = "utilities"\npath = "vendor/utilities"\n'
                             '[[lean_lib]]\nname = "Docs"\n[[lean_lib]]\nname = "Solutions"\nroots = ["Main"]\n',
                             {"Docs.lean": "example : True := trivial\n", "Main.lean": KP,
                              "vendor/utilities/Utilities.lean": "def version := 1\n",
                              "vendor/utilities/lakefile.toml": 'name = "utilities"\n[[lean_lib]]\nname = "Utilities"\n',
                              "lake-manifest.json": json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [
                                  {"type": "path", "scope": "", "name": "utilities", "manifestFile": "lake-manifest.json",
                                   "inherited": False, "dir": "vendor/utilities", "configFile": "lakefile.toml"}],
                                  "name": "Example", "lakeDir": ".lake"})})
R["G7-hidden-suggestions"] = gproj("G7", 'name = "Example"\ndefaultTargets = ["Quick"]\n[[lean_lib]]\nname = "Quick"\n[[lean_lib]]\n'
                                   'name = "Main"\nsrcDir = ".proofs"\n',
                                   {".proofs/Main/Facts.lean": HFACTS, ".proofs/Main.lean": HMAIN,
                                    "Quick.lean": "example : 1 = 1 := by decide +kernel\n"})
def cfgpin(mod):   # the given challenge with another solution module (its own comparator config + pin)
    f = os.path.join(w, "cfg-" + hashlib.sha256(mod.encode()).hexdigest()[:8] + ".json")
    c = json.load(open(os.path.join(chal2, "comparator.json"))); c["solution_module"] = mod
    write(f, json.dumps(c))
    return pin[:2] + ["--comparator-config", f, "--comparator-sha256", hashlib.sha256(open(f, "rb").read()).hexdigest()]
# C1: a reproduction case, verbatim (4.36 project and source challenge)
tc36 = "leanprover/lean4:v4.36.0\n"
c436 = os.path.join(w, "chal-436")
write(f"{c436}/lean-toolchain", tc36)
write(f"{c436}/lakefile.toml", 'name = "Challenge"\ndefaultTargets = ["Challenge"]\n[[lean_lib]]\nname = "Challenge"\n')
write(f"{c436}/Challenge.lean", "@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := Nat.add_zero n\n")
write(f"{c436}/comparator.json", json.dumps({"challenge_module": "Challenge", "solution_module": "Main", "theorem_names": ["qaAddZero"],
      "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "external_kernels": {"nanoda": ["nanoda_bin"]}}))
R["unrelated-default"] = d36 = os.path.join(w, "C1")
write(f"{d36}/lean-toolchain", tc36)
write(f"{d36}/lakefile.toml", 'name = "Main"\ndefaultTargets = ["Main", "Scratch"]\n[[lean_lib]]\nname = "Main"\n[[lean_lib]]\nname = "Scratch"\n')
write(f"{d36}/Main.lean", "@[simp] theorem qaAddZero (n : Nat) : n + 0 = n := Nat.add_zero n\n")
write(f"{d36}/Scratch.lean", 'def unrelated : Nat := "pending"\n')
for nm, pr, opts, ref, ex in (("S1-u2028-roots", "reference", [], ("REJECTED",), None), ("S1-u2028-roots", "sound-auto", [], None, None),
                              ("S1-u2028-roots", "sound", [], None, None), ("S1-u2028-roots", "b1-c0", ["--build", "B1", "--check", "C0"], None, None),
                              ("S2-nel-roots", "reference", [], ("REJECTED",), None), ("S2-nel-roots", "sound-auto", [], None, None),
                              ("S3-u2028-exe", "reference", [], ("ACCEPTED",), None), ("S3-u2028-exe", "sound", [], None, None),
                              ("S4-symlink-target", "reference", [], ("REJECTED",), None), ("S4-symlink-target", "sound-auto", [], None, None),
                              ("S5-symlink-b1", "reference", [], ("REJECTED",), None), ("S5-symlink-b1", "sound-auto", [], None, None),
                              ("S5-symlink-b1", "sound", [], None, None), ("S5-symlink-b1", "b1-c0", ["--build", "B1", "--check", "C0"], None, None),
                              ("G1-source-name", "reference", [], ("ACCEPTED",), cfgpin("Book.lean")),
                              ("G1-source-name", "sound-auto", [], None, cfgpin("Book.lean")),
                              ("G1-source-name", "sound", [], None, cfgpin("Book.lean")),
                              ("G2-unrelated-stack", "reference", [], ("ACCEPTED",), None), ("G2-unrelated-stack", "sound", [], None, None),
                              ("G3-hidden-and-bench", "reference", [], ("ACCEPTED",), None), ("G3-hidden-and-bench", "sound-auto", [], None, None),
                              ("G4-space-module", "reference", [], ("ACCEPTED",), cfgpin("\u00abFinal Result\u00bb")),
                              ("G4-space-module", "sound-auto", [], None, cfgpin("\u00abFinal Result\u00bb")),
                              ("G5-dots-module", "reference", [], ("ACCEPTED",), cfgpin("\u00abAnswer..Final\u00bb")),
                              ("G5-dots-module", "sound-auto", [], None, cfgpin("\u00abAnswer..Final\u00bb")),
                              ("G6-local-locked", "reference", [], ("ACCEPTED",), None), ("G6-local-locked", "sound-auto", [], None, None),
                              ("G7-hidden-suggestions", "sound-auto", [], ("ACCEPTED",), None),
                              ("unrelated-default", "reference", [], ("ACCEPTED",), "C436PIN"),
                              ("unrelated-default", "sound-auto", [], None, "C436PIN")):
    if ex == "C436PIN":   # the built 4.36 challenge's comparator pin
        ex = ["--comparator-sha256", hashlib.sha256(open(os.path.join(c436, "comparator.json"), "rb").read()).hexdigest()]
    o = (opts or ["--preset", pr]) + (pin if ex is None else ex)
    runs.append((f"{nm}/{pr}", o, R[nm], c436 if nm.startswith("C1") else chal2, ref or "=reference"))
CHECKS["G7-hidden-suggestions/sound-auto"] = chk_nopremoff
# M1 the configured name `«Main»` (canonical `Main`, what the comparator passes to Lake) +
# a symlink Main -> Draft.lean: the comparator's `lake build Main` builds Draft and fails -> REJECTED everywhere (an
# earlier B0 built `«Main»` = module Main, ACCEPTED in every preset); M2 the configured name `Main Draft` (canonical
# [anonymous]): no preset may build {Main, Draft} and accept (an earlier sound-auto did) -> ERROR / REJECTED, = reference
R["M1-guillemet-name-symlink"] = gproj("M1", 'name = "Example"\ndefaultTargets = ["Lib"]\n[[lean_lib]]\nname = "Lib"\nroots = ["Main", "Draft"]\n',
                                       {"Main.lean": KP, "Draft.lean": DRAFT})
os.symlink("Draft.lean", os.path.join(w, "M1", "Main"))
R["M2-space-in-name"] = gproj("M2", 'name = "Example"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n[[lean_lib]]\nname = "Draft"\n',
                              {"Main.lean": KP, "Draft.lean": "theorem draftOk : True := True.intro\n"})
for nm, mod, ref in (("M1-guillemet-name-symlink", "\u00abMain\u00bb", ("REJECTED",)), ("M2-space-in-name", "Main Draft", ("ERROR", "REJECTED"))):
    for pr, opts in (("reference", []), ("sound-auto", []), ("sound", []), ("b1-c0", ["--build", "B1", "--check", "C0"])):
        runs.append((f"{nm}/{pr}", (opts or ["--preset", pr]) + cfgpin(mod), R[nm], chal2, ref if pr == "reference" else "=reference"))
# a TOML root with a project-local PATH dependency (a checked-in manifest locks it).
# W1 the dependency's lakefile.lean detects the planner (IO.appPath) and fails only under `lake`: official REJECTED, every
# preset must be too (earlier sound / sound-auto / B1+C0 ACCEPTED - Shape 1 skipped the require check); W2 a pure
# TOML path dependency imported by Main: ACCEPTED, and B3 must hand off at once (no failed B3 first); W3 the dependency's
# lakefile.lean looks for the planner's plan path in /proc/self/cmdline and writes a marker next to it and into
# ../src (the host-executed helpers): no marker may appear in the run's log dir
def pdep(name, deplake, depcfg, extra_dep, main):
    d = gproj(name, 'name = "Example"\ndefaultTargets = ["Main"]\n[[require]]\nname = "dep"\npath = "dep"\n[[lean_lib]]\nname = "Main"\n',
              dict({"Main.lean": main, "dep/lean-toolchain": tcid + "\n", "dep/" + depcfg: deplake,
                    "lake-manifest.json": json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "name": "Example",
                        "lakeDir": ".lake", "packages": [{"type": "path", "scope": "", "name": "dep", "manifestFile": "lake-manifest.json",
                        "inherited": False, "dir": "dep", "configFile": depcfg}]})}, **extra_dep))
    return d
R["W1-pathdep-lakefile-lean-detect"] = pdep("W1", "import Lake\nopen Lake DSL\npackage dep\n#eval show IO Unit from do\n"
    "  let app \u2190 IO.appPath\n  if app.fileName != some \"planner\" then\n    throw (IO.userError \"dep fails under official lake\")\n",
    "lakefile.lean", {}, KP)
R["W2-pathdep-toml-valid"] = pdep("W2", 'name = "dep"\n[[lean_lib]]\nname = "DepMod"\n', "lakefile.toml",
    {"dep/DepMod.lean": "namespace DepMod\ndef four : Nat := 4\nend DepMod\n"},
    "import DepMod\ntheorem qaTheorem : 2 + 2 = 4 := by have : DepMod.four = 4 := rfl; decide +kernel\n")
R["W3-pathdep-lakefile-lean-escape"] = pdep("W3", "import Lake\nopen Lake DSL\npackage dep\n#eval show IO Unit from do\n"
    "  let cmd \u2190 IO.FS.readFile \"/proc/self/cmdline\"\n"
    "  for a in cmd.splitOn \"\\x00\" do\n    if a.endsWith \"plan.jsonl\" then\n"
    "      let d := (System.FilePath.mk a).parent.getD \".\"\n"
    "      try IO.FS.writeFile (d / \"ESCAPE-MARKER\") \"x\" catch _ => pure ()\n"
    "      try IO.FS.writeFile (d / \"src\" / \"ESCAPE-MARKER\") \"x\" catch _ => pure ()\n"
    "      try IO.FS.writeFile (d / \"..\" / \"src\" / \"ESCAPE-MARKER\") \"x\" catch _ => pure ()\n",
    "lakefile.lean", {}, KP)
def chk_b3_handoff(out, r):
    at = (r.get("build") or {}).get("attempts") or []
    return bool(at) and at[0].get("option") == "B3" and at[0].get("exit") == 2, f"first attempt {[(a.get('option'), a.get('exit')) for a in at][:1]}"
def chk_no_marker(out, r):
    hits = [os.path.join(dp, f) for dp, dn, fn in os.walk(out) for f in fn if f == "ESCAPE-MARKER"]
    return not hits, f"markers: {hits[:3]}"
for nm, ref in (("W1-pathdep-lakefile-lean-detect", ("REJECTED", "ERROR")), ("W2-pathdep-toml-valid", ("ACCEPTED",)),
                ("W3-pathdep-lakefile-lean-escape", ("ACCEPTED", "REJECTED", "ERROR"))):
    for pr, opts in (("reference", []), ("sound-auto", []), ("sound", []), ("b1-c0", ["--build", "B1", "--check", "C0"])):
        runs.append((f"{nm}/{pr}", (opts or ["--preset", pr]) + pin, R[nm], chal2, ref if pr == "reference" else "=reference"))
CHECKS["W2-pathdep-toml-valid/sound-auto"] = chk_b3_handoff
for pr in ("sound-auto", "sound", "b1-c0"):
    CHECKS[f"W3-pathdep-lakefile-lean-escape/{pr}"] = chk_no_marker
# a path dependency whose manifest entry names a Lean config file with ANOTHER name (configFile = "build.lean";
# Lake picks the config language by extension alone). W4 (fastverify): the file fails only under `lake` -> every preset
# = reference (REJECTED). W5 (build.sh directly, no --require-modules, so no [[require]] check): the file writes a marker
# next to the plan path it finds in /proc/self/cmdline -> build.sh must decline BEFORE planning, and no marker may exist
DETECT = ("import Lake\nopen Lake DSL\npackage dep\n#eval show IO Unit from do\n  let app \u2190 IO.appPath\n"
          "  if app.fileName != some \"planner\" then\n    throw (IO.userError \"dep fails under official lake\")\n")
R["W4-pathdep-config-other-name"] = pdep("W4", DETECT, "build.lean", {}, KP)
W5 = pdep("W5", R["W3-pathdep-lakefile-lean-escape"] and open(os.path.join(R["W3-pathdep-lakefile-lean-escape"], "dep", "lakefile.lean")).read(),
          "cfg/build.lean", {}, KP)
for pr, opts in (("reference", []), ("sound-auto", []), ("sound", []), ("b1-c0", ["--build", "B1", "--check", "C0"])):
    runs.append((f"W4-pathdep-config-other-name/{pr}", (opts or ["--preset", pr]) + pin, R["W4-pathdep-config-other-name"], chal2,
                 ("REJECTED", "ERROR") if pr == "reference" else "=reference"))
def w5_direct():
    lg = os.path.join(w, "W5-log")
    p = subprocess.run(["bash", os.path.join(fv, "build", "build.sh"), W5, "/nonexistent", tc, "--log", lg, "--plan-only",
                        "--threads", "4"], capture_output=True, text=True, timeout=1800)
    try:
        st = json.loads(p.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        st = {}
    hits = [os.path.join(dp, f) for dp, dn, fn in os.walk(lg) for f in fn if f == "ESCAPE-MARKER"]
    ok = st.get("status") == "DECLINED" and not hits and "build.lean" in str(st.get("detail"))
    row(ok, "W5-pathdep-config-other-name/build.sh-no-require-modules",
        f"status {st.get('status')}, markers {hits[:2]}: {str(st.get('detail'))[:140]}")
import re
only = os.environ.get("NONDEFAULT_ONLY")
if only:
    runs = [r for r in runs if re.search(only, r[0])]
seen = {}
import threading
from concurrent.futures import ThreadPoolExecutor
lock = threading.Lock()
def one(name, opts, pj, ch, want):
    if isinstance(want, str) and want.startswith("="):   # the verdict of another row of the same project
        want = seen.get(name.rsplit("/", 1)[0] + "/" + want[1:], "(reference row missing)")
    out = os.path.join(w, "out-" + name.replace("/", "-"))
    p = subprocess.run([os.path.join(fv, "bin", "fastverify"), pj, ch, out, "--threads", "4"] + opts,
                       capture_output=True, text=True, timeout=3600)
    try:
        r = json.load(open(os.path.join(out, "result.json")))
        v, why = r.get("verdict"), str(r.get("verdict_basis"))[:160]
    except (OSError, ValueError):
        v, why = None, (p.stdout + p.stderr)[-200:]
    ok = v in want if isinstance(want, tuple) else v == want
    if ok and name in CHECKS:
        ok, extra = CHECKS[name](out, r)
        why = extra + "; " + why
    with lock:
        seen[name] = v
        row(ok, name, f"verdict {v} (want {want}), exit {p.returncode}: {why}")
groups = {}
for rr in runs:
    groups.setdefault(rr[0].rsplit("/", 1)[0], []).append(rr)
def group(rows):
    for rr in rows:
        one(*rr)
with ThreadPoolExecutor(max_workers=int(os.environ.get("NONDEFAULT_JOBS", "6"))) as ex:
    list(ex.map(group, groups.values()))
if not only or re.search(only, "W5-pathdep-config-other-name"):
    w5_direct()
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY
