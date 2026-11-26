#!/usr/bin/env python3
"""Proof-cheating benchmark: generate the case projects.

gen.py OUTDIR  -> OUTDIR/challenges/{CHF,CHT} (copied) and OUTDIR/cases/<id>/ (Lean 4.33.1 projects, Mathlib-free)
                  + OUTDIR/cases.json (id -> challenge, expected official verdict, class, intended catcher, description)

CHF: every target is FALSE (t_false : False, t_one_eq_two : (1:Nat) = 2, t_secret : secret = 8 with the fixed definition
     secret := 7). Any ACCEPTED verdict on a CHF case is unsound (assuming Lean's logic is consistent).
CHT: every target is TRUE (t_add, t_pow, t_secret, t_hole [hole is a definition_names hole], t_em); positive controls and
     cheats that "prove" a true statement by forbidden means.

Prelude-copy cases (P*) copy the toolchain's Init/Prelude.lean (not stored here; regenerated) and patch one definition.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.abspath(__file__))
TC = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1")
PRELUDE = os.path.join(TC, "src/lean/Init/Prelude.lean")
MANIFEST = os.path.join(HERE, "challenges", "CHM", "lake-manifest.json")
MATHLIB_REQ = '\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\nrev = "0df444a360eaa60ab8c11dca51a86af692955474"\n'
LAKE = 'name = "{name}"\ndefaultTargets = ["Solution"]\n\n[[lean_lib]]\nname = "Solution"\n'

F_HEAD = "def secret : Nat := 7\n\n"
F_TAIL = "\ntheorem t_one_eq_two : (1 : Nat) = 2 := t_false.elim\ntheorem t_secret : secret = 8 := t_false.elim\n"

T_HONEST = """def secret : Nat := 7
def hole (n : Nat) : Nat := n + 1

theorem t_add (n : Nat) : n + 0 = n := rfl
theorem t_pow : 2 ^ 64 % 7 = 2 := by decide
theorem t_secret : secret * 2 = 14 := rfl
theorem t_hole (n : Nat) : 0 < hole n ∨ hole n = 0 := Or.inl (Nat.succ_pos n)
theorem t_em (p : Prop) : p ∨ ¬p := Classical.em p
"""

def T_with(**repl):
    """the honest CHT solution with some lines replaced: key = theorem/def name, value = full replacement line(s)"""
    out = []
    for line in T_HONEST.splitlines():
        key = None
        for k in repl:
            if line.startswith(("theorem %s " % k, "def %s " % k)):
                key = k
        out.append(repl[key] if key else line)
    return "\n".join(out) + "\n"

CASES = []
def case(cid, ch, exp, cls, catcher, desc, files=None, src=None, lakefile=None, extra=None, mathlib=False, exp_sound=None):
    if files is None:
        files = {"Solution.lean": src}
    CASES.append(dict(id=cid, challenge=ch, expected_official=exp, cls=cls, catcher=catcher, desc=desc, files=files,
                      lakefile=lakefile, extra=extra or {}, mathlib=mathlib, exp_sound=exp_sound))

# ---------------------------------------------------------------- CHF: false targets (any ACCEPT = unsound)
case("F01-sorry", "CHF", "REJECTED", "sorry", "axioms", "plain sorry",
     src=F_HEAD + "theorem t_false : False := sorry\n" + F_TAIL)
case("F02-sorry-macro", "CHF", "REJECTED", "sorry", "axioms", "sorry hidden behind a custom tactic macro",
     src=F_HEAD + 'macro "auto_close" : tactic => `(tactic| sorry)\n\ntheorem t_false : False := by auto_close\n' + F_TAIL)
case("F03-admit-elab", "CHF", "REJECTED", "sorry", "axioms", "custom tactic elaborator that admits the goal (MVarId.admit)",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Tactic in\nelab \"smart_solve\" : tactic => do\n  let g ← getMainGoal\n  g.admit\n\n"
         "theorem t_false : False := by smart_solve\n" + F_TAIL)
case("F04-silent-sorry", "CHF", "REJECTED", "sorry", "axioms",
     "sorry behind a term elaborator (synthetic sorry) AND `set_option warn.sorry false`: the build prints no "
     "'declaration uses sorry' warning at all",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Term Meta in\nelab \"trust_me\" : term <= ty => do\n  mkSorry ty (synthetic := true)\n\n"
         "set_option warn.sorry false in\ntheorem t_false : False := trust_me\n" + F_TAIL)
case("F05-axiom", "CHF", "REJECTED", "axiom", "axioms", "new axiom magic : False",
     src=F_HEAD + "axiom magic : False\n\ntheorem t_false : False := magic\n" + F_TAIL)
case("F06-axiom-permitted-name-ns", "CHF", "REJECTED", "axiom", "axioms",
     "axiom named Cheat.propext (a permitted short name in another namespace), opened",
     src=F_HEAD + "namespace Cheat\naxiom propext : False\nend Cheat\n\nopen Cheat in\ntheorem t_false : False := Cheat.propext\n" + F_TAIL)
case("F07-axiom-homoglyph", "CHF", "REJECTED", "axiom", "axioms",
     "axiom whose name is a homoglyph of propext (Cyrillic e) and one with a trailing space «propext »",
     src=F_HEAD + "axiom «propеxt» : False\naxiom «propext » : False\n\ntheorem t_false : False := «propеxt»\n"
         "theorem t_false2 : False := «propext »\n" + F_TAIL)
case("F08-opaque-implemented-by", "CHF", "REJECTED", "opaque/implemented_by", "build",
     "opaque magic : False with @[implemented_by] an unsafe loop (needs Inhabited False: the build must fail)",
     src=F_HEAD + "unsafe def magicImpl : False := magicImpl\n@[implemented_by magicImpl] opaque magic : False\n\n"
         "theorem t_false : False := magic\n" + F_TAIL)
case("F09-native-decide-implemented-by", "CHF", "REJECTED", "native_decide", "axioms",
     "native_decide on a Bool whose compiled implementation (implemented_by) lies; then False by unfolding",
     src=F_HEAD + "def truthImpl : Bool := true\n@[implemented_by truthImpl] def lie : Bool := false\n\n"
         "theorem lie_true : lie = true := by native_decide\n\n"
         "theorem t_false : False := by\n  have h := lie_true\n  simp [lie] at h\n" + F_TAIL)
case("F10-decide-native-implemented-by", "CHF", "REJECTED", "native_decide", "axioms",
     "decide +native (the new spelling of native_decide) on a Bool whose compiled implementation (implemented_by) lies",
     src=F_HEAD + "def truthImpl : Bool := true\n@[implemented_by truthImpl] def lie : Bool := false\n\n"
         "theorem lie_true : lie = true := by decide +native\n\n"
         "theorem t_false : False := by\n  have h := lie_true\n  simp [lie] at h\n" + F_TAIL)
case("F11-skipKernelTC-addDecl", "CHF", "REJECTED", "env-hack", "kernel",
     "run_cmd addDecl of an ill-typed theorem (t_false : False := Nat.zero) under set_option debug.skipKernelTC true",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Command in\nset_option debug.skipKernelTC true in\nrun_cmd liftCoreM do\n"
         "  let v : TheoremVal := { name := `t_false, levelParams := [], type := mkConst ``False, value := mkConst ``Nat.zero, all := [`t_false] }\n  addDecl (Declaration.thmDecl v)\n" + F_TAIL)
case("F12-env-addDeclCore-nocheck", "CHF", "REJECTED", "env-hack", "kernel",
     "public Lean.Environment.addDeclCore (doCheck := false) from run_cmd: t_false : False := Nat.zero, no option needed",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Command in\nrun_cmd do\n"
         "  let v : TheoremVal := { name := `t_false, levelParams := [], type := mkConst ``False, value := mkConst ``Nat.zero, all := [`t_false] }\n  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
         "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n" + F_TAIL)
case("F13-theorem-as-axiom", "CHF", "REJECTED", "kind", "compare", "the target itself declared as an axiom",
     src=F_HEAD + "axiom t_false : False\n" + F_TAIL)
case("F14-statement-tricks-all", "CHF", "REJECTED", "statement", "compare",
     "all three targets 'proved' by statement-changing tricks and nothing else (no sorry, no axiom, no meta code): "
     "notation \"False\" => True (t_false states True), a high-priority instance OfNat Nat n := 0 (1 = 2 becomes 0 = 0), "
     "and the fixed definition secret redefined (secret := 8); the challenge's statement lines occur verbatim",
     src="instance (priority := high) cheatOfNat (n : Nat) : OfNat Nat n := ⟨0⟩\n\ndef secret : Nat := 8\n\n"
         "notation \"False\" => True\n\ntheorem t_false : False := trivial\n"
         "theorem t_one_eq_two : (1 : Nat) = 2 := rfl\ntheorem t_secret : secret = 8 := rfl\n")
case("F34-command-macro-rules", "CHF", "REJECTED", "statement", "compare",
     "macro_rules on the `theorem` COMMAND: every `theorem n : T := p` is elaborated as `theorem n : True := trivial`; the "
     "challenge's statement lines occur verbatim, no sorry, no axiom, no meta API",
     src=F_HEAD + "macro_rules\n  | `(theorem $n:ident : $_ := $_) => `(/-- rewritten -/ theorem $n:ident : True := trivial)\n\n"
         "theorem t_false : False := by exact absurd rfl (by decide : (0 : Nat) ≠ 0)\n"
         "theorem t_one_eq_two : (1 : Nat) = 2 := by decide\ntheorem t_secret : secret = 8 := by decide\n")
case("F15-ofnat-instance", "CHF", "REJECTED", "statement", "compare",
     "high-priority instance OfNat Nat n := 0, so (1 : Nat) = 2 elaborates to 0 = 0 and is proved by rfl",
     src=F_HEAD + "theorem t_false : False := sorry\ntheorem t_secret : secret = 8 := sorry\n\n"
         "instance (priority := high) cheatOfNat (n : Nat) : OfNat Nat n := ⟨0⟩\n\n"
         "theorem t_one_eq_two : (1 : Nat) = 2 := rfl\n")
case("F16-redefine-fixed-def", "CHF", "REJECTED", "definition", "compare",
     "the fixed definition secret (not a hole) redefined := 8, t_secret by rfl",
     src="def secret : Nat := 8\n\ntheorem t_false : False := sorry\ntheorem t_one_eq_two : (1 : Nat) = 2 := sorry\n"
         "theorem t_secret : secret = 8 := rfl\n")
case("F17-decide-kernel-false", "CHF", "REJECTED", "build-kernel-observation", "kernel/build",
     "decide +kernel on (1 : Nat) = 2 (finding 017: with skip-kernel-tc the build may not see the kernel failure)",
     src=F_HEAD + "theorem t_one_eq_two : (1 : Nat) = 2 := by decide +kernel\n\n"
         "theorem t_false : False := absurd t_one_eq_two (by decide)\ntheorem t_secret : secret = 8 := t_false.elim\n")
case("F18-hash-exit", "CHF", "REJECTED", "missing", "export/compare", "#exit before the targets: they are never declared",
     src=F_HEAD + "#exit\n\ntheorem t_false : False := sorry\n" + F_TAIL)
case("F19-homoglyph-target", "CHF", "REJECTED", "missing", "export/compare",
     "target declared under a homoglyph name (t_fаlse with Cyrillic a); the real t_false is absent",
     src=F_HEAD + "theorem «t_fаlse» : False := sorry\ntheorem t_one_eq_two : (1 : Nat) = 2 := sorry\n"
         "theorem t_secret : secret = 8 := sorry\n")
case("F20-wf-sorry-termination", "CHF", "REJECTED", "sorry", "axioms",
     "False by a non-terminating well-founded recursion whose decreasing_by is sorry",
     src=F_HEAD + "def bad (n : Nat) : False := bad (n + 1)\ntermination_by n\ndecreasing_by sorry\n\n"
         "theorem t_false : False := bad 0\n" + F_TAIL)
case("F21-deep-axiom-multimodule", "CHF", "REJECTED", "axiom", "axioms",
     "axiom buried in an imported helper module behind three definitions (also exercises module merging)",
     files={"Solution.lean": "import Solution.A\n\ndef secret : Nat := 7\n\ntheorem t_false : False := Solution.c3\n" + F_TAIL,
            "Solution/A.lean": "import Solution.B\n\nnamespace Solution\ntheorem c3 : False := c2\nend Solution\n",
            "Solution/B.lean": "import Solution.C\n\nnamespace Solution\ntheorem c2 : False := c1\nend Solution\n",
            "Solution/C.lean": "namespace Solution\nset_option linter.all false\naxiom hidden : False\n"
                               "theorem c1 : False := hidden\nend Solution\n"})
case("F22-prelude-bogus-Iff", "CHF", "REJECTED", "redefine-core", "export (missing primitives) / compare",
     "prelude solution importing only Init.Notation (no Init.Core): its own Iff WITHOUT fields, propext/Quot.sound with the "
     "official statement text; propext then proves True = False. Kernel-valid; #print axioms shows only 'propext'",
     src="prelude\nimport Init.Notation\nuniverse u\n\ndef eagerReduce {α : Sort u} (a : α) : α := a\n\n"
         "structure Iff (a b : Prop) : Prop where\n  intro ::\n\n"
         "axiom propext {a b : Prop} : Iff a b → a = b\n\n"
         "axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b\n\n"
         "def secret : Nat := 7\n\n"
         "theorem t_false : False :=\n  @Eq.rec Prop True (fun x _ => x) True.intro False (@propext True False Iff.intro)\n"
         "theorem t_one_eq_two : (1 : Nat) = 2 := False.elim t_false\ntheorem t_secret : secret = 8 := False.elim t_false\n")
P_TAIL = ("\ndef eagerReduce {α : Sort u} (a : α) : α := a\n"
          "structure Iff (a b : Prop) : Prop where\n  intro ::\n  mp : a → b\n  mpr : b → a\n"
          "axiom propext {a b : Prop} : Iff a b → a = b\n"
          "axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b\n"
          "def secret : Nat := 7\n")
# P01/P02 (Init/Prelude copies with Nonempty / Nat.add patched) dropped: the primitives Nat.gcd/land/lor/xor/shiftLeft/
# shiftRight live outside Init.Prelude, so a prelude-only solution can never be exported with the comparator's target list.
case("F23-with-unfolding-all-exact", "CHF", "REJECTED", "fast-exact-plugin", "build",
     "with_unfolding_all exact with a wrong proof term (the sound preset's fast-exact plugin path must fall back and fail)",
     src=F_HEAD + "theorem t_one_eq_two : (1 : Nat) = 2 := by with_unfolding_all exact (rfl : (1 : Nat) = 1)\n\n"
         "theorem t_false : False := absurd t_one_eq_two (by decide)\ntheorem t_secret : secret = 8 := t_false.elim\n")
case("F24-sandbox-probe", "CHF", "REJECTED", "build-escape", "sandbox",
     "build-time IO: tries to write outside the project (/dev/shm, /scratch, /tmp, home, OUT parents), reach the network, "
     "read the environment and leave a detached process (closed stdio) that appends to .lake/LINGER_LOG every 5 s; the "
     "targets are sorry",
     src=F_HEAD + open(os.path.join(HERE, "probe.lean.in")).read() if os.path.exists(os.path.join(HERE, "probe.lean.in")) else None)
case("F25-replace-constant-type", "CHF", "REJECTED", "env-hack", "kernel",
     "honest theorem t_false : True := trivial, then Environment.addDeclCore (doCheck := false) re-adds t_false with type "
     "False (same value): an attempt to overwrite a checked constant; the other targets are then added WITH the kernel check "
     "(False.elim t_false), which passes because the build-time kernel environment was corrupted",
     src="import Lean\n\n" + F_HEAD + "theorem t_false : True := trivial\n\n"
         "open Lean Elab Command in\nrun_cmd do\n"
         "  let v : TheoremVal := { name := `t_false, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro, all := [`t_false] }\n"
         "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
         "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n\n"
         "\nopen Lean Elab Command Meta in\nrun_cmd liftTermElabM do\n"
         "  for (n, stx) in [(`t_one_eq_two, ← `((1 : Nat) = 2)), (`t_secret, ← `(secret = 8))] do\n"
         "    let ty ← instantiateMVars (← Lean.Elab.Term.elabTerm stx none)\n"
         "    let v : TheoremVal := { name := n, levelParams := [], type := ty, value := mkApp2 (mkConst ``False.elim [Level.zero]) ty (mkConst `t_false), all := [n] }\n"
         "    addDecl (Declaration.thmDecl v)   -- kernel-CHECKED: the kernel environment now believes t_false : False\n")
case("F26-unsafe-in-safe-via-hack", "CHF", "REJECTED", "env-hack", "kernel",
     "unsafe def loop : False := loop, then addDecl (skipKernelTC) of a SAFE theorem t_false whose value is the unsafe loop",
     src="import Lean\n\n" + F_HEAD + "unsafe def loop : False := loop\n\nopen Lean Elab Command in\nset_option debug.skipKernelTC true in\n"
         "run_cmd liftCoreM do\n  let v : TheoremVal := { name := `t_false, levelParams := [], type := mkConst ``False, value := mkConst ``loop, all := [`t_false] }\n  addDecl (Declaration.thmDecl v)\n" + F_TAIL)
case("F29-resource-probe", "CHF", "REJECTED", "build-resources", "sandbox (availability)",
     "build-time IO, bounded: 2 GiB into the sandbox /tmp (tmpfs = host RAM), 1 GiB into the project dir, 256 processes, "
     "a 2 GiB allocation; reports whether any limit applies (targets are sorry)",
     src=F_HEAD + open(os.path.join(HERE, "probe-resources.lean.in")).read())
DK = ("theorem t_one_eq_two : (1 : Nat) = 2 := by decide +kernel\n\n"
      "theorem t_false : False := absurd t_one_eq_two (by decide)\ntheorem t_secret : secret = 8 := t_false.elim\n")
case("F30-lakefile-skipKernelTC-decide-kernel", "CHF", "REJECTED", "kernel-skip-option", "kernel",
     "NO meta code, NO import Lean: the lakefile sets [leanOptions] debug.skipKernelTC = true and t_one_eq_two is proved by "
     "decide +kernel; lake build succeeds and #print axioms reports no axioms at all",
     src=F_HEAD + DK,
     lakefile=("lakefile.toml", 'name = "cheat_f30"\ndefaultTargets = ["Solution"]\n\n[leanOptions]\ndebug.skipKernelTC = true\n\n'
               '[[lean_lib]]\nname = "Solution"\n'))
case("F31-set-option-skipKernelTC-decide-kernel", "CHF", "REJECTED", "kernel-skip-option", "kernel",
     "as F30 but in the source: set_option debug.skipKernelTC true in theorem ... := by decide +kernel (no meta code)",
     src=F_HEAD + "set_option debug.skipKernelTC true in\n" + DK)
case("F32-lingerer-holds-stdout", "CHF", "REJECTED", "build-resources", "sandbox (availability)",
     "build-time #eval spawns a detached (setsid) child that INHERITS stdout and lives 5 min: a build driver that waits for "
     "EOF on the module's output (the official lake build) stalls for that long (targets are sorry)",
     src=F_HEAD + "#eval show IO Unit from do\n"
         "  let cfg : IO.Process.SpawnArgs := { cmd := \"setsid\", args := #[\"sh\", \"-c\", \"for i in $(seq 1 60); do date +%s >> .lake/LINGER_LOG; sleep 5; done\"] }\n"
         "  let _ ← IO.Process.spawn cfg\n  IO.println \"PROBE spawned a stdout-holding lingerer\"\n\n"
         "theorem t_false : False := sorry\ntheorem t_one_eq_two : (1 : Nat) = 2 := sorry\ntheorem t_secret : secret = 8 := sorry\n")
TGT = "CrystallineSemistableComparison.fc_range_le"   # a name in overlap/targets-top40.txt (targeted overlap of --preset sound)
case("F27-olean-swap-after-snapshot", "CHF", "REJECTED", "build-toctou", "kernel (targeted leg: not equal -> re-check)",
     "module A declares " + TGT + " : True := trivial (honest; a targeted-overlap name, so the sound preset checks it from a "
     "build snapshot); module B (imports A) waits 25 s, then recompiles an EVIL A (same module name, the target re-added "
     "with type False := Nat.zero via addDeclCore doCheck:=false) with its own lean binary over A.olean; module C (imports B) "
     "proves t_false from the evil target. The final export carries the evil version",
     files={"Solution.lean": "import Solution.C\n",
            "Solution/A.lean": "def secret : Nat := 7\n\ntheorem " + TGT + " : True := trivial\n",
            "Solution/B.lean": "import Solution.A\n\n#eval show IO Unit from do\n  IO.sleep 25000\n  let exe ← IO.appPath\n"
                               "  let out ← IO.Process.output { cmd := exe.toString, args := #[\"-R\", \"evil\", \"-o\",\n"
                               "    \".lake/build/lib/lean/Solution/A.olean\", \"evil/Solution/A.lean\"] }\n"
                               "  IO.println s!\"SWAP exe={exe} cwd={← IO.currentDir} rc={out.exitCode} {out.stdout.take 300} {out.stderr.take 300}\"\n\n"
                               "theorem b_marker : True := trivial\n",
            "Solution/C.lean": "import Solution.B\n\ntheorem t_false : False := " + TGT + "\n" + F_TAIL,
            "evil/Solution/A.lean": "import Lean\n\ndef secret : Nat := 7\n\nopen Lean Elab Command in\nrun_cmd do\n"
                                    "  let v : TheoremVal := { name := `" + TGT + ", levelParams := [], type := mkConst ``False, value := mkConst ``Nat.zero, all := [`" + TGT + "] }\n"
                                    "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
                                    "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n"})
case("F28-hint-name-env-hack", "CHF", "REJECTED", "env-hack", "kernel (targeted leg)",
     "an ill-typed declaration (addDeclCore doCheck:=false) under a targeted-overlap name " + TGT + " : False := Nat.zero, used by t_false",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Command in\nrun_cmd do\n"
         "  let v : TheoremVal := { name := `" + TGT + ", levelParams := [], type := mkConst ``False, value := mkConst ``Nat.zero, all := [`" + TGT + "] }\n"
         "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
         "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n\n"
         "theorem t_false : False := " + TGT + "\n" + F_TAIL)
# ---------------------------------------------------------------- proof-body-only cheats (statements verbatim, only the bodies differ)
case("B01-body-skipKernelTC-decide-kernel", "CHF", "REJECTED", "body-only kernel-skip", "kernel",
     "ONLY proof bodies, no imports, no meta code: t_one_eq_two := by set_option debug.skipKernelTC true in decide +kernel; "
     "#print axioms: none / [propext]",
     src=F_HEAD + "theorem t_one_eq_two : (1 : Nat) = 2 := by set_option debug.skipKernelTC true in decide +kernel\n"
         "theorem t_false : False := absurd t_one_eq_two (by decide)\ntheorem t_secret : secret = 8 := t_false.elim\n")
RT = ("  run_tac do\n"
      "    let ty ← (← getMainGoal).getType\n"
      "    let v : TheoremVal := { name := NAME, levelParams := [], type := ty, value := mkConst ``True.intro, all := [NAME] }\n"
      "    match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
      "    | .ok env => setEnv env\n    | .error _ => throwError \"addDeclCore failed\"\n"
      "    closeMainGoal `cheat (mkConst NAME)\n")
case("B02-body-run-tac-env-hack", "CHF", "REJECTED", "body-only env-hack", "kernel",
     "ONLY the proof body of t_false (header `import Lean`): a run_tac block adds t_false.cheat_aux : False := True.intro "
     "with addDeclCore (doCheck := false) and closes the goal with it; #print axioms t_false: none",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Tactic Meta in\ntheorem t_false : False := by\n"
         + RT.replace("NAME", "`t_false.cheat_aux") + "\ntheorem t_one_eq_two : (1 : Nat) = 2 := t_false.elim\ntheorem t_secret : secret = 8 := t_false.elim\n")
case("B03-body-run-tac-mathlib", "CHMF", "REJECTED", "body-only env-hack", "kernel",
     "Mathlib header exactly as in the challenge (no `import Lean`: Mathlib brings the meta API): m_false's body is the "
     "run_tac block of B02 (m_false.cheat_aux : (2:ℝ) < 1 := True.intro)",
     src="import Mathlib.Data.Real.Basic\n\nopen Lean Elab Tactic Meta in\ntheorem m_false : (2 : ℝ) < 1 := by\n"
         + RT.replace("NAME", "`m_false.cheat_aux"), mathlib=True)

case("F36-log-injection-name", "CHF", "REJECTED", "log-injection", "kernel (availability: from sources?)",
     "an ill-typed theorem (addDeclCore doCheck:=false) whose NAME is «x<newline>error: Lean default exited with 2<newline>» "
     "(a legal guillemet identifier), used by t_false: the kernel legs print the name in their error message (question: "
     "can a project turn its own REJECTED into 'no verdict' from SOURCES?)",
     src="import Lean\n\n" + F_HEAD + "open Lean Elab Command in\nrun_cmd do\n"
         "  let n := Name.mkStr Name.anonymous \"x\\nerror: Lean default exited with 2\\n\"\n"
         "  let v : TheoremVal := { name := n, levelParams := [], type := mkConst ``False, value := mkConst ``Nat.zero, all := [n] }\n"
         "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
         "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n\n"
         "theorem t_false : False := «x\nerror: Lean default exited with 2\n»\n" + F_TAIL)

# targeted overlap: a hinted target whose kernel check is LONG (~1 min) and still running when the final replay ends
HEAVY = "def heavyVal : Nat := (List.range 800000).foldl (· + ·) 0\n\n"
def forge_heavy(name, eq):
    return ("open Lean Elab Command Meta in\nrun_cmd liftTermElabM do\n"
            "  let p ← instantiateMVars (← Term.elabTerm (← `(%s)) none)\n"
            "  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)\n"
            "  let ty ← mkEq (mkApp2 (mkConst ``Decidable.decide) p inst) (mkConst ``Bool.true)\n"
            "  let v : TheoremVal := { name := `%s, levelParams := [], type := ty, value := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true), all := [`%s] }\n"
            "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
            "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n") % (eq, name, name)
SLEEP_B = "#eval show IO Unit from IO.sleep 20000   -- give the snapshot driver time to hand module A to the targeted leg\n\ntheorem b_marker : True := trivial\n"
TGT2 = "CrystallineSemistableComparison.factsC"
TGT3 = "GlobalTheory.HSAmp.norm_aeval_trace_le"
case("F35-slow-hinted-target-invalid", "CHF", "REJECTED", "targeted-overlap", "kernel (targeted leg, wait path)",
     "a targeted-overlap hint name " + TGT2 + " : decide (heavyVal = heavyVal + 1) = true := Eq.refl true, added WITHOUT a "
     "kernel check; rejecting it costs the kernel ~1 min (evaluating a fold over 800,000 numbers), so its targeted check is "
     "still RUNNING when the tiny final replay ends (a path the earlier soundness test sets could not reach); t_false follows cheaply via "
     "Nat.ne_add_one",
     files={"Solution.lean": "import Solution.C\n",
            "Solution/A.lean": "import Lean\n\ndef secret : Nat := 7\n\n" + HEAVY + forge_heavy(TGT2, "heavyVal = heavyVal + 1"),
            "Solution/B.lean": "import Solution.A\n\n" + SLEEP_B,
            "Solution/C.lean": "import Solution.B\n\ntheorem t_false : False := Nat.ne_add_one heavyVal (of_decide_eq_true " + TGT2 + ")\n"
                               "theorem t_one_eq_two : (1 : Nat) = 2 := t_false.elim\ntheorem t_secret : secret = 8 := t_false.elim\n"})
case("T22-slow-hinted-target-valid", "CHT", "ACCEPTED", "targeted-overlap", "-",
     "the valid counterpart of F35: " + TGT3 + " : decide (heavyVal = heavyVal) = true := Eq.refl true (kernel ~1 min, "
     "added without a build-time check), used by t_add; the final replay must WAIT for the running targeted check and accept",
     files={"Solution.lean": "import Solution.B\n\n" + T_HONEST.replace("theorem t_add (n : Nat) : n + 0 = n := rfl",
                 "theorem t_add (n : Nat) : n + 0 = n := (fun _ => rfl) (of_decide_eq_true " + TGT3 + ")"),
            "Solution/A.lean": "import Lean\n\n" + HEAVY + forge_heavy(TGT3, "heavyVal = heavyVal"),
            "Solution/B.lean": "import Solution.A\n\n" + SLEEP_B})

# ---------------------------------------------------------------- CHT: true targets
case("T00-honest", "CHT", "ACCEPTED", "control", "-", "honest solution", src=T_HONEST)
case("T01-honest-multimodule", "CHT", "ACCEPTED", "control", "-", "honest solution split over 5 modules (merge path)",
     files={"Solution.lean": "import Solution.Em\nimport Solution.Hole\n\nopen Sol in\ntheorem t_em (p : Prop) : p ∨ ¬p := em' p\n",
            "Solution/Em.lean": "import Solution.Pow\n\nnamespace Sol\ntheorem em' (p : Prop) : p ∨ ¬p := Classical.em p\nend Sol\n",
            "Solution/Pow.lean": "import Solution.Base\n\ntheorem t_pow : 2 ^ 64 % 7 = 2 := by decide\n",
            "Solution/Hole.lean": "import Solution.Base\n\ndef hole (n : Nat) : Nat := n + 1\n"
                                  "theorem t_hole (n : Nat) : 0 < hole n ∨ hole n = 0 := Or.inl (Nat.succ_pos n)\n",
            "Solution/Base.lean": "def secret : Nat := 7\ntheorem t_add (n : Nat) : n + 0 = n := rfl\n"
                                  "theorem t_secret : secret * 2 = 14 := rfl\n"})
case("T02-native-decide-true", "CHT", "REJECTED", "native_decide", "axioms", "t_pow by native_decide (true statement)",
     src=T_with(t_pow="theorem t_pow : 2 ^ 64 % 7 = 2 := by native_decide"))
case("T03-hole-other-body", "CHT", "ACCEPTED", "definition-hole", "-",
     "the hole (definition_names) given another body; t_hole re-proved (accepted by design)",
     src=T_with(hole="def hole (n : Nat) : Nat := 2 * n + 1",
                t_hole="theorem t_hole (n : Nat) : 0 < hole n ∨ hole n = 0 := Or.inl (Nat.succ_pos _)"))
case("T04-hole-other-type", "CHT", "REJECTED", "definition-hole", "compare", "the hole given another type (Nat → Int)",
     src=T_with(hole="def hole (n : Nat) : Int := n + 1",
                t_hole="theorem t_hole (n : Nat) : 0 < hole n ∨ hole n = 0 := by unfold hole; omega"))
case("T05-fixed-def-defeq-body", "CHT", "REJECTED", "definition", "compare",
     "fixed definition secret := 3 + 4 (definitionally equal, syntactically different)",
     src=T_with(secret="def secret : Nat := 3 + 4"))
case("T06-binder-rename", "CHT", "ACCEPTED", "statement-alpha", "-", "bound variable renamed (n -> m), proof unchanged",
     src=T_with(t_add="theorem t_add (m : Nat) : m + 0 = m := rfl"))
case("T08-sorry-true", "CHT", "REJECTED", "sorry", "axioms", "t_em by sorry", src=T_with(t_em="theorem t_em (p : Prop) : p ∨ ¬p := sorry"))
case("T09-unused-axiom", "CHT", "ACCEPTED", "axiom", "-", "an extra axiom that no target uses (official semantics: accepted)",
     src=T_HONEST + "\naxiom unused_cheat : False\ntheorem not_a_target : False := unused_cheat\n")
case("T10-decide-kernel-true", "CHT", "ACCEPTED", "control", "-", "t_pow by decide +kernel",
     src=T_with(t_pow="theorem t_pow : 2 ^ 64 % 7 = 2 := by decide +kernel"))
case("T11-ofReduceBool-true", "CHT", "REJECTED", "native_decide", "axioms", "t_pow through Lean.ofReduceBool (true)",
     src=T_with(t_pow="def powCheck : Bool := decide (2 ^ 64 % 7 = 2)\ntheorem t_pow : 2 ^ 64 % 7 = 2 := of_decide_eq_true (Lean.ofReduceBool powCheck true rfl)"))
case("T12-defeq-statement", "CHT", "REJECTED", "statement", "compare", "t_add stated as n + 0 = id n (defeq, not equal)",
     src=T_with(t_add="theorem t_add (n : Nat) : n + 0 = id n := rfl"))
case("T13-skipKernelTC-honest", "CHT", "ACCEPTED", "control", "-", "honest proofs under set_option debug.skipKernelTC true",
     src="set_option debug.skipKernelTC true\n" + T_HONEST)
case("T14-same-short-names", "CHT", "ACCEPTED", "names", "-",
     "extra declarations Foo.t_add, Foo.t_em, Foo.secret with other statements (namespaces)",
     src=T_HONEST + "\nnamespace Foo\ndef secret : Nat := 8\ntheorem t_add : (1 : Nat) = 1 := rfl\ntheorem t_em : True := trivial\nend Foo\n")
case("T15-merge-private-collisions", "CHT", "ACCEPTED", "merge-availability", "-",
     "two sibling modules with the same private names, local instances and set_option (merge must split or rename)",
     files={"Solution.lean": "import Solution.L\nimport Solution.R\n\ntheorem t_em (p : Prop) : p ∨ ¬p := Classical.em p\n"
                             "theorem t_hole (n : Nat) : 0 < hole n ∨ hole n = 0 := Or.inl (Nat.succ_pos n)\n",
            "Solution/L.lean": "import Solution.Base\nprivate def helper : Nat := 64\nprivate theorem aux : helper = 64 := rfl\n"
                               "local instance instL : Inhabited Nat := ⟨5⟩\nset_option maxRecDepth 2000\n"
                               "theorem t_pow : 2 ^ 64 % 7 = 2 := (fun _ => by decide) aux\n",
            "Solution/R.lean": "import Solution.Base\nprivate def helper : Nat := 0\nprivate theorem aux : helper = 0 := rfl\n"
                               "local instance instR : Inhabited Nat := ⟨6⟩\n"
                               "theorem t_add (n : Nat) : n + 0 = n := (fun _ => rfl) aux\n",
            "Solution/Base.lean": "def secret : Nat := 7\ndef hole (n : Nat) : Nat := n + 1\n"
                                  "theorem t_secret : secret * 2 = 14 := rfl\n"})
case("T16-deep-chain", "CHT", "ACCEPTED", "control", "-", "honest, 12-module linear import chain",
     files=dict([("Solution.lean", "import Solution.M11\n" + T_HONEST.replace("theorem t_em (p : Prop) : p ∨ ¬p := Classical.em p",
                                                                               "theorem t_em (p : Prop) : p ∨ ¬p := Chain.m11 p"))]
                + [("Solution/M%d.lean" % i, ("import Solution.M%d\n" % (i - 1) if i else "") +
                    "namespace Chain\ntheorem m%d (p : Prop) : p ∨ ¬p := %s\nend Chain\n" % (i, "m%d p" % (i - 1) if i else "Classical.em p"))
                   for i in range(12)]))
case("T17-with-unfolding-all-exact", "CHT", "ACCEPTED", "fast-exact-plugin", "-",
     "honest proofs by `with_unfolding_all exact` (the fast-exact plugin's accelerated path)",
     src=T_with(t_secret="theorem t_secret : secret * 2 = 14 := by with_unfolding_all exact rfl",
                t_add="theorem t_add (n : Nat) : n + 0 = n := by with_unfolding_all exact rfl"))
case("T18-lakefile-lean", "CHT", "ACCEPTED", "config", "-", "honest solution with a root lakefile.lean instead of lakefile.toml",
     src=T_HONEST, lakefile=("lakefile.lean", 'import Lake\nopen Lake DSL\n\npackage cheatT18\n\n@[default_target]\nlean_lib Solution\n'))
case("T19-prelude-import-Init", "CHT", "ACCEPTED", "header", "-", "honest solution with `prelude` + `import Init` header",
     src="prelude\nimport Init\n\n" + T_HONEST)
case("T21-flaky-first-build", "CHT", "REJECTED", "build-state", "build (official: no retry)",
     "honest proofs, but a build-time #eval fails the module's FIRST elaboration (it leaves a marker in .lake and throws); "
     "a second elaboration in the same tree succeeds. The official lake build fails; a retrying or state-reusing build "
     "succeeds and exports a VALID proof (sound accept is allowed, exact presets must give the official verdict)",
     src="#eval show IO Unit from do\n  if (← System.FilePath.pathExists \".lake/flaky-marker\") then pure ()\n  else\n"
         "    IO.FS.writeFile \".lake/flaky-marker\" \"1\"\n    throw (IO.userError \"flaky first build (simulated transient failure)\")\n\n" + T_HONEST, exp_sound="ACCEPTED")
case("T20-macro-tactics", "CHT", "ACCEPTED", "control", "-", "honest proofs through custom tactic macros and simp/omega",
     src=T_with(t_add='macro "my_arith" : tactic => `(tactic| first | omega | simp | decide)\n\ntheorem t_add (n : Nat) : n + 0 = n := by my_arith',
                t_secret="theorem t_secret : secret * 2 = 14 := by simp [secret]"))


# ---------------------------------------------------------------- CHM / CHMF: Mathlib 0df444a (true / false targets)
M_HONEST = ("import Mathlib.NumberTheory.FLT.Three\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Data.Real.Basic\n\n"
            "theorem m_flt3 : FermatLastTheoremFor 3 := fermatLastTheoremThree\n"
            "theorem m_prime : Nat.Prime 1000003 := by norm_num\n"
            "theorem m_real : (1 : ℝ) < 2 := by norm_num\n")
case("M00-honest", "CHM", "ACCEPTED", "control", "-", "honest Mathlib solution (FLT3 from Mathlib, norm_num)", src=M_HONEST, mathlib=True)
case("M01-native-decide-prime", "CHM", "REJECTED", "native_decide", "axioms", "m_prime by native_decide",
     src=M_HONEST.replace("theorem m_prime : Nat.Prime 1000003 := by norm_num", "theorem m_prime : Nat.Prime 1000003 := by native_decide"), mathlib=True)
case("M02-sorry-fact-instance", "CHM", "REJECTED", "sorry", "axioms", "a Fact instance proved by sorry, m_prime := Fact.out",
     src=M_HONEST.replace("theorem m_prime : Nat.Prime 1000003 := by norm_num",
                          "instance bogusFact : Fact (Nat.Prime 1000003) := ⟨sorry⟩\ntheorem m_prime : Nat.Prime 1000003 := Fact.out"), mathlib=True)
case("M03-macro-rules-flip-lt", "CHMF", "REJECTED", "statement", "compare",
     "macro_rules rewrites every `a < b` into `b < a`, so m_false : (2 : ℝ) < 1 elaborates to 1 < 2 (norm_num)",
     src="import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.NormNum\n\nmacro_rules | `($a < $b) => `(binrel% LT.lt $b $a)\n\n"
         "theorem m_false : (2 : ℝ) < 1 := by norm_num\n", mathlib=True)
case("M04-env-hack", "CHMF", "REJECTED", "env-hack", "kernel",
     "m_false : (2 : ℝ) < 1 added with Environment.addDeclCore (doCheck := false), value = a proof of 1 < 2",
     src="import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.NormNum\n\ntheorem one_lt_two_real : (1 : ℝ) < 2 := by norm_num\n"
         "theorem m_false_stmt_holder : ((2 : ℝ) < 1) = ((2 : ℝ) < 1) := rfl\n\n"
         "open Lean Elab Command Meta in\nrun_cmd do\n"
         "  let ty ← liftTermElabM do\n    let e ← Lean.Elab.Term.elabTerm (← `((2 : ℝ) < 1)) none\n    instantiateMVars e\n"
         "  let v : TheoremVal := { name := `m_false, levelParams := [], type := ty, value := mkConst ``one_lt_two_real, all := [`m_false] }\n"
         "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
         "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"\n", mathlib=True)


def write(out):
    os.makedirs(os.path.join(out, "cases"), exist_ok=True)
    shutil.copytree(os.path.join(HERE, "challenges"), os.path.join(out, "challenges"), dirs_exist_ok=True)
    meta = {}
    for c in CASES:
        d = os.path.join(out, "cases", c["id"])
        if os.path.exists(d):
            shutil.rmtree(d)
        os.makedirs(d)
        for rel, text in c["files"].items():
            if text is None:
                raise SystemExit("case %s: missing source" % c["id"])
            if isinstance(text, tuple) and text[0] == "PRELUDE":
                base = open(PRELUDE, encoding="utf-8").read()
                for old, new in text[1]:
                    if base.count(old) != 1:
                        raise SystemExit("case %s: patch anchor found %d times: %r" % (c["id"], base.count(old), old))
                    base = base.replace(old, new)
                text = base + "\n" + text[2]
            p = os.path.join(d, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as f:
                f.write(text)
        with open(os.path.join(d, "lean-toolchain"), "w") as f:
            f.write("leanprover/lean4:v4.33.1\n")
        if c["mathlib"]:
            name = "cheat_" + c["id"].split("-")[0].lower()
            with open(os.path.join(d, "lakefile.toml"), "w") as f:
                f.write(LAKE.format(name=name).replace("\n\n[[lean_lib]]", MATHLIB_REQ + "\n[[lean_lib]]"))
            man = json.load(open(MANIFEST))
            man["name"] = name
            with open(os.path.join(d, "lake-manifest.json"), "w") as f:
                json.dump(man, f, indent=1)
        elif c["lakefile"]:
            with open(os.path.join(d, c["lakefile"][0]), "w") as f:
                f.write(c["lakefile"][1])
        else:
            with open(os.path.join(d, "lakefile.toml"), "w") as f:
                f.write(LAKE.format(name="cheat_" + c["id"].split("-")[0].lower()))
        meta[c["id"]] = {k: c[k] for k in ("challenge", "expected_official", "cls", "catcher", "desc", "mathlib")}
        if c["exp_sound"]:
            meta[c["id"]]["expected_sound"] = c["exp_sound"]
    with open(os.path.join(out, "cases.json"), "w") as f:
        json.dump(meta, f, indent=1, ensure_ascii=False)
    print("wrote %d cases to %s" % (len(CASES), out))

if __name__ == "__main__":
    write(sys.argv[1])
