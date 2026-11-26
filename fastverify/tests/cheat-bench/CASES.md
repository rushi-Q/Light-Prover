| case | challenge | official verdict (expected) | class | description |
|---|---|---|---|---|
| B01-body-skipKernelTC-decide-kernel | CHF | REJECTED | body-only kernel-skip | ONLY proof bodies, no imports, no meta code: t_one_eq_two := by set_option debug.skipKernelTC true in decide +kernel; #print axioms: none / [propext] |
| B02-body-run-tac-env-hack | CHF | REJECTED | body-only env-hack | ONLY the proof body of t_false (header `import Lean`): a run_tac block adds t_false.cheat_aux : False := True.intro with addDeclCore (doCheck := false) and closes the goal with it; #print axioms t_false: none |
| B03-body-run-tac-mathlib | CHMF | REJECTED | body-only env-hack | Mathlib header exactly as in the challenge (no `import Lean`: Mathlib brings the meta API): m_false's body is the run_tac block of B02 (m_false.cheat_aux : (2:ℝ) < 1 := True.intro) |
| F01-sorry | CHF | REJECTED | sorry | plain sorry |
| F02-sorry-macro | CHF | REJECTED | sorry | sorry hidden behind a custom tactic macro |
| F03-admit-elab | CHF | REJECTED | sorry | custom tactic elaborator that admits the goal (MVarId.admit) |
| F04-silent-sorry | CHF | REJECTED | sorry | sorry behind a term elaborator (synthetic sorry) AND `set_option warn.sorry false`: the build prints no 'declaration uses sorry' warning at all |
| F05-axiom | CHF | REJECTED | axiom | new axiom magic : False |
| F06-axiom-permitted-name-ns | CHF | REJECTED | axiom | axiom named Cheat.propext (a permitted short name in another namespace), opened |
| F07-axiom-homoglyph | CHF | REJECTED | axiom | axiom whose name is a homoglyph of propext (Cyrillic e) and one with a trailing space «propext » |
| F08-opaque-implemented-by | CHF | REJECTED | opaque/implemented_by | opaque magic : False with @[implemented_by] an unsafe loop (needs Inhabited False: the build must fail) |
| F09-native-decide-implemented-by | CHF | REJECTED | native_decide | native_decide on a Bool whose compiled implementation (implemented_by) lies; then False by unfolding |
| F10-decide-native-implemented-by | CHF | REJECTED | native_decide | decide +native (the new spelling of native_decide) on a Bool whose compiled implementation (implemented_by) lies |
| F11-skipKernelTC-addDecl | CHF | REJECTED | env-hack | run_cmd addDecl of an ill-typed theorem (t_false : False := Nat.zero) under set_option debug.skipKernelTC true |
| F12-env-addDeclCore-nocheck | CHF | REJECTED | env-hack | public Lean.Environment.addDeclCore (doCheck := false) from run_cmd: t_false : False := Nat.zero, no option needed |
| F13-theorem-as-axiom | CHF | REJECTED | kind | the target itself declared as an axiom |
| F14-statement-tricks-all | CHF | REJECTED | statement | all three targets 'proved' by statement-changing tricks and nothing else (no sorry, no axiom, no meta code): notation "False" => True (t_false states True), a high-priority instance OfNat Nat n := 0 (1 = 2 becomes 0 = 0), and the fixed definition secret redefined (secret := 8); the challenge's statement lines occur verbatim |
| F15-ofnat-instance | CHF | REJECTED | statement | high-priority instance OfNat Nat n := 0, so (1 : Nat) = 2 elaborates to 0 = 0 and is proved by rfl |
| F16-redefine-fixed-def | CHF | REJECTED | definition | the fixed definition secret (not a hole) redefined := 8, t_secret by rfl |
| F17-decide-kernel-false | CHF | REJECTED | build-kernel-observation | decide +kernel on (1 : Nat) = 2 (finding 017: with skip-kernel-tc the build may not see the kernel failure) |
| F18-hash-exit | CHF | REJECTED | missing | #exit before the targets: they are never declared |
| F19-homoglyph-target | CHF | REJECTED | missing | target declared under a homoglyph name (t_fаlse with Cyrillic a); the real t_false is absent |
| F20-wf-sorry-termination | CHF | REJECTED | sorry | False by a non-terminating well-founded recursion whose decreasing_by is sorry |
| F21-deep-axiom-multimodule | CHF | REJECTED | axiom | axiom buried in an imported helper module behind three definitions (also exercises module merging) |
| F22-prelude-bogus-Iff | CHF | REJECTED | redefine-core | prelude solution importing only Init.Notation (no Init.Core): its own Iff WITHOUT fields, propext/Quot.sound with the official statement text; propext then proves True = False. Kernel-valid; #print axioms shows only 'propext' |
| F23-with-unfolding-all-exact | CHF | REJECTED | fast-exact-plugin | with_unfolding_all exact with a wrong proof term (the sound preset's fast-exact plugin path must fall back and fail) |
| F24-sandbox-probe | CHF | REJECTED | build-escape | build-time IO: tries to write outside the project (/dev/shm, the host scratch directories, /tmp, home, OUT parents), reach the network, read the environment and leave a detached process (closed stdio) that appends to .lake/LINGER_LOG every 5 s; the targets are sorry |
| F25-replace-constant-type | CHF | REJECTED | env-hack | honest theorem t_false : True := trivial, then Environment.addDeclCore (doCheck := false) re-adds t_false with type False (same value): an attempt to overwrite a checked constant; the other targets are then added WITH the kernel check (False.elim t_false), which passes because the build-time kernel environment was corrupted |
| F26-unsafe-in-safe-via-hack | CHF | REJECTED | env-hack | unsafe def loop : False := loop, then addDecl (skipKernelTC) of a SAFE theorem t_false whose value is the unsafe loop |
| F27-olean-swap-after-snapshot | CHF | REJECTED | build-toctou | module A declares CrystallineSemistableComparison.fc_range_le : True := trivial (honest; a targeted-overlap name, so the sound preset checks it from a build snapshot); module B (imports A) waits 25 s, then recompiles an EVIL A (same module name, the target re-added with type False := Nat.zero via addDeclCore doCheck:=false) with its own lean binary over A.olean; module C (imports B) proves t_false from the evil target. The final export carries the evil version |
| F28-hint-name-env-hack | CHF | REJECTED | env-hack | an ill-typed declaration (addDeclCore doCheck:=false) under a targeted-overlap name CrystallineSemistableComparison.fc_range_le : False := Nat.zero, used by t_false |
| F29-resource-probe | CHF | REJECTED | build-resources | build-time IO, bounded: 2 GiB into the sandbox /tmp (tmpfs = host RAM), 1 GiB into the project dir, 256 processes, a 2 GiB allocation; reports whether any limit applies (targets are sorry) |
| F30-lakefile-skipKernelTC-decide-kernel | CHF | REJECTED | kernel-skip-option | NO meta code, NO import Lean: the lakefile sets [leanOptions] debug.skipKernelTC = true and t_one_eq_two is proved by decide +kernel; lake build succeeds and #print axioms reports no axioms at all |
| F31-set-option-skipKernelTC-decide-kernel | CHF | REJECTED | kernel-skip-option | as F30 but in the source: set_option debug.skipKernelTC true in theorem ... := by decide +kernel (no meta code) |
| F32-lingerer-holds-stdout | CHF | REJECTED | build-resources | build-time #eval spawns a detached (setsid) child that INHERITS stdout and lives 5 min: a build driver that waits for EOF on the module's output (the official lake build) stalls for that long (targets are sorry) |
| F34-command-macro-rules | CHF | REJECTED | statement | macro_rules on the `theorem` COMMAND: every `theorem n : T := p` is elaborated as `theorem n : True := trivial`; the challenge's statement lines occur verbatim, no sorry, no axiom, no meta API |
| F35-slow-hinted-target-invalid | CHF | REJECTED | targeted-overlap | a targeted-overlap hint name CrystallineSemistableComparison.factsC : decide (heavyVal = heavyVal + 1) = true := Eq.refl true, added WITHOUT a kernel check; rejecting it costs the kernel ~1 min (evaluating a fold over 800,000 numbers), so its targeted check is still RUNNING when the tiny final replay ends (a path the earlier soundness test sets could not reach); t_false follows cheaply via Nat.ne_add_one |
| F36-log-injection-name | CHF | REJECTED | log-injection | an ill-typed theorem (addDeclCore doCheck:=false) whose NAME is «x<newline>error: Lean default exited with 2<newline>» (a legal guillemet identifier), used by t_false: the kernel legs print the name in their error message (question: can a project turn its own REJECTED into 'no verdict' from SOURCES?) |
| M00-honest | CHM | ACCEPTED | control | honest Mathlib solution (FLT3 from Mathlib, norm_num) |
| M01-native-decide-prime | CHM | REJECTED | native_decide | m_prime by native_decide |
| M02-sorry-fact-instance | CHM | REJECTED | sorry | a Fact instance proved by sorry, m_prime := Fact.out |
| M03-macro-rules-flip-lt | CHMF | REJECTED | statement | macro_rules rewrites every `a < b` into `b < a`, so m_false : (2 : ℝ) < 1 elaborates to 1 < 2 (norm_num) |
| M04-env-hack | CHMF | REJECTED | env-hack | m_false : (2 : ℝ) < 1 added with Environment.addDeclCore (doCheck := false), value = a proof of 1 < 2 |
| T00-honest | CHT | ACCEPTED | control | honest solution |
| T01-honest-multimodule | CHT | ACCEPTED | control | honest solution split over 5 modules (merge path) |
| T02-native-decide-true | CHT | REJECTED | native_decide | t_pow by native_decide (true statement) |
| T03-hole-other-body | CHT | ACCEPTED | definition-hole | the hole (definition_names) given another body; t_hole re-proved (accepted by design) |
| T04-hole-other-type | CHT | REJECTED | definition-hole | the hole given another type (Nat → Int) |
| T05-fixed-def-defeq-body | CHT | REJECTED | definition | fixed definition secret := 3 + 4 (definitionally equal, syntactically different) |
| T06-binder-rename | CHT | ACCEPTED | statement-alpha | bound variable renamed (n -> m), proof unchanged |
| T08-sorry-true | CHT | REJECTED | sorry | t_em by sorry |
| T09-unused-axiom | CHT | ACCEPTED | axiom | an extra axiom that no target uses (official semantics: accepted) |
| T10-decide-kernel-true | CHT | ACCEPTED | control | t_pow by decide +kernel |
| T11-ofReduceBool-true | CHT | REJECTED | native_decide | t_pow through Lean.ofReduceBool (true) |
| T12-defeq-statement | CHT | REJECTED | statement | t_add stated as n + 0 = id n (defeq, not equal) |
| T13-skipKernelTC-honest | CHT | ACCEPTED | control | honest proofs under set_option debug.skipKernelTC true |
| T14-same-short-names | CHT | ACCEPTED | names | extra declarations Foo.t_add, Foo.t_em, Foo.secret with other statements (namespaces) |
| T15-merge-private-collisions | CHT | ACCEPTED | merge-availability | two sibling modules with the same private names, local instances and set_option (merge must split or rename) |
| T16-deep-chain | CHT | ACCEPTED | control | honest, 12-module linear import chain |
| T17-with-unfolding-all-exact | CHT | ACCEPTED | fast-exact-plugin | honest proofs by `with_unfolding_all exact` (the fast-exact plugin's accelerated path) |
| T18-lakefile-lean | CHT | ACCEPTED | config | honest solution with a root lakefile.lean instead of lakefile.toml |
| T19-prelude-import-Init | CHT | ACCEPTED | header | honest solution with `prelude` + `import Init` header |
| T20-macro-tactics | CHT | ACCEPTED | control | honest proofs through custom tactic macros and simp/omega |
| T21-flaky-first-build | CHT | REJECTED (sound: ACCEPTED) | build-state | honest proofs, but a build-time #eval fails the module's FIRST elaboration (it leaves a marker in .lake and throws); a second elaboration in the same tree succeeds. The official lake build fails; a retrying or state-reusing build succeeds and exports a VALID proof (sound accept is allowed, exact presets must give the official verdict) |
| T22-slow-hinted-target-valid | CHT | ACCEPTED | targeted-overlap | the valid counterpart of F35: GlobalTheory.HSAmp.norm_aeval_trace_le : decide (heavyVal = heavyVal) = true := Eq.refl true (kernel ~1 min, added without a build-time check), used by t_add; the final replay must WAIT for the running targeted check and accept |
