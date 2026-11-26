# Proof-cheating benchmark (`tests/cheat-bench/`)

**Question.** Does any configuration of fastverify ACCEPT a source-level "proof" that an AI prover (or an adversary) could
produce by cheating instead of proving? And how do simpler verifier set-ups, as used by many evaluation harnesses, fare on
the same inputs?

**Answer (measured; the run records are not shipped, `run.sh` + `summarize.py` regenerate them).** 65 cases (50 cheats, 15 controls),
1,355 runs (reference / sound / fast-exact / default, repeats incl. a run after two fixes found by this benchmark,
threads 1/4/8/32, the UNSAFE `fastest` preset, an AMD host with the zygote + PGO toolchains) + a source mutation campaign
(`mut.py`: 595 mutants of 61 base projects x reference/sound): **no fastverify preset ever accepted what the official flow
rejected.** The only verdict differences: T21 (sound accepts a VALID proof whose official build fails once; `test.sh`
requires the unmodified official comparator to accept that very export) and F36 (sound gives "no verdict" where the official
flow rejects: a declaration name carrying an injected error line steers `check-sound.sh`'s exit mapping). The naive
configurations are fooled (of the 49 officially rejected cases): `lake build` succeeds on 45, "no `sorry` warning" passes 33
(defeated by `set_option warn.sorry false`), "`#print axioms` + statement text verbatim" passes 15 (meta-programmed
declarations, the kernel-skip option `debug.skipKernelTC` + `decide +kernel` - also as a ONE-LINE proof body, statement-
changing notation / instances / `macro_rules`, a `prelude` module with its own `propext`), "kernel replay only" passes 28
(every axiom / sorry / statement cheat). Only the full check (statement comparison + axiom closure + kernel replay of the
whole closure) rejects all of them.

## Layout
| file | what |
|---|---|
| `gen.py OUTDIR` | generates the 65-case corpus: `challenges/` (copied) + `cases/<id>/` (Lean 4.33.1 projects) + `cases.json` (challenge, expected official verdict, class, intended catcher, description). Small: everything is regenerated. |
| `challenges/CHF` | Mathlib-free challenge whose targets are all FALSE (`t_false : False`, `t_one_eq_two : (1:Nat) = 2`, `t_secret : secret = 8` with the fixed `def secret := 7`): any ACCEPT is unsound |
| `challenges/CHT` | Mathlib-free, all targets TRUE (incl. a `definition_names` hole and a `Classical.em` target): honest controls + "forbidden means" cheats |
| `challenges/CHM`, `CHMF` | Mathlib 0df444a: true targets (FLT for n = 3, `Nat.Prime 1000003`, `(1:ℝ) < 2`) / a false target (`(2:ℝ) < 1`) |
| `probe.lean.in`, `probe-resources.lean.in` | build-time IO probes (sandbox: writes, reads, network, detached processes; bounded resource use) used by F24 / F29 |
| `run.sh OUTROOT LANES THREADS "PRESETS" [GLOB]` | freezes a copy of the package (`FV_UNDER_TEST`, default the live `fastverify/`) in OUTROOT/pkg, runs every case x preset through `bin/fastverify` (all project code is elaborated in the package's bwrap sandbox), then `summarize.py`. `EXCLUDE=REGEX` skips cases |
| `summarize.py OUTROOT` | `summary.tsv` (one row per run: verdict, status, build/export attempts, reason) + `summary.md` (pivot). Status: PASS = verdict equals the expected official verdict; FAIL-CRITICAL = ACCEPTED where the official verdict is REJECTED |
| `verifiers.py CORPUS WORKDIR` | the naive configurations V1-V4 (below), every project built in bwrap (`tools/lsand.sh`) |
| `report.py` | merges `summary.tsv` + `verifiers.tsv` (+ the AMD summary) into one merged markdown table |
| `amd.sh [PRESETS]` | the same benchmark on an AMD host with the deployed package (zygote + PGO toolchains active there): `bash amd.sh` in a copy of this directory with the package under test at `fv/` |
| `tools/lsand.sh DIR CMD` | bwrap wrapper (no network, `/` read-only, home hidden, only DIR writable) |
| `mut.py BASE OUT [N [all\|core\|mathlib]]`, `mutsum.py OUTROOT...` | source mutation campaign on a corpus of honest one-challenge projects (`projects/<id>/Solution.lean` + `challenges/<id>/` + `cases.json`; 9 operators) and its reference-vs-sound table |

## Verifier configurations compared
| config | accepts when |
|---|---|
| V1 | `lake build` exits 0 |
| V2 | V1 and the build output has no "declaration uses 'sorry'" warning |
| V3 | V2 and `#print axioms T` (appended to a copy of the solution file) lists only `propext`, `Quot.sound`, `Classical.choice` for every target T, and every `theorem NAME ... :` line of the challenge occurs verbatim in the solution sources |
| V4 | the official lean4export (v4.33.0, `LEAN_ABORT_ON_PANIC=1`) of the targets' closure is accepted by the official Lean 4.36 `leanchecker --from-export` (kernel replay without statement/axiom comparison) |
| reference | the official flow: official `lake build` (B0) + official lean4export (E0) + unmodified Lean 4.36 `lake comparator` (C0) = `bin/fastverify --preset reference` |
| sound / fast-exact / default | the fastverify presets |

## Running
```
# Intel host, 64 cores, all presets, 8 lanes x 8 threads (~25 min; F24/F32 stall the build on purpose)
tests/cheat-bench/run.sh $SCRATCH/cheat 8 8 'reference sound fast-exact default'
# naive verifiers
python3 tests/cheat-bench/gen.py $SCRATCH/cheat-corpus && LANES=8 python3 tests/cheat-bench/verifiers.py $SCRATCH/cheat-corpus $SCRATCH/verif
python3 tests/cheat-bench/report.py CORPUS/cases.json OUT/summary.tsv VERIF/verifiers.tsv [AMD_summary.tsv] > RESULTS.md
```
Pass criterion of the regression use: `summarize.py` prints `FAIL 0` (no ACCEPT of an officially rejected case) and every
`sound` verdict equals the `reference` verdict.
