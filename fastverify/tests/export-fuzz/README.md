# export-fuzz — crafted exports against the sound check

In sound mode the build, the exporter and the orchestration are untrusted: the soundness claim is a claim about
`check/sound/check-sound.sh` (CS) on an **arbitrary export file**. This directory attacks CS at exactly that boundary and
compares every verdict with the unmodified Lean 4.36 `lake comparator` (`check/official/check.sh`, Lean-only configuration
= the oracle).

| status of a row | meaning |
|---|---|
| **FAIL-CRITICAL** | CS ACCEPTED and the official comparator did not (re-checked with the unmodified `check-sound.sh`) |
| **FAIL-PARSER** | `parsediff`: the trusted fast reader returned an environment different from the official reader's (parser agreement) |
| WARN-AVAIL | the official comparator ACCEPTED, CS did not (availability) |
| OK-ACCEPT / OK-REJECT / OK-DECLINE / OF-ERROR | both accept / both reject / CS no verdict, official reject / official could not run |

## Tools

| file | what |
|---|---|
| `xfuzz.py` | 52 structure-aware mutation operators, classes S (syntax/bytes), I (index tables), D (declarations, inductive/ctor/recursor records), E (expressions, levels, names), C (comparator level), R (meaning-preserving re-serialization), P (proof-only = kernel-level: only declarations/expressions outside the comparator's statement closure, incl. the targets' proofs). `xfuzz.py list` prints them |
| `seams.py` | 46 targeted cases per base (unsafe/partial skipping, orphan ctors/recs, inductive records, block layout, mutual `all`, NUL bytes, malformed hygienic names, target edge cases, literal syntax, quotient lines, definition holes, log-line injection through names) |
| `runfuzz.py` | per mutant: parsediff, official comparator, CS (bulk variant), the second kernel alone; `--premade DIR` runs a case directory |
| `bigfuzz.py` | the same for Mathlib-scale bases (parse once, fork workers, one mutant at a time on disk) |
| `mkbulk.py` | derives `$W/check-sound-bulk.sh` from `check-sound.sh`: identical decision logic without the input-independent per-run checks (pin hashes, toolchain verification, self-test), which `setup.sh` runs once with the unmodified script. Every CS accept the official tool does not give is re-run with the unmodified script |
| `parsediff/` | `ParseDiff.lean` (built by `build.sh` against the verbatim trusted reader sources of `check/sound/src`), `realrun.sh` (parser agreement on real exports), `sbx.sh` (bwrap, no network: crafted exports are only read inside it) |
| `bases/` | `mkbases.py` (6 Init-only base projects: ind, quot, lit, univ, hole), `mk.sh` (built with `--preset reference`) |
| `campaign.sh`, `runseams.sh`, `e2e_exportin.sh`, `thrmatrix.sh`, `resmatrix.sh` | campaigns, seams, export-in through `bin/fastverify --from-export --preset sound`, thread matrix, resource limits |
| `test.sh` | the regression test (setup, seams vs `results/seams-expected.tsv`, 2 mutants/operator/base, export-in, parser agreement on the bases) |
| `toctou/test.sh [N]` | regression test of the TOCTOU defect: the export is rewritten in place (A <-> B, neither a proof) while the package judges it; FIXED since check-sound.sh cab8c319 / lib/fastverify.py ef9b6b97 (40/40 runs without an accept), OPEN on the earlier versions (3-6 accepts per 40) |
| `summarize.py` | markdown tables of a run (per base / class, availability reasons, who decided, second kernel alone) |

## Running

```
export EXPORT_FUZZ_WORK=$SCRATCH/exportfuzz                # local work dir
tests/export-fuzz/test.sh                                   # regression, ~10-20 min on 16-32 cores
tests/export-fuzz/setup.sh && tests/export-fuzz/campaign.sh OUT 25 SEED 16      # a full campaign (all operators, 25 each)
tests/export-fuzz/campaign.sh OUT 100 7 8 ind quot -- P_node,P_decl             # kernel-level (proof-only) mutations
tests/export-fuzz/parsediff/realrun.sh OUT.tsv $BENCH_INPUTS/mathlib/export/mathlib.export ...   # parser agreement on real exports
python3 tests/export-fuzz/summarize.py OUT
```
Requirements: the package's pinned sound-check binaries on this host (`check-sound.sh --preflight` must pass), the official
Lean 4.33.1 / 4.36.0 toolchains, bwrap. Optional base `cmpx` = the cmpx corpus accept-base against the rh-miniF mini
challenge (`CMPX_DIR`, `RHMINI_CHALLENGE`).
