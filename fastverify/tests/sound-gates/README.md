# Soundness suites of the sound check — `tests/sound-gates/`

One harness, `gates.py`, runs every suite (selected with `--gate NAME`) that a change to a TRUSTED component of the sound mode
(`check/sound/check-sound.sh` and the binaries it pins: ccmp, pleanchecker, gruszka; any new parser / replay driver /
verdict logic) must pass before it is used for a verdict:

| suite (`--gate`) | input | what is run | pass criterion |
|---|---|---|---|
| `arena` | lean-kernel-arena suite, 225 exports (`$BENCH_INPUTS/arena/suite`, label = `good/` or `bad/`; the official 4.36 `leanchecker` agrees with the label on 225/225) | the two kernel legs exactly as `check-sound.sh` runs them (legs file: binary, flags, environment) | the official-kernel leg gives the label on every test (= the official verdict); no bad test accepted by the combination (both legs accept) |
| `suitex` | an adversarial kernel corpus (`$BENCH_INPUTS/suitex`: authoritative copy 762 tests, a mirror with 742) | same legs | no bad test accepted (lean leg or combination); false rejects / declines are reported as WARN (availability) |
| `cmpx` | comparator-level corpus (`$BENCH_INPUTS/cmpx`), 27 kernel-valid solutions vs the rh-miniF mini challenge (`$BENCH_INPUTS/rh-miniF`), labels = official comparator (`expected.txt`), in both configs (leanonly, nanoda) | `check-sound.sh EXPORT CHALLENGE CONFIG` | every reject case REJECTED (no accept); accept cases rejected/declined = WARN. `split-fmt-thm-moved-to-end`: official leanonly ACCEPTS, official nanoda REJECTS (nanoda's format limits) -> either verdict passes in the nanoda config |
| `mathlib` | Mathlib differential (`$BENCH_INPUTS/mathlib-differential`, not shipped): 3 projects + 16 variants, exports made once with the unmodified package (`tools/mk_mathlib_corpus.sh`, preset fast-exact) | `check-sound.sh` on (solution export, challenge export, comparator.json) | every verdict = `cases.json` `expected_official` (P1-f-builderror has no export: the build fails) |
| `mutants` | the 61.6 GB RH export and its mutants M1-M4 (made with `tools/fvmut.cpp` + `specs/M1.spec`-`specs/M4.spec`; sha256 identical to the published mutants) | `check-sound.sh` with the RH challenge | honest ACCEPTED; M1 (early ill-typed proof), M2 (late ill-typed proof), M3 (illegal axiom 51 steps deep), M4 (statement definition := True) all REJECTED |
| `mathlib-e2e` (tools/mathlib_e2e.sh) | the same 19 Mathlib-differential cases, whole pipeline | `bin/fastverify PROJECT CHALLENGE OUT --preset sound` (exercises the orchestrator's verdict logic: decide_sound, build/export failure paths) | every `result.json` verdict = `cases.json` `expected_official` |
| `threads` | rh-mid honest export (`$BENCH_INPUTS/rh-mid`) + 2 rh-mid mutants (first / last theorem outside the challenge, value := its own type; `mk_thm_mutant_spec.py`) + 3 cmpx cases | `check-sound.sh` at 1 / 32 / 128 / 255 / 256 / 384 threads | identical exit codes (0 or 1) for every case across all thread counts |

Output: `OUT/<gate>.tsv` (one row per run: exit codes, seconds, status PASS/WARN/FAIL, classes, reason line) and
`OUT/summary.json`; exit 0 iff no FAIL row. FAIL classes: `FAIL-CRITICAL` (a reject-labelled case accepted),
`FAIL-REJECT` (the official-kernel leg rejects a test the official kernel accepts: the leg is not the official replay).
WARN classes (availability, never soundness): declines, false rejects of accept cases, second-kernel declines.

Usage:
```
gates.py --out DIR --check fastverify/check/sound/check-sound.sh --legs legs/sound-pinned.json --gate arena --gate suitex --gate cmpx
gates.py --out DIR --check ... --gate mathlib                       # needs the corpus: mk_mathlib_corpus.sh
gates.py --out DIR --check ... --gate mutants --inputs inputs-mutants-host1.json --jobs 2 --threads 96
gates.py --out DIR --check ... --gate threads --inputs inputs-threads.json
```
On a 384-thread AMD host with the authoritative suitex/cmpx copies: `bash amd_gates.sh LABEL
[arena suitex cmpx threads mutants]` (uses the deployed package's check-sound.sh and pins).

**Extra veto kernels (check-sound v2.3-H).** Both extra kernels are opt-in, so the script
suites (`cmpx`, `mathlib`, `mutants`, `threads`, `mathlib-e2e`) run the two-kernel judge by default; add
`--check-args "--kernel con-leche"` and/or `--check-args "--kernel nanoda"` to include them. The kernel-only corpora (`arena`, `suitex`) take the extra kernels from the legs file's optional `"extra"` map
(`legs/sound-pinned-extra-kernels-conleche.json`, `legs/sound-pinned-extra-kernels-both.json`; `{kjobs}` = min(threads, 64), nanoda's
`"config"` = the JSON check-sound.sh writes, path `{config}`); each extra run is classified by the check script's own
classifier (`--xk-classify`), the combined verdict is ACCEPT iff both legs accept and no extra kernel rejects, an extra
kernel rejecting a good test both legs accept is `WARN(xk ... rejects good)` (availability), and the per-test statuses are
in the `xk` column.

A legs file describes the kernel legs exactly as the check script runs them (placeholders `{export}`, `{threads}`):
`{"lean": {"argv": [...], "env": {...}}, "k2": {"argv": [...], "env": {...}}, "ro": [paths to bind read-only]}`.
`{here}` = this directory (the shipped `legs/empty.hints` is the empty hint file of the plain replay). `legs/sound-pinned.json`
= the current pins (pleanchecker 53957eed, gruszka ece04e74).

## Further tools (all in `tools/`)
| tool | what |
|---|---|
| `mathlib_e2e.sh OUTROOT LANES [PRESET] [fastverify args...]` | the 19 Mathlib-differential cases END TO END through `bin/fastverify` (default `--preset sound`; extra args e.g. the final run's `--unsafe ...` list and `--overlap-targets ...`); `FV_UNDER_TEST` = the (frozen) package |
| `mk_r2_specs.py EXPORT CHALLENGE OUTDIR` + `r2_run.sh PKG OUTROOT` | 12 one-edit kernel-level mutation classes (theorem->axiom, universe params dropped/swapped, recursor rule rhs / K flag, constructor fields, inductive isRec, duplicate declaration, projection index, universe instantiation, binder info, wrong primitive definition), labelled by the OFFICIAL comparator, then judged by `check-sound.sh` (also usable through `--gate incr`: `inputs/r2-incr-host1.json`) |
| `incr-server-args.sh` | `overlap/incr-server.sh`'s sandbox + extra pleanchecker args (`--targeted=FILE`); `GATE_SERVER_NO_THP=1` for hosts with fragmented memory |
| `attach_attack.sh PKG WORKDIR` | adversarial test of the `--incr-dir`/`--attach` protocol from a build-like sandbox (forged answer file, injected requests, garbage; `A3_EMPTY_LINE=1` = the empty-line case) |
| `audit_result.py RESULT.json [PINS.env]` | audit of a measured run: verdict/trust/exit, challenge pin, every recorded check binary = the tested pin, warnings |
| `mk_thm_mutant_spec.py`, `mk_def_swap_spec.py`, `mk_del_spec.py` | spec generators for the rh-mid mutants (value := type, definition value swap, deleted declaration) |

## Re-running a suite later (inputs)
`inputs/*.json` are the exact inputs of the recorded runs and contain the absolute paths of the original work machines. The
corpus paths map to `$BENCH_INPUTS/<name>` (rh-mid, rh-miniF, arena, suitex, cmpx); the work-dir copies of the mutants, the
honest RH export and the Mathlib corpus no longer exist. To re-run a suite that used them, re-make them (work dir
`$W` = `$SOUND_GATES_WORK`, default in `tools/common.sh`) and rewrite the paths (`OLD` = the recorded work-dir prefix in
`inputs/X.json`):
```
tools/mk_midmut.sh                                    # rh-mid mutants midM1/midM2 -> $W/midmut (threads suite)
tools/mk_rh_mutants.sh HONEST_RH_EXPORT $W/rh-mut     # M1-M4 with the published sha256 (checked); XFS reflinks advised
tools/mk_mathlib_corpus.sh $W/mathlib                 # Mathlib corpus -> inputs key "mathlib" = $W/mathlib/corpus
fvmut (tools/fvmut.cpp) RHMID_EXPORT OUT specs/<name>.spec   # any other rh-mid mutant of specs/ (midDel*, midNatSubAdd, r2/*)
sed "s#$OLD/midmut#$W/midmut#g; s#$OLD/rh-mut#$W/rh-mut#g; s#$OLD/rh/#/PATH/OF/HONEST/#g" inputs/X.json > my.json
```
The honest RH export = the official / `--preset default` export of the RH tree (sha256 5ea74b91...be244e; the
mutant specs M1-M4 are byte offsets into exactly that file - a `--preset sound` run with merge exports a different file). Always test a frozen copy of the package (`tools/snapshot_pkg.sh`), never a tree that may change during the run.
