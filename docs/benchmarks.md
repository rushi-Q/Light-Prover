# Benchmarks

Headline measurements of Light-Prover against the official Lean toolchain, with their setup and caveats. Light-Prover
verdicts below come from the sound judge described in the [soundness model](concepts/soundness.md) unless the basis
column names another source (the official comparator); the official flow is the official
`lake build`, the official exporter and the unmodified official `lake comparator`.

## How to read this page

- **Status.** *proven*: the measured component is in the package (default or opt-in), reviewed, tested and measured as
  stated (stable in v0.1). *staged*: built and tested, not on a live path. *experimental*: one exploratory run, a
  self-labelled corpus or a model-judged study, or a component labelled EXPERIMENTAL in v0.1 (the incremental machinery,
  theorem inference of the HTTP API); guidance, not a claim. *historical*: measured on an earlier
  pin set or integration; kept for reference.
- **N.** Unless a range or N is given, a number is one run on the named machine. Medians are over the stated runs.
- **Machines.** *Server A*: x86-64, 384 hardware threads. *Machine B*: x86-64, 224 hardware threads.
  *Machine C*: x86-64, 208 hardware threads, shared with other jobs (two runs of the same judge there took 1,584.8 s and 1,086.6 s). On machine B most budget runs ran inside a cgroup-v2 scope (`memory.max`, swap off). Memory is the cgroup peak unless stated.
  Memory budgets and cgroup limits are binary quantities (GiB) even where they are written "GB"; export sizes are
  decimal GB.
- **Method.** Numbers from before the v0.1 measurements, unless marked *(not recomputable)*, were recomputed from their
  raw per-run rows by a person who had not produced them, and kept only if the recomputation matched. The v0.1
  measurements (marked v0.1) are copied by a script from each run's own result file; the run records are
  not part of the repository. The benchmark harnesses are under [`fastverify/bench/`](../fastverify/bench/),
  the soundness gates under [`fastverify/tests/sound-gates/`](../fastverify/tests/sound-gates/). Rows marked
  *(not recomputable)* were checked only against machine-local run files that were never part of the repository.

## Riemann Hypothesis proof, end to end

Input: the published Lean 4.33.1 proof of the Riemann Hypothesis (175,187 modules, Mathlib 0df444a), its clean challenge
(five target theorems; permitted axioms `propext`, `Quot.sound`, `Classical.choice`) and a 61.6 GB export of the
targets' closure. All runs on server A (384 hardware threads): the Light-Prover runs had the whole machine
(a pre-release snapshot of the package with the same judge binaries and judge scripts as v0.1, and the inputs verified
by sha256 before each run); the official comparator runs shared it with other jobs. On the released package (v0.1.0
code), one run: 1,798.7 s total (build 1,346.5 s, export 25.1 s, judge 414.8 s), ACCEPTED. Memory: the `--preset sound`
runs peaked at 425.2-457.6 GiB and the released-package run at 471.6 GiB (cgroup memory.peak, including the 61.6 GB
export on tmpfs).

| flow | time to a verdict | basis | status |
|---|---|---|---|
| official pipeline: build 5,222 s (official `lean` per module under the package's scheduler, a proxy for `lake build`) + official export 5,306 s + unmodified official `lake comparator`, Lean-only configuration, 189,899 s | about 55.7 h (about 56.8 h with the full comparator configuration) | official | measured, N=1 |
| `--preset sound` without module merging (export byte-identical to the official one) | 2,029 s | sound | measured, N=1 |
| **`--preset sound`, pre-release snapshot with the v0.1 judge** (fast build B3 in every run) | **median 1,811.9 s** (runs 1,825.3, 1,811.9, 1,796.5 s; medians: build 1,338.1 s, export 25.3 s, judge 437.5 s) | sound | measured, N=3, all ACCEPTED |
| `--preset sound-auto`, same snapshot | 1,816.3 s (build 1,337.3 s, export 25.1 s, judge 415.0 s) | sound | measured, N=1, ACCEPTED |

The official verdict on the export byte-identical to the original-Lean export:

| official run | result |
|---|---|
| unmodified `lake comparator`, Lean-only configuration | ACCEPTED in 52 h 44 min 59 s ("Your solution is okay!", exit 0; `lake` process max RSS 86.9 GB, the kernel process was not measured) |
| unmodified `lake comparator`, full configuration (statement comparison + nanoda + Lean kernel) | ACCEPTED, whole run 53 h 50 min 35 s (exit 0; `lake` process max RSS 86.9 GB, the kernel process was not measured) |
| the same, second run, on the byte-identical export of the package's `default` preset | ACCEPTED in 53 h 50 min 9 s (193,809 s, exit 0) |
| official `leanchecker`, only `MIMALLOC_GENERIC_COLLECT=1000000` added (kernel replay only) | ACCEPTED in 13 h 12 min 43 s (47,563 s; 45,407 CPU-s) |

Setup notes: the official build is the official `lean` per module under the package's direct scheduler, a proxy for
`lake build`, which was not run to completion (the proof's authors report 6 h 58 min on 128 hardware threads); the official
comparator runs shared the server with other jobs, so 200,427 s / 1,811.9 s = 110.6x uses an upper bound (72-91 % of
their CPU went to the allocator's periodic heap collection); against the official `leanchecker` with only
`MIMALLOC_GENERIC_COLLECT=1000000` added (47,563 s) the judge ratio is 108.7x and the end-to-end ratio 58,091 s /
1,811.9 s = 32.1x, but that run replays the kernel only, without the comparator's statement and axiom comparison (about
85 s inside Light-Prover's judge), and the `lake comparator` with that setting has not been measured yet (a run is
planned); the official comparator starts its kernel with a cleared environment, so an allocator setting cannot be passed
to it by ordinary means, which is why that baseline runs `leanchecker` directly; the build items of `--preset sound` were tuned on earlier
runs of this proof; the Light-Prover total includes about 12 s of preflight and preparation, and the two sha256 stages
run beside the judge; the export of `--preset sound` differs from the official one by construction (merged modules),
and the run without merging is byte-identical to it (sha256 `5ea74b91…`, 61,570,595,788 bytes).

## Judging an export by machine budget

The judge alone on an existing export (export-in). Riemann Hypothesis export (61.6 GB), the v0.1 judge binaries, server A. Each run in its own cgroup scope whose CPU set gives the stated number of threads; the judge's wall
time includes its private copy of the export (about 16 s). Memory is the cgroup's `memory.peak` (includes the page
cache of that copy) and the sampled anonymous memory.

| setup | judge | result | status |
|---|---|---|---|
| 384 threads (whole server) | sound | median 423.2 s (424.5, 421.9 s), N=2; memory.peak 364-382 GiB, anonymous up to 309 GiB | proven |
| 192 threads (one socket) | sound | 503.9 s, N=1 | proven |
| 192 threads (one socket) | notary | 556.6 s, N=1 | experimental in v0.1 |
| 64 threads (32 cores of one socket) | sound | 827.1 s, N=1; memory.peak 276.58 GiB, anonymous 211.38 GiB | proven |
| 32 threads, 128 GB cgroup limit | low-memory | 1,297 s, ACCEPTED (run concurrent with its four mutant checks; memory.peak 111.8 GiB, page cache included; mutants REJECTED: M1 223 s, M2 1,120 s, M3 120 s, M4 113 s) and 1,589.0 s, ACCEPTED (another run with the same binaries, concurrent with five other runs; memory.peak 128.00 GiB, the cap); 0 OOM kills | proven |
| 24 threads, 64 GB cgroup limit | ultra-low-memory (`pleanchecker_lowmem` d27c3bdd) | 4,265.6 s, N=1, ACCEPTED; memory.peak 62.2 GiB (page cache included; cap 64 GiB). Mutants: M1 REJECTED in 4,472.6 s (memory.peak 61.1 GiB), M2 REJECTED in 17,496.4 s (memory.peak 61.1 GiB), M3 REJECTED in 110.0 s, M4 REJECTED in 111.1 s (memory.peak 14.0 GiB each); all within 64 GB. Machine B, same pin, threads and limit: 7,497 s, ACCEPTED; M1-M4 REJECTED within 64 GB | proven |

Concurrency (separate CPU sets; shared disk and fabric): the 384- and 192-thread sound runs had their CPUs to themselves;
the 64-thread run ran alongside the memory-capped runs; the notary run ran alongside another memory-capped run. The
ultra-low-memory honest run ran alongside a mutant check of the same judge on another CPU set and two single-threaded
official-comparator runs on separate cores. The low-memory row is the judge as shipped
(`ccmp_lowmem` da4b77b0, `pleanchecker` 53957eed, `gruszka` ece04e74): the honest export and the four mutants ran
concurrently on server A, each in its own 128 GB cgroup with 32 threads; during the first ~10 min the server also
served the export files to other machines.

### Machines compared

The sound judge on the same export at 192 threads, v0.1 judge binaries, on three machines. A and B have AMD processors, C
has Intel processors; the verdicts were identical on all three (the honest export and the four mutants M1-M4, with the
same messages):

| machine | hardware threads | judge only, honest export | from sources, `--preset sound` |
|---|---|---|---|
| server A | 384 | 503.9 s, N=1 | median 1,811.9 s at 384 threads, N=3 |
| machine B | 224 | 1,315.9 s, N=1 | not measured |
| machine C | 208, shared | 1,584.8 s (first run) and 1,086.6 s (second run), N=2 | not measured |

Machine C was memory-contended in both runs: other jobs held most of its memory as page cache and only 39 GB was free on
part of the machine; the first,
slower run spent 404.2 s in the comparison leg's parse (127.6 s in the second).

Smaller exports (machine B unless marked, cgroup limit and wall time, one run per cell):

| export | sound judge | low-memory judge | ultra-low-memory judge |
|---|---|---|---|
| rh-mid, an 11,371-module part of the proof (1.10 GB), 16 threads | 6 GB: 32.2 s | 3 GB: 51.3 s | 1 GB: 291.3 s (machine C, 2 threads) |
| all of Mathlib (6.07 GB), 16 threads | 24 GB: 159.6 s | 12 GB: 175.7 s | 8 GB: 484.0 s (machine C, peak 7.94 GiB) |

Below its memory floor every run ended DECLINED: 10 of 10 capped runs of the default judge and 36 of 36 of the low-memory
judge. No OOM kill became a verdict. A fitted model of the default judge's peak, about 3.64 x export size + 46 MB x
threads + 1.24 GB, is guidance only (experimental).

## Pull requests and CI

In v0.1 the incremental entry points (`fvwork serve --check sound`, `fv verify --incr-base`, `tools/incr/incr-reverify.sh`)
take the cold sound path: every request is a fresh build, export and trusted check of the submitted tree, so a commit costs
about what a cold run of the project costs. The incremental machinery is EXPERIMENTAL and opt-in
(`--experimental-incremental` of `fvwork serve` and `incr-reverify.sh`; `bin/fv` has no such option), and nothing it
yields is counted. Per-commit and per-push latencies measured with it before the release are therefore not published for
v0.1.

## Other projects

Measured with the v0.1 judge binaries on a pre-release snapshot of the package. Official flow against Light-Prover end to end from sources, both flows on
the same CPUs (6-100 per flow, per row in the table; on machine B or machine C; for the 4 new
openai/math challenges 100 per flow for VPVNP and LinearProgramming and 24 for Hirsch and MatrixExponent), dependencies (Mathlib cache and other
packages) prebuilt in a shared workspace and counted in neither time, one run each unless noted. "Official" is the project release's
own judge: `lake comparator` of the release, or for releases before 4.35 the comparator and `lean4export` of that release.
ACCEPTED means the Lean proof proves the named challenge statement from the permitted axioms; whether the statement
matches the paper was not checked.

| set | CPUs per flow | what was run | verdicts | ratio official / Light-Prover |
|---|---|---|---|---|
| mathematics, about 45 public repositories | 6-56 (most projects 50-56; AxiomMath single-paper batches 28 or 6) | 78 claims: the projects' own `comparator.json` where present (PFR, Carleson, about 60 AxiomMath single-paper challenges on Lean 4.28-4.36), otherwise challenges on the main theorems (sphere-eversion, PrimeNumberTheoremAnd, Foundation, con-nf, flt-regular, Equational Theories, IMO 2026, FLT, sphere packing) | 77 of 78 agree (75 ACCEPTED and 2 REJECTED by both); 1 disagreement: Equational Theories, ACCEPTED by the official comparator and REJECTED by Light-Prover when given the old-format challenge export; Light-Prover ACCEPTED it with a 4.36-format challenge export ([limitations](limitations.md)) | summed over the 77 agreeing claims 34,403 s against 18,497 s = 1.9x; median claim 1.2x (small single-file challenges are dominated by Light-Prover's fixed cost of about 20 s); flt-regular 367.75 s against 59.6 s (6.2x), sphere-eversion 291.24 s against 141 s, PFR 193.04 s against 105.7 s (1.8x) (flt-regular and PFR: Light-Prover on the released package, two runs each, 59.6 / 59.7 s and 105.7 / 105.6 s, on another host of the same type that was also running other jobs; official time from the earlier run; the earlier paired run, 79.1 s and 104.6 s, judged these Lean 4.37.0-rc1 projects with the 4.36 judge, which v0.1 refuses, so it is not v0.1 behaviour); smallest ratio among the 77 claims 0.6x (AxiomMath BerkovichUncu, 32.27 s against 51 s), PrimeNumberTheoremAnd 520.02 s against 303 s, Carleson 263.03 s against 166 s |
| mathematics, judge only on official exports | 54 (FLT), 100 (CFSG) | FLT, whole environment (721,265 declarations); StacksCore (the human-reviewed tier of the Stacks formalization, 445 modules); a 19,422-module sub-closure of AxiomMath/CFSG | all agree (every declaration accepted; StacksCore and the CFSG sub-closure ACCEPTED) | FLT: official `leanchecker --from-export` 4,303 s against Light-Prover's kernels 101 s + 11 s (54 threads); StacksCore: comparator 180 s against 66 s; CFSG sub-closure: comparator 5,687 s against 467 s (100 threads) |
| code verification, 9 projects, 15 challenges | 50-56 | Cedar, Aeneas examples, SampCert, Strata, ArkLib, cslib, lean4lean, LNSym, clean (zk circuits) | every verdict Light-Prover gave equals the official one; no Light-Prover verdict on one clean challenge (second kernel, see [limitations](limitations.md)); SampCert as distributed: the official sandbox cannot run its `g++` build step (REJECTED), Light-Prover ACCEPTED | from 0.6x (LNSym on a shared host, 151.1 s against 249.1 s; 0.7x in a rerun on another host, 91 s against 134 s; Light-Prover slower) to 1.5x (SampCert, 126 s against 195 s); Aeneas 1.0x (212 s against 214 s), lean4lean 1.1x, cslib 1.3x, Cedar 1.3x, Strata 1.4x, ArkLib 1.5x |
| openai/math comparator challenges | 8 (export-in judge); 24 or 100 for the 4 new challenges | 413 challenges judged export-in on the exports the official comparator judged, 22 of them also from sources, and 4 new large challenges from sources | 413 of 413 and 4 of 4 ACCEPTED by both; 22 of 22 from sources agree; no Light-Prover verdict on 2 new challenges the official comparator accepted and on 2 whose official run had not finished (second kernel, see [limitations](limitations.md)) | per challenge, the Light-Prover judge on the official run's exports (8 threads) median 31 s against 255 s for the official comparator run on the prebuilt tree including its two exports (412 timed); the 4 new challenges end to end: 4,551 s against 6,325 s (1.4x) |

On most of these projects the build stage is the official build (the project is outside the fast-build shapes of
[which build runs](reference/options.md#which-build-runs), or on a release other than 4.33.1, 4.36.0 and 4.37.0-rc1),
so the gain comes from the export and the judge. Not judgeable as distributed:
projects on Lean 4.25 or earlier (refused), projects with path dependencies (refused), and repositories that need
generated files that are not in the repository.

## Correctness evidence

Status: proven. Details of the trust argument: [soundness model](concepts/soundness.md).

- **Crafted exports against the official comparator.** 27,099 crafted export files (structure-aware fuzzing with 52
  operators on Init and Mathlib bases, kernel-level proof mutations, Mathlib-scale and real-project mutations, targeted
  seam cases) were judged by the judge and by the unmodified official comparator: **0 accepts of an export the official
  comparator rejects**, after the fix of one critical defect (below). The second kernel alone would accept 1,787 of
  13,517 official rejects in the fuzzing campaigns; the judge accepts none.
- **From sources.** About 5,800 whole-pipeline runs from sources (small proofs, real projects, a cheating corpus, source
  mutants, synthetic shapes, Mathlib as the project) and 3,000 batch attempts: 0 accepts of anything the official flow
  rejects. The only extra accepts are valid proofs that the official *build* rejects for its own reasons.
- **Cheating corpus.** 65 cases (50 cheats, 15 controls) through 4 presets, repeated: 1,355 runs, 0 false accepts.
  Naive verifier configurations accept up to 45 of the 49 cases the official flow rejects.
- **Known kernel bugs.** Exports shaped after Lean issues #16489, #15100 and #15101: no ACCEPTED on any trusted path
  (87/87). The official `lake comparator` accepts 6 of them; the official-kernel leg alone accepted 7 before the
  replay driver's veto checks were added, when only the second kernel rejected them; with them the official-kernel
  leg rejects all of them as well.
- **Judge variants against the default judge.** Randomized differentials: low-memory 802 inputs, ultra-low-memory 777,
  notary 777, the 4.37 judge 777, frontier 39 crafted cases and 6 real states: 0 verdict differences
  that matter (the notary judge rejects 25 malformed exports where the default judge gives no verdict).
- **A fixed race in the judge.** The judge's legs once read the export file independently, so a writer that rewrote the file
  during the check could make it accept a file that never held a proof (3-6 of 40 race runs). This was reachable only for
  a submitted export the submitter could still write, never from sources; the official comparator has the same
  multi-read design (13 of 40). Fixed by judging a private copy with a change stamp: 0 of 40 after the fix.
- **Service level.** One service bug let concurrent batches share a fallback export file, so an attempt could be judged
  on a sibling's export and a per-attempt reward could be wrong; the judge itself was unaffected. Fixed; every published
  service number was re-examined.

What this evidence does not cover is listed under [limitations](limitations.md#assurance).

## Compressed Riemann Hypothesis proof

Post-hoc tools shrink and document an accepted proof; every candidate is rebuilt from its own sources and judged against
the unchanged official challenge, so no compression tool is trusted. Two candidates against the original: C4 (rule-based
transformations) and A3r (the same transformations plus model-written proof rewrites, composed through a git train ledger):

| | original | C4 | A3r |
|---|---|---|---|
| files (modules) | 175,187 | 119,471 (-31.8 %) | 115,830 (-33.9 %) |
| lines | 17,374,215 | 15,403,774 (-11.3 %) | 14,516,021 (-16.5 %) |
| non-whitespace characters | 761.7 M | 624.8 M (-18.0 %) | 593.3 M (-22.1 %) |
| source declarations | 1,065,592 | 891,084 (-16.4 %) | 837,595 (-21.4 %) |
| export size | 61.57 GB | 61.44 GB (-0.2 %) | 61.24 GB (-0.5 %) |
| verdict against the official challenge | ACCEPTED | ACCEPTED | ACCEPTED |
| `--preset sound` from pristine sources (server A) | 1,831.0 s (paired with C4); 1,866.8 and 1,814.0 s (A3r session) | 1,678.8 s (-8.3 %, paired) | 1,951.6 s (+6.0 % vs the mean of the two; build -14.4 %, check +73 %) |

In both candidates the statement closure (5,344 declarations) is unchanged. For C4 the judge time stays flat because the
export is the proofs.
Status: tools proven. A3r verifies more
slowly than the original although it builds faster: two automated shortenings close goals with `rfl` and become single
kernel jobs of 521 s and 387 s. The lesson for compression tools: check each shortened proof's kernel replay time (the
parallel kernel replay reports per-declaration times with `PCHK_SLOW_MS`). The proof and its compressed versions are not redistributed.

## Reproducing the Riemann Hypothesis runs

**Inputs.**

1. The project (175,187 modules, `lean-toolchain` v4.33.1, Mathlib 0df444a), published by its author, Levent Alpöge, as
   the archive `https://alpo.ge/lean.tar.gz.part01` to `part14` (announcement: https://alpo.ge/remark.pdf). The community
   repository https://github.com/leanprover-community/riemann-hypothesis starts its 4.33.1 history at commit 40e56bab,
   which is byte-identical to the pristine sources. The scripts expect it at `$LIGHT_LEAN/alpoge-rh/lean` unless
   `RH_PROJECT` is set.
2. Its clean challenge, at `$LIGHT_LEAN/verify/challenge` unless `RH_CHALLENGE` is set: `Challenge.lean` with the five
   target statements, `comparator.json`, `comparator.nanoda.json` and `comparator.leanonly.json`, `lean-toolchain`
   v4.33.1, `.lake/packages` with Mathlib 0df444a and its dependencies at exactly the project manifest's revisions, and
   `challenge.export` (with `.sha256`) made by the official exporter. `tools/rh-sound.sh` pins the challenge export of
   the published runs (sha256 `3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d`) and its
   `comparator.json` (sha256 `d419c0d8cd8696eb6c3ebc01deb500038fb5820f04c6edc2b1b4ec24673b84c0`); for a challenge built
   from a different `Challenge.lean`, call `fastverify/bin/fastverify ... --preset sound --challenge-sha256 HEX
   --comparator-sha256 HEX` directly.
3. Optional: `RH_REF`, an independently produced original-Lean export of the same project, for a byte comparison.
4. Host: `vm.max_map_count` of at least about 192,000 (the project's main module imports every module), and memory for
   the judge as in the tables above.

```bash
fastverify/tools/rh-sound.sh OUT [THREADS]
# = fastverify/bin/fastverify $RH_PROJECT $RH_CHALLENGE OUT --preset sound --threads THREADS --no-build-fallback \
#     --challenge-sha256 3cf404f4…b91d --comparator-sha256 d419c0d8…84c0 [--export-dir /dev/shm] [--reference-export $RH_REF]
```

Expected: `verdict` ACCEPTED, `trust` sound; the script prints the verdict, trust basis, export sha256 and stage times.
For large runs follow [large runs](large-runs.md).
