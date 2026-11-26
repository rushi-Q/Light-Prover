# fastverify regression suite

One regression test per numbered finding (`NNN-slug/`, NNN = the finding number; the one-line description is the
`# finding:` line of its `test.sh`), each re-running the finding's own reproduction (`NNN-slug/x/`)
against the **delivered package** and comparing with the **official flow**, plus generality tests (`lake-config`:
Lake-configuration variants, `challenge-config`: a non-RH challenge configuration, `odd-layouts`: odd but valid source
layouts, `challenge-variants`: comparator.json shapes: enable_nanoda, definitions-only, nested modules, unicode/escaped
names, no Quot), a bench test on real RH code (`rh-minif-export`, heavy: rh-miniF through the package vs the original-Lean
reference export) and the stage component tests (`stage-checkb-wrapper`, `stage-prechk`, `stage-export`, `stage-build`,
`build-artifacts-identity` (heavy: fast build vs official `lake build` artifact byte-identity on every finding project),
`orchestrator-package` (bin/fastverify orchestration), `lean436-projects`, `checkb-definition-names` (check B on comparator
definition_names), `build-merge`, `build-zygote`, `build-j1-hints`, `build-importarts-empty` (sound-mode build items),
`retired-checka` (the retired check A options are refused)). `run_all.sh` runs the numbered tests and these suites (the
`SUITES` list at its top). [INDEX.md](INDEX.md) lists all
tests (kind, severity, what is checked, cases); `run_all.sh` writes the TSV of every suite run (+ run metadata JSON
with the package snapshot digest) to `results/`.

## Sound mode and its trusted check

The soundness test sets for every trusted piece of the sound check (`check/sound/`, `overlap/` incremental leg) live in
`sound-gates/` (own harness `sound-gates/gates.py`, not part of `run_all.sh`; README there; run records are not shipped); the unit cases of `check-sound.sh` are `check/sound/test/run.sh` (incl. 13 cases for the
leg-scoped verdict of check-sound v2: fake judge lines / stack words from a kernel leg, the real deep-recursion format, a
second kernel printing the judge's lines, `--keep-config-kernels` legs, the > 4 GiB copy/link rule; the v1 script fails 8
of them). The untrusted sound-mode build items have their own component
tests in `build/test/` (each prints PASS/FAIL rows and `RESULT: PASS|FAIL`; no Mathlib, ~1-2 min): `premiseoff.sh` (header
parser, premise-off metadata + eligibility, lean-path-order, sound-fast-path, cost-hints, check-tail), `merge.sh`,
`zygote.sh` (the zygote toolchain part runs only on a host whose glibc can start the zygote toolchain), `crash-retry.sh`,
fast-exact rows in `build/test/run.sh`.

## Generality, correctness and frontier

`smallproofs`, `batchverify`, `incr-reverify` + `seam-sandbox`, `cheat-bench-quick` (wrapper around
`cheat-bench/test.sh` quick; the full proof-cheating benchmark, its generators, the naive-verifier comparison and every
recorded table are in `cheat-bench/`, README there), `shapes`, `confirm-reject` + `build-j1-hints` +
`build-importarts-empty`, `exe-dep-readonly` + `escaped-package-name`
, `export-fuzz/` (export-level fuzzing, seams, a TOCTOU reproduction). Cases
per suite: [INDEX.md](INDEX.md).

## Other Lean releases and many claims

`other-releases` (projects on other official Lean releases via `tools/addrelease.py` - reference vs sound verdicts and
export identity on core cases, refusal of releases <= 4.25), `multi-claims` (`tools/claims.py` - many comparator
claims of one project with one untrusted build, per-claim official export + export-in sound check).

## Daily production use

* **Conditional verdict modulo the sorry frontier:** `frontier-conditional/test.sh [--quick] [WORK]` (~4 min, no Mathlib;
  official Lean 4.36 + its exporter): 18 Init-only cases (incl. 3 proof sketches) x {fast preparer scan, Python preparer
  scan, `check/frontier/check-frontier.sh` end to end}, allowed lists (private lemmas by source spelling, blockers named),
  pinned frontier, blueprint-style challenge with a sorried helper, an open lemma inside a target statement's closure named
, redirect keeps the open lemmas theorems, ledger proved / dropped / drift checks, `--a-cache` (hit, bad
  record, group access, forged C' with a populated cache), and LYING preparers (forged frontier challenge, target smuggled
  into the frontier, dropped lemma, permissive configs).
* **Conditional-verdict construction + real-history replays:** `../tools/frontier/test/run.sh [WORK]` (WORK, or a
  directory under `$FV_SCRATCH`, outside `/tmp`, `/home`, `/var`, `/run`; ~5 min, no
  Mathlib; official Lean 4.33.1 build/export via `bin/fastverify --preset sound`): 14 source cases, the pinned flow and 4
  fault injections of the construction behind `check-frontier.sh` (24 rows); `../tools/frontier/test/run437.sh [WORK]`
  (~3 min): the same 24 rows on Lean 4.37.0-rc1 through the production path `bin/fastverify --pins
  check/sound/pins-437.env --modulo-frontier`, + 3 `check-frontier.sh --axioms` rows (27; needs the 4.37 judge binaries on
  the host).
* **Isolation of shared verifiers:** `fvguard/` (unit test of `tools/guard/fvguard.py`: 20 bounded probes - every
  limit, honest exit codes, orphan kill, library API - plus the cgroup backend where a cgroup runner is available;
  no Lean, ~40 s) and `service-guard/` (heavy, ~8 min: 6 bounded resource probes + 10 honest attempts through
  `tools/batchverify.py --limits` and `tools/fvserve --limits` with the fork server; probes NO-VERDICT or refused by the
  sandbox, honest ACCEPTED, no leftover fork child, `--max-pending`, `--request-timeout`, slow lane,
  fork-server restart, stale export dirs, `--fair` / `--max-pending-per-client`, linger + disconnect, dispatcher
  error path (unit), concurrent honest + cheat siblings on the fallback export path, code/stale report; 12 cases,
  47 rows). Run them directly (`tests/d07-*/test.sh [WORK]`; env `FV_PACKAGES`, `TC433`). `fvserve-437/` (the attempt
  service and batchverify on a Lean 4.37.0-rc1 problem set with `--pins check/sound/pins-437.env`: 18 attempts must get
  the official 4.37 flow's verdicts; needs `FV437_PACKAGES` = a built 4.37 Mathlib workspace, else SKIP; ~6 min).
* **Resource budgets:** `budget/run.sh` (7 cases, < 20 s, no Mathlib: `lib/budget.py host/estimate/plan`, the fitted
  model inside the measured floors, `bench/budget/{fit,mkreport,summarize}.py` on the shipped results, `frontier.py` on a
  synthetic export, the cgroup runner where available: capped run + OOM kill recorded); `build-kill/run.sh` (3 cases;
  a `lean` of the official `lake build` SIGKILLed 3 s in must give ERROR exit 2, never REJECTED; control run
  ACCEPTED; `enospc-log`: the archived disk-full log excerpt of a real run must be classified ERROR by
  `build/official-build.sh`; ~2 min, needs the Mathlib workspace); `build-jobs/run.sh` (2 cases, ~2 min, no Mathlib:
  the official `lake build` through `build/official-build.sh --threads N` under an N-CPU affinity mask
  must run at most N+1 `lean` processes at once; Lake sizes its pool by the host's hardware concurrency, so without the fix
  a 4-CPU scope on a 224-thread node ran 103 lean processes; synthetic 32-module project, each module ~5 s of `#eval`; env
  `OFFICIAL_BUILD` points the test at a staged script).
* The remaining suites (judge variants, interfaces, compression, other releases) are listed with their current
  counts in [INDEX.md](INDEX.md).

## Running

```
export FV_TEST_WORK=/local/disk/fvtests           # work directory of the runs (or pass --work DIR)
$FASTVERIFY/tests/run_all.sh --jobs 12             # all non-heavy tests (~15-25 min on 96 cores)
$FASTVERIFY/tests/run_all.sh --heavy               # + heavy tests (Mathlib-scale, 044/051 chains, 064, ...)
$FASTVERIFY/tests/run_all.sh 038 066 024           # selected findings (heavy ones included when named)
$FASTVERIFY/tests/NNN-slug/test.sh [WORKDIR]       # one test (prints its TSV rows)
$FASTVERIFY/tests/run_all.sh --standin    # harness self-test: the OFFICIAL flow stands in for bin/fastverify -> all PASS
$FASTVERIFY/tests/run_all.sh --deployed   # e2e tests with the original (attacked) fast flow (fastflow.deployed.sh) -> the divergences
```

Requirements: a host with the official toolchains Lean 4.33.1 and 4.36.0 under `$ELAN_HOME/toolchains`, the official
lean4export pinned in `config/components.json`, bwrap, a node-local work directory (`--work DIR`, or `FV_TEST_WORK`: runs
go to `$FV_TEST_WORK/<stamp>-<label>`; preferably outside `/tmp`, `/home`, `/var` and `/run`, which the kernel sandbox of
the trusted check hides), and the package's binaries installed under their pinned prefix `/scratch/fastverify-next` (test
001 checks that). The official tools the tests compare against are taken from the package's own configuration
(`config/components.json`, regenerated per machine by `tools/configure.py`) by `lib/paths.sh`: `FV_T33` / `FV_T36`
(official Lean 4.33.1 / 4.36.0 prefixes), `FV_OFFICIAL_EXPORTER`, and `FV_PACKAGES` (the trusted dependency workspace,
default: `$LIGHT_LEAN/verify/challenge`, the RH challenge workspace; set it on another machine). Every `x/officialflow*.sh` snapshot reads these
variables (`tools/parametrize.sh`); a few helper scripts of the findings that the tests do not call (deployed-flow variants,
`mkexp.sh`) still carry the original installation's paths.
Knobs: `EVAL_THREADS` (threads per test, default 8), `--jobs`, `KEEP_WORK=1`, `FV_TEST_OFFICIAL=recorded|live`,
`FV_TEST_TIMEOUT` (per test, default 7200 s), `--fv BIN` (entry point to test), `--fv-args '<menu flags>'` (package options
under test, default `--check C3,C0`; formerly `--check both` = C1,C3,C0, refused since check A's retirement),
`--unsafe-run` (options under test are UNSAFE opt-ins), `--no-snapshot`.

Per-option testing (menu of the package): `tools/option_matrix.sh [GROUP...]` runs the e2e and generality tests once per
option (reference, B2, E0, C3, and the UNSAFE opt-ins C4, C4+ignore-order and every B3 build option on the findings it is
documented to break) and writes the matrix to `$FV_TEST_WORK/OPTIONS.md`. Export-level tests exercise every legacy check option (C3, C4) in every run;
rows of UNSAFE variants are named `<case>/C4!unsafe`. (fast-exact, C1 and C2 were retired with check A.)

## Running the test suite on a fresh clone

A row whose input or environment is missing prints `SKIP` with the reason. A SKIP is neither PASS nor FAIL, and
`run_all.sh` exits 0 when no row is FAIL or ERROR. The rows below SKIP or fail on a fresh clone for that reason; none of
them concerns a judge verdict.

| rows | on a fresh clone | what to do |
|---|---|---|
| rows that need the trusted Mathlib workspace: `exe-dep-readonly`, `multi-claims`, the `dependency-mismatch` row of `tests/package` | SKIP | set `FV_PACKAGES` or provide `verify/challenge` |
| parts of `budget`, `ultralowmem-check`, `lowmem-check`, `check437`, `lean-leg-record-checks` | SKIP: they need a cgroup tool, large corpora or RH-scale exports that are not part of the repository | - |
| `001-*` | FAIL if a pinned fast binary is missing or does not start here; a local toolchain copy under the binary prefix that does not start is a SKIP | install the pinned components (`docs/getting-started.md` section 4) |
| the clean-audit row of `cli-mcp` | SKIP without `cargo` on `/usr/bin:/bin` and without a prebuilt `tools/audit/bin/expaudit` | install Rust, or build `expaudit` once |
| `mcp-symlink-paths` | inside a user namespace the `--packages` ownership check sees `/` as owned by another account | run it outside a user namespace |
| the 4.37 rows of `cli-mcp` | need Lean 4.37.0-rc1 registered and a packages workspace | `python3 -I fastverify/tools/addrelease.py --elan-home "$ELAN_HOME" 4.37.0-rc1`, and `--packages` / `FV_PACKAGES` |
| the triage, audit and diff rows of `interfaces` | SKIP without a packages workspace (triage) or without `cargo` on `PATH` (the `expaudit` deep audit, the `expdiff` export diff) | `FV_PACKAGES`; install Rust, or set `EXPAUDIT_BIN` / `EXPDIFF_BIN` |
| the two work-directory rows of `notary` | SKIP when `/var/tmp` is not writable | set `NOTARY_TEST_VARTMP` to a writable directory outside `/tmp` |

Tests that take a work directory default to a new directory under `$TMPDIR` (else `/tmp`); pass one, or set the
variable the test names (`WORK`, `SCRATCH`, ...), to put it elsewhere. The judge unit tests `check/sound/test/run.sh` and
`xk.sh`, and `sandbox-ipc`, need a work directory that the sandboxes still show (they hide `/tmp`, `/home`, `/root`,
`/var` and `/run`): `CHECK_SOUND_TEST_DIR` (or the argument) if set, else `fastverify/tests/.work/` when the clone
itself lies outside those directories, else another visible writable location (`tests/lib/visible_workdir.sh`); they
SKIP with the reason only when there is none. The official exporter must be built where section 3 of
`docs/getting-started.md` puts it (`$LIGHT_LEAN/env/tools/lean4export`).

## Result rows

`id case official_rc fast_rc official_sha16 fast_sha16 result note` (0 = ACCEPTED). `result`:

| result | meaning |
|---|---|
| PASS | same verdict as the official flow and, when both accept, byte-identical export (sha256) |
| PASS-DECLINE / PASS-REFUSED | the fast tool declined / the package refused where the official REJECTS (or a refusal was the expected fail-closed behaviour) |
| WARN-DECLINE | a fast checker declined (exit 2) where the official ACCEPTS: no fast verdict, the official path decides (coverage/speed, not accuracy) |
| WARN-ERROR / WARN-CRASH | the package refused / a fast checker crashed where the official REJECTS (never an accept) |
| WARN-REFUSED | the package explicitly refused (no verdict, fail closed, e.g. a source symlink leaving the project) where the official ACCEPTS |
| **FAIL-ACCEPT** | the fast flow ACCEPTS what the official flow rejects (accuracy violation) |
| **FAIL-EXPORT** | both accept but the exports differ (accuracy violation) |
| **FAIL-REJECT** | the fast flow rejects what the official flow accepts (false reject) |
| FAIL / ERROR / SKIP | other mismatch / the test produced no rows / component missing |

`run_all.sh` exits 0 iff there is no FAIL* or ERROR row. The note column carries the path the package took (`path
build=fast|official export=fast|official checkB=...`), declines, and `DRIFT(...)` when a live official result
differs from the value recorded with the finding (environment change: investigate before trusting that row).

## Test kinds (how each finding is exercised)

* **e2e** (`lib/xrepro.sh`, files `REPRO`, `EXPECT`): `x/` is a snapshot of the finding directory (build products, logs
  and repro outputs dropped). Every `fastflow.sh` in it is a symlink to
  `lib/fastflow.sh`, which runs `bin/fastverify PROJECT CHALLENGE_DIR OUT --check C3,C0` under `env -i` (projects with
  dependencies get `--packages verify/challenge`, the pinned Mathlib workspace that the findings' official flow copies)
  and reports the package's outcome in the findings' format (FAST outcome = ACCEPTED if the final verdict or the
  fast-check verdict accepts). The OFFICIAL side is the finding's unmodified `officialflow.sh` (official `lake build`
  4.33.1 + official lean4export v4.33.0 + `lake comparator` 4.36). `EXPECT` holds the official verdict and export sha
  recorded from live official runs (identical to the values recorded with the findings). Custom e2e tests: 067 (OUT reuse must be
  refused), 066 (reference = `officialflow-clean.sh`: the sources are judged, shipped `.lake/build` artifacts are removed
  - the package does the same), 035 (4 scripts incl. sub-cases a/b/c), 014 (liveness case only with `--heavy`).
* **export-level** (`lib/checkcases.sh`, file `CASES`): crafted or officially built exports. For every case, every fast
  checker `check/*/check*.sh` (official/ and prechk/ excluded) and the entry point (`bin/fastverify - CHALLENGE_DIR OUT
  --export SOL --check C3`, pseudo-checker `fastverify`) are compared with a live official `lake comparator` run
  (`lib/official-check.sh`; values marked `*` in CASES are slow and taken from the findings' records unless
  `FV_TEST_OFFICIAL=live`). Modes cover the glue findings: `path:` (path-substring checks, 002/005), `nochallenge`, `pipe`
  (/dev/stdin, 009), `cwd:` (files in the working directory, 049), environment pollution (016), `rlimit:` (address-space
  limits, 042), `gen:` (inputs generated per run: 044, 051, 071, 009).
* **exporter** (`lib/exportcases.sh`, file `ECASES`): sources compiled with the official Lean 4.33.1 (optionally with
  `-Ddebug.skipKernelTC=true`, i.e. the oleans the old fast build produced), then `export/export.sh --official-fallback` vs
  the official lean4export on the same .olean files: identical bytes or both fail (008 010 013 018 030 033).
* **component** (`lib/component.sh`): scripts printing PASS/FAIL lines (or `RESULT .. PASS|FAIL`, or TSV rows ending in
  PASS|FAIL), run once per suite run and shared between findings. Stage tests (`stage-*`, `build-artifacts-identity`) call the stage scripts' own tests
  (`check/checkB/test/run.sh`, `check/prechk/test/run.sh`, `tests/export/run.sh`,
  `build/test/run.sh`, `build/test/cmp_official.sh` over all finding projects). Finding tests: `tests/toolchain/run.sh`
  (toolchain verifier refusals + the findings' `regress_toolchain.sh` with the package's toolchain: 004 014 020 031 037 040
  046 048 050 052 061), `001-*/portability.sh` (no AMD-only instructions, glibc <= host, libraries resolve, every stage's
  `--preflight` passes on this host), `036-*/degrade.py` (copies of the package with one broken pinned component must
  refuse or not use it; a broken official-toolchain pin must always refuse), 003 (the sound check's Lean leg - check A's
  descendant - vs the official leanchecker on finding 003's inputs; check A's own legs before its retirement), `retired-checka`
  (`tests/package/retired-checkA.sh`: every retired check A option is refused with a message naming the replacement).

## Adding / refreshing tests

* new finding: put its reproduction under `NNN-slug/x/` (repro scripts, crafted projects/exports;
  no build products), replace every `fastflow.sh` in it by a symlink to `lib/fastflow.sh` (keep the original as
  `fastflow.deployed.sh`), run `tools/parametrize.sh`, then write `NNN-slug/test.sh` (copy a test of the same kind) and
  `EXPECT` / `CASES` / `ECASES`.
* `python3 tools/mk_index.py` regenerates the finding rows of INDEX.md (and adds a row for any new test directory); the
  other rows and the severity column are maintained by hand in INDEX.md.

## Known limits

* The official side of a few cases is resource-bound (official build timeouts, stack overflows, nanoda limits: 007, 029,
  044, 047, 050, 051, 064). The recorded verdicts hold on the original test hosts with default limits; on other hosts
  re-run with `FV_TEST_OFFICIAL=live` and check the DRIFT notes.
* e2e tests use the findings' tiny projects; RH-scale behaviour is measured separately (package README, section 5).

## Provenance

* `NNN-*/x/`: the finding directories (inputs and reproduction scripts: repro scripts, crafted projects/exports;
  build products, logs and repro outputs dropped; every
  `fastflow.sh` replaced by a symlink to `lib/fastflow.sh`, the original kept as `fastflow.deployed.sh`; references to
  other finding dirs rewritten to the snapshots; identical exports hard-linked).
* `EXPECT` (official verdict + export sha per e2e case): recorded from live official runs, identical to the values
  recorded with the findings where both exist. `CASES` official values: the findings' records, re-checked live in every run (two
  wrong records were found that way and corrected: 044 depth 2^24-2 and 039 late-sparse, both REJECTED by the official
  comparator with nanoda).
