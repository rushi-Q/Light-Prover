# Command-line reference

Light-Prover has two command-line entry points: `fastverify/bin/fastverify`, the orchestrator with every stage option,
and `fastverify/bin/fv`, the daily CLI that wraps it and the services. Long-running services and the standalone judges
have their own entry points, listed at the end. Workflows are in the [user guide](../user-guide.md); presets and stage
options in [options.md](options.md); output formats in [result-json.md](result-json.md).

Paths are relative to the repository root. `fastverify/bin/fastverify --help` and `fastverify/bin/fv SUBCOMMAND --help`
print the current option list (`fv ci` has no `--help`; its synopsis is below). Run both entry points directly, never as
`bash FILE`.

## `bin/fastverify`

```
fastverify/bin/fastverify PROJECT CHALLENGE OUT
    [--preset sound-auto|sound|notary|reference|fastest] [--experimental]
    [--build B0|B1|B2|B3] [--unsafe OPT,...|all] [--export E0|E1|FILE] [--from-export FILE]
    [--check CS,CN,C0,C3,C4] [--fast-policy primary|any|all]
    [--threads N] [--packages WS] [--comparator-config FILE] [--reference-export FILE]
    [--challenge-sha256 HEX --comparator-sha256 HEX] [--pins FILE] [--check-hints FILE|none] [--check-hide FILE|none]
    [--modulo-frontier [auto|FILE]] [--frontier-pin DIR] [--frontier-base RESULT]
    [--overlap] [--overlap-targeted] [--overlap-targets FILE] [--export-dir DIR] [--notary-kernels LIST]
    [--extra-kernel con-leche|nanoda] [--require-kernel con-leche|nanoda] [--skip-extra-kernel con-leche|nanoda]
    [--confirm-reject | --no-confirm-reject] [--require-sorried-holes] [--no-integrity-cache] [--confirm-build-failure-full] [--build-cache DIR|none]
    [--official-timeout SEC] [--parallel-checks | --sequential-checks]
    [--require-fast] [--no-build-fallback] [--no-confirm-build-failure] [--preflight-only] [--keep-work]
```

Aliases: `--build official` = B0, `--build fast` = B1; `--check official` = C0. Without `--preset`, `--check` is required
(build B1 and export E1 unless given).

**Retired before v0.1 (refused with exit 2 and a message naming the replacement, `--preset sound` / `--preset sound-auto`;
never mapped to another check):** the presets `fast-exact` and `default`, a run without `--preset` and without `--check`
(formerly the implicit preset `default`), `--check C1` and `--check C2` (the legacy judge check A), the aliases
`--check fast` (= C1,C3) and `--check both` (= C1,C3,C0), `--fast-checks`, `--fast-policy checkA` (use `primary`) and
`--unsafe nanoda-c07`. Check A is kept on the branch `archive/checkA`.

| argument | meaning |
|---|---|
| `PROJECT` | the Lean 4 project: sources, `lakefile.toml` or `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` when it has dependencies (a dependency-free project can omit it). Anything under `PROJECT/.lake` is ignored; the project is judged from its sources. |
| `CHALLENGE` | the clean challenge: `comparator.json`, `lean-toolchain`, and either `challenge.export` (with an optional `challenge.export.sha256`) or the challenge sources, which are then built and exported officially. An `export-targets.txt`, if present, must equal the target list Lake's comparator derives from `comparator.json`. |
| `OUT` | the output directory; must not exist or be empty, and must be disjoint from `PROJECT` and `CHALLENGE` (neither inside them nor containing them). Receives `result.json`, `solution.export` and `log/`. |
| `--threads N` | CPU budget for every stage (default: the CPUs in the affinity mask). |
| `--packages WS` | a trusted Lake workspace whose `.lake/packages` holds the project's dependencies at the manifest's revisions (for example a challenge directory after `lake exe cache get`). Default: `CHALLENGE` if `CHALLENGE/.lake/packages` exists. The build has no network. |
| `--challenge-sha256 HEX` | sound mode: the sha256 the challenge export must have. Sound mode refuses a given challenge export without it. |
| `--comparator-sha256 HEX` | the sha256 the comparator configuration must have (the other half of the challenge identity: the configuration decides which statements and axioms are checked, so it is pinned like the challenge). Required wherever `--challenge-sha256` is (sound, sound-auto, notary, frontier with a given challenge export): missing or mismatching, the run is refused (exit 2) before anything runs. |
| `--comparator-config FILE` | comparator configuration (default `CHALLENGE/comparator.json`), given unchanged to every check. |
| `--experimental` | required in v0.1 for the notary check (`--preset notary`, `--check CN`, `--check CS,CN`), which is EXPERIMENTAL. |
| `--from-export FILE` | judge a private copy of an existing export; no solution build or export (the challenge is still prepared, and built officially if only its sources are given). |
| `--reference-export FILE` | compare the produced export byte for byte with a reference (`export.reference.identical`); information only in sound mode. |
| `--pins FILE` | sound mode: the pins file of the judge, a `pins*.env` in `check/sound/` (default `check/sound/pins.env`, the Lean 4.36 judge; `check/sound/pins-437.env` is the Lean 4.37.0-rc1 judge). `sound-auto` and `sound` select the file matching the challenge's release: from the challenge export's meta line when a challenge export is given, otherwise from the challenge's `lean-toolchain`, and refuses before the build if that judge is not installed; an explicit 4.36 pins file, or `--preset notary`, for a 4.37 challenge is refused, so `--pins check/sound/pins.env` cannot force the 4.36 judge on a 4.37 challenge. |
| `--check-hints FILE\|none`, `--check-hide FILE\|none` | sound mode: scheduling hints for the judge's kernel replay (order only) and the 4.37 hide list (availability only). |
| `--modulo-frontier [auto\|FILE]` | sound mode: answer CONDITIONAL (exit 3) when every target follows from the permitted axioms plus the reported open lemmas; with FILE, only the listed lemmas may stay open. |
| `--frontier-pin DIR`, `--frontier-base RESULT` | judge against a pinned frontier challenge (statements cannot drift, no new open lemma); report the status of each open lemma of an earlier result (information only). |
| `--overlap`, `--overlap-targeted`, `--overlap-targets FILE` | sound mode: check kernel jobs during the build. |
| `--export-dir DIR\|none` | prefer a fresh directory under DIR for the export (for example tmpfs); used only when DIR has at least 256 GB free and is not a tmpfs under a memory budget below 512 GB, otherwise the export goes to OUT; removed at the end unless `--keep-work`. |
| `--build-cache DIR\|none` | untrusted per-user cache of the compiled planner and of verification stamps. |
| `--no-integrity-cache` | `sound-auto`: verify every toolchain tree and pinned file in full in every run. |
| `--confirm-build-failure-full` | accepted, no effect in v0.1: a failed transformed build is always confirmed by the full exact build B1 (or B0). |
| `--confirm-reject`, `--no-confirm-reject` | sound mode, on by default in `sound` and `sound-auto`: when the export of a successful transformed build (B3) is REJECTED, build once more exactly (B1, or B0 where B1 declines), export and check again; a confirmation that cannot complete is DECLINED ([options.md](options.md#--confirm-reject)). `--no-confirm-reject` turns it off: such a rejection is then reported unconfirmed (DECLINED). |
| `--require-sorried-holes` | CS / CN: refuse a challenge whose definition hole is not sorried, for releases before 4.37 too (default off; [options.md](options.md#sorried-definition-holes-cs-cn)). |
| `--notary-kernels LIST` | with `--preset notary`: the independent kernels, a subset of `gruszka,con-ron,con-leche,nanoda`; `gruszka` is always run (added if missing), every selected kernel is mandatory. |
| `--extra-kernel NAME`, `--require-kernel NAME`, `--skip-extra-kernel NAME` | sound mode: enable, make mandatory or skip a veto-only extra kernel of the judge (both are off by default); one name per option, repeatable ([options.md](options.md#extra-veto-kernels-cs)). |
| `--official-timeout SEC` | stop C0 after SEC seconds; a timeout is ERROR, never an accept. |
| `--parallel-checks`, `--sequential-checks` | run all checks at once, or each alone with C0 last (default: C0 in the background, the other checks one after another). |
| `--require-fast` | refuse (exit 2) at preflight instead of falling back when a selected fast option is unavailable on this host (runtime declines still fall back). |
| `--no-build-fallback` | stop with ERROR instead of falling back to an exact build when a fast build declines or fails. |
| `--no-confirm-build-failure` | do not confirm a fast-build failure with an exact build: outside sound mode it is REJECTED; in sound mode an unconfirmed failure of the transformed build is no verdict. |
| `--preflight-only` | only verify that every selected component is installed, pinned and starts; prints `preflight OK` (verdict `PREFLIGHT_OK`, exit 0; `PREFLIGHT_INCOMPLETE`, exit 2). |
| `--keep-work` | keep `OUT/work` (the prepared and built project). |

**Exit status:** 0 ACCEPTED, 1 REJECTED, 2 no verdict (DECLINED, ERROR, refused, interrupted), 3 CONDITIONAL (only with
`--modulo-frontier`); 0 also for `PREFLIGHT_OK`. The raw exit 0 is given to an ACCEPTED of any trust, including `official`
(`--preset reference`) and `UNSAFE`: read `trust` in `result.json`, or use `fv`, which counts only the sound family. The
process runs under `env -i`.

## `bin/fv`

`fv` emits the versioned API JSON (`--json`, `--json-out FILE`), SARIF 2.1.0 (`--sarif FILE`) and LSP 3.17 diagnostics
(`--lsp-out FILE`) on the subcommands that produce verdicts.

**Exit status of `verify`, `check`, `attempt` and `watch`** = the envelope's `exit_code`, which depends on the trust as
well as on the verdict ([trust rule](result-json.md#api-envelope-result-v1)): 0 only for an ACCEPTED with trust `sound`,
`sound-conditional` or `notary`; 1 REJECTED; 3 CONDITIONAL; 2 everything else - DECLINED, NO-VERDICT, ERROR, a refused
input, and an ACCEPTED with any other trust. A `--preset reference --allow-unsound-presets` run whose official comparator
accepts therefore reports `verdict: "ACCEPTED"`, `trust: "official"`, `accepted: false`, `reward: 0.0` and exits 2.

### `fv verify` - verify a project

```
fv verify PROJECT --challenge CHALLENGE [--challenge-sha256 HEX --comparator-sha256 HEX]
          [--trust-challenge-sha256-file] [--preset PRESET] [--allow-unsound-presets] [--pins PINS] [--no-integrity-cache]
          [--build {B0,B1,B2,B3}] [--packages WS] [--threads N] [--out OUT] [--export-dir DIR] [--build-cache DIR|none] [--keep-work]
          [--confirm-reject] [--modulo-frontier [auto|FILE]] [--frontier-pin DIR] [--frontier-base RESULT]
          [--incr-base OUT] [--optimistic | --no-optimistic] [--closure-only] [--integrity-cache DIR]
          [--json] [--json-out FILE] [--sarif FILE] [--lsp-out FILE] [--include-raw] [--quiet]
          [--guard SPEC] [--extra-arg ARG]
```

Default preset `sound-auto`. `--pins` accepts `436`, `437` or a path under `check/sound/`. `--incr-base OUT` (with
`--optimistic` / `--no-optimistic` and `--closure-only`) is accepted, but in v0.1 it takes the cold sound path and the
result says so ("incremental mode is experimental in v0.1 and was not used"); the incremental machinery is EXPERIMENTAL
and not reachable from `fv`. `--guard` adds resource limits (for example
`mem=16G,wall=600`). `--trust-challenge-sha256-file` reads the pin from `challenge.export.sha256`; use it only when the
challenge directory is trusted.

`--preset` takes `sound-auto` (default) or `sound`; `notary` is refused in v0.1 because `fv verify` has no `--experimental`
(use `fv check --experimental --notary` or `bin/fastverify --experimental --preset notary`). Any other active preset (`reference`, `fastest`) is refused
unless `--allow-unsound-presets` is given; its verdict is then reported but never counted (an ACCEPTED exits 2).
`--extra-arg ARG` (repeatable; spelled exactly, a value as `=V` or as the next token) forwards only options of an
allow-list that touch the untrusted build and export or scheduling, or make the check stricter: `--threads`, `--build`,
`--official-timeout`, `--extra-kernel`, `--require-kernel`, `--parallel-checks`,
`--sequential-checks`, `--no-confirm-build-failure`, `--confirm-build-failure-full`, `--no-build-fallback`,
`--require-fast`, `--no-integrity-cache`, `--keep-work`, `--overlap`, `--overlap-targeted`, `--require-sorried-holes`,
`--confirm-reject`. Anything else (what is judged, the pins, the deciding check, paths such as `--export-dir` and
`--build-cache`, which `fv verify` takes as its own checked options) is refused before `bin/fastverify` runs.

### `fv check` - judge an export

```
fv check EXPORT (--challenge CHALLENGE | --challenge-export FILE --comparator-json FILE)
         --challenge-sha256 HEX --comparator-sha256 HEX
         [--frontier] [--allowed-frontier FILE] [--frontier-axioms FILE] [--frontier-pinned DIR] [--frontier-base FILE]
         [--low-mem] [--experimental --notary] [--notary-kernels LIST] [--pins PINS] [--guard SPEC] [--threads N] [--timeout S]
         [--json] [--json-out FILE] [--sarif FILE] [--lsp-out FILE] [--include-raw] [--quiet]
```

Default: the sound judge. `--low-mem` selects the low-memory judge, `--notary` the notary judge (EXPERIMENTAL in v0.1, needs `--experimental`), `--frontier` the
conditional check (exit 3 = CONDITIONAL; `--frontier-axioms` lists declared project axioms as hypotheses), `--pins 437`
the Lean 4.37.0-rc1 judge.

### `fv attempt` - one proof attempt through a running service

```
fv attempt FILE --pset PSET --theorem THEOREM [--state FVSERVE_STATE | --http URL] [--api-key KEY]
           [--timeout S] [--json] [--json-out FILE] [--sarif FILE] [--lsp-out FILE] [--include-raw] [--quiet]
```

`FILE` may be `-` for stdin.

### `fv watch` - verify on every save (EXPERIMENTAL in v0.1)

```
fv watch --experimental PATH [--challenge CHALLENGE] [--challenge-sha256 HEX --comparator-sha256 HEX] [--trust-challenge-sha256-file]
         [--fvserve-state DIR] [--no-advance] [--pset PSET] [--theorem THEOREM]
         [--incr-base OUT] [--closure-only] [--integrity-cache DIR] [--preset PRESET] [--no-integrity-cache]
         [--build BUILD] [--packages WS] [--export-dir DIR] [--threads N] [--interval S] [--timeout S]
         [--once] [--max-runs N] [--json-out FILE] [--sarif FILE] [--lsp-out FILE]
```

`PATH` is a project directory (each save runs a cold `fv verify` of it; `--fvwork-state` is refused in v0.1) or a single
attempt file (with `--fvserve-state`, `--pset`, `--theorem`).

### `fv ci` - CI and pull-request gate (EXPERIMENTAL in v0.1)

```
fv ci --experimental --project DIR --challenge DIR --challenge-sha256 HEX --comparator-sha256 HEX --out-dir DIR
      [--cache-dir DIR] [--packages WS] [--preset P] [--pins P] [--no-integrity-cache] [--build B]
      [--export-dir DIR] [--closure-only] [--confirm-reject] [--frontier] [--allowed-frontier FILE]
      [--frontier-axioms FILE] [--frontier-pinned DIR] [--wall S] [--disk BYTES] [--mem BYTES]
      [--threads N] [--commit SHA]
```

Runs `fastverify/tools/ci-action/fv-ci.sh` (also a GitHub composite action, `tools/ci-action/action.yml`). It refuses to
run (exit 2, nothing read or written) without `--experimental` (or `FV_EXPERIMENTAL_CI=1`; action input
`experimental: "true"`). Every run is a cold sound run; both pins are required as full 64-hex values. Default preset
`sound-auto`, default `--wall` 3600 s; in v0.1 `--cache-dir` is ignored (every run is cold) and `--disk` has no effect.
`--fv-root` is refused (`fv ci` always runs this package). `fv ci --help` is not supported; this synopsis lists the
accepted arguments.

### `fv init-challenge` - build and pin a challenge

```
fv init-challenge CHALLENGE_SRC OUT [--packages WS] [--threads N] [--timeout S] [--json]
```

Builds and exports the challenge with the official `lake build` and the official exporter, and prints its sha256.

### `fv doctor` - host readiness

```
fv doctor [--project PROJECT] [--json]
```

Checks bubblewrap, the cgroup memory budget, `/dev/shm` and the pins, and prints the plan `sound-auto` would choose.

### Advisory subcommands (never a verdict)

```
fv audit CHALLENGE [--challenge-sha256 HEX] [--config FILE] [--probe] [--packages WS] [--reading-set OUT.lean] [--conjecture-mode] [--solution-mode] [--json]
fv triage --experimental FILE [--theorem T] [--toolchain DIR] [--packages WS] [--snapshot-dir DIR] [--repo PROJECT] [--static-only] [--timeout S] [--json]
fv lookup [FILE] --index DIR [--name NAME] [--hash HASH] [--targets LIST] [--toolchain DIR] [--packages WS] [--snapshot DIR] [--threads N] [--json]
fv diff OLD_EXPORT NEW_EXPORT [--targets LIST|FILE] [--explain N] [--dead-lets] [--private-modulo] [--threads N] [--timeout S] [--json]
fv mint PROJECT --out DIR [--theorem T]... [--frontier-file FILE] [--module M] [--permitted-axioms LIST] [--packages WS] [--for-fvserve] [--threads N] [--timeout S] [--json]
```

- `audit`: statement-fidelity lints and kernel-certified probes on a challenge; `--reading-set` writes the minimal set of
  non-library statements a reader must check. `fv audit` exits 0 when the audit passed; treat any other exit as "not
  passed" (the underlying `tools/audit/audit.py` exits 0 passed, 1 a finding at or above its `--fail-on`, 2 input error).
  It is advisory and takes no comparator pin.
- `triage` (EXPERIMENTAL in v0.1): static lints and sandboxed probes of a proposed `sorry` lemma before anyone tries to
  prove it.
- `lookup`: does a theorem with exactly this kernel statement already exist in an indexed library?
- `diff`: per-target classification of two exports (identical, alpha-equal, proof changed, statement changed, removed,
  added).
- `mint`: pinned sub-challenges for the open lemmas of a blueprint project; `--for-fvserve` makes them servable by
  `fvserve`.

## Services

| entry point | subcommands | purpose |
|---|---|---|
| `python3 -I fastverify/tools/fvwork/fvwork.py` | `init`, `serve`, `verify`, `watch`, `status`, `stop` | per-repository daemon; in v0.1 each request is a cold sound run, the incremental machinery is EXPERIMENTAL (`--experimental-incremental`, never counted) ([README](../../fastverify/tools/fvwork/README.md)) |
| `python3 -I fastverify/tools/fvserve/fvserve.py` | `serve`, `submit`, `stats`, `stop` | attempt service for provers and RL ([README](../../fastverify/tools/fvserve/README.md)) |
| `python3 -I fastverify/tools/http/fvapi.py` | - | Kimina-compatible HTTP API in front of `fvserve` ([README](../../fastverify/tools/http/README.md)) |
| `fastverify/tools/mcp/fastverify-mcp` | - | MCP server, JSON-RPC 2.0 over stdio ([README](../../fastverify/tools/mcp/README.md)) |
| `python3 -I fastverify/check/warm/fvcheckd.py` | `serve`, `check-delta`, `check-full`, `stats`, `stop` | warm delta judge: not in v0.1; research code, not sound in its current form |

`fvwork`, `fvserve` and `fvcheckd` listen on Unix sockets in their `--state` directory; `fvapi` listens on TCP (loopback
by default); `fastverify-mcp` talks over stdin / stdout.

### HTTP endpoints (`fvapi.py`)

`GET /health`, `GET /metrics` (Prometheus), `POST /v1/verify`, `POST /v1/verify/batch`, and the Kimina-compatible
`POST /verify` and `POST /api/check` (`{"codes": [{"custom_id", "proof", "theorem"}]}`, answered with `is_pass`,
`verdict`, `reward`). A `theorem` is required per request unless `--custom-id-is-theorem` is set; the explicit `theorem`
field is the supported path. `--experimental-theorem-inference` (EXPERIMENTAL in v0.1, not reward-safe against
adversarial multi-theorem submissions) infers it from the source and answers NO-VERDICT whatever it cannot read exactly;
the old `--allow-theorem-inference` is refused. Hardening options:
`--api-key-file` (Bearer token), `--max-concurrent` (HTTP 429 beyond it), `--max-connections` (HTTP 503 before a handler
thread exists), `--header-timeout` (default 10 s), `--body-timeout` (default 15 s), `--max-body-bytes`,
`--max-source-bytes`, `--max-batch`.

### MCP tools (`fastverify-mcp`)

Tools: `fv_status`, `fv_doctor`, `fv_verify_attempt`, `fv_verify_batch`, `fv_verify_project`, `fv_verify_patch` (through
`fvwork`), `fv_check_export` (sound, frontier, notary, low-memory), `fv_triage_sublemma`, `fv_lookup_duplicate`,
`fv_diff_exports`, `fv_mint_subchallenges`, `fv_audit_challenge`, `fv_init_challenge`, `fv_parse_diagnostics`. Resources:
`fastverify://schema/result-v1`, `fastverify://status`. Prompt: `sound_proof_repair_loop`. Trusted challenges are
registered with `--challenge ID=DIR[:CHALLENGE_SHA256[:COMPARATOR_SHA256]]`; `--allow-root DIR` confines paths;
caller-supplied paths need a `comparator_sha256` wherever they need a `challenge_sha256` (`--allow-unpinned-comparator`
does not relax this). `fv_triage_sublemma` and `fv_check_export` with `notary: true` are EXPERIMENTAL and need the
server started with `--experimental` (or `FV_EXPERIMENTAL=1`).

## Standalone judges

Each takes the solution export, the official challenge export and the comparator configuration, prints a JSON object on
its last stdout line (or writes it with `--json FILE`) and exits 0 / 1 / 2 (3 for CONDITIONAL). Every judge script also
takes `--challenge-sha256 HEX` and `--comparator-sha256 HEX` (verified on its private copies; optional when the script
is started directly, passed by every front end) and `--require-sorried-holes`. The leg binaries inside them (`ccmp`,
`pleanchecker`) are not judges: their exit status alone is not a verdict
([standalone judge output](result-json.md#standalone-judge-output)).

```
fastverify/check/sound/check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE]
    [--timeout S] [--workdir DIR] [--hints FILE|none] [--private-inputs] [--pins FILE] [--hide FILE]
    [--kernel NAME] [--require-kernel NAME] [--skip-kernel NAME] [--kernel-jobs N] [--kernel-grace S] | --preflight [--pins FILE]
fastverify/check/lowmem/check-sound-lowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--mem-budget-mb MB]
    [--pins FILE] [--hide FILE|none] [--private-inputs] ...
fastverify/check/lowmem/check-sound-ultralowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--mem-budget-mb MB] ...
fastverify/check/notary/check-notary.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--kernels gruszka,con-ron,con-leche,nanoda] ...
fastverify/check/frontier/check-frontier.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--allowed FILE] [--pinned DIR]
    [--base BASE.json] [--axioms FILE] [--pins FILE] ...
```

The judges copy every input privately before reading it, so the kernel legs judge a file nobody else can write.
`--private-inputs` asserts that no other process can write the inputs and hard-links exports larger than 4 GiB instead;
use it only for a file you produced.

## Tools

| command | purpose |
|---|---|
| `python3 -I fastverify/tools/configure.py --elan-home DIR --light-lean DIR [--check-only]` | write `fastverify/config/components.json` and check every pinned official file |
| `python3 -I fastverify/tools/addrelease.py --elan-home DIR RELEASE...` | register further official Lean releases |
| `fastverify/tools/deploy.sh HOST` | copy an installation (package and pinned binaries) to another host and run the preflight there |
| `python3 -I fastverify/lib/autotune.py PROJECT --json` | print what `--preset sound-auto` would choose, and why |
| `python3 -I fastverify/tools/frontier/frontier.py pin EXPORT CHALLENGE_EXPORT COMPARATOR_JSON PINDIR` | pin a frontier (fixes the statements of the open lemmas) |
| `python3 -I fastverify/tools/frontier/ledger.py gate BASE.json CURRENT.json [--allow-new] [--require-progress] [--block-dropped]` | merge gate on the open-lemma ledger |
| `fastverify/tools/delta-export/export-delta.sh PROJECT MODULE delta.ndjson --packages WS` | export a delta for the warm judge (not in v0.1) |
| `fastverify/tools/subcontract/{mint,triage,subverify,merge,report}.py` | sub-challenges for untrusted contributors (EXPERIMENTAL in v0.1; [README](../../fastverify/tools/subcontract/README.md)) |
| `python3 -I fastverify/tools/guard/fvguard.py [LIMITS] [--json FILE] -- CMD...` | run a command under resource limits; exit 125 when a limit ended it ([limits and isolation](../user-guide.md#share-one-verifier-limits-and-isolation)) |
| `fastverify/tools/claims.py pin CHALLENGES_ROOT WS GIVEN_ROOT`, `fastverify/tools/claims.py verify PROJECT GIVEN_ROOT WS OUT` | several claims of one repository: build once, judge each claim against its own pinned challenge |
| `fastverify/tools/rh-sound.sh OUT [THREADS]` | reproduce the Riemann Hypothesis measurements ([benchmarks.md](../benchmarks.md#reproducing-the-riemann-hypothesis-runs)) |
| `fastverify/tests/run_all.sh [--heavy] [--jobs J] [--work DIR] [IDS...]` | the regression suite ([getting-started.md](../getting-started.md#7-run-the-tests)) |
