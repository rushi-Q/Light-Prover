# `fastverify/` - the Light-Prover package

This directory is the package: the orchestrator, the untrusted fast build and export, the trusted judges, the services
and the tests. The user documentation is in [`../docs/`](../docs/README.md); measurements are in
[`../docs/benchmarks.md`](../docs/benchmarks.md), limitations in [`../docs/limitations.md`](../docs/limitations.md).

## Entry points

| command | what it does |
|---|---|
| `bin/fv` | the daily CLI: `verify`, `check`, `doctor`, `init-challenge`, `audit`, `attempt`, ... ([CLI reference](../docs/reference/cli.md)) |
| `bin/fastverify PROJECT CHALLENGE OUT --preset ...` | the orchestrator behind every interface: build, export and judge, `result.json` ([presets and options](../docs/reference/options.md)) |
| `check/sound/check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON` | the sound judge on an existing export |
| `tools/fvwork/fvwork.py`, `tools/fvserve/fvserve.py`, `tools/batchverify.py`, `tools/http/fvapi.py`, `tools/mcp/mcp_server.py` | the per-repository daemon, the attempt service, batch verification, the HTTP API and the MCP server ([user guide](../docs/user-guide.md)) |
| `tools/configure.py` | writes `config/components.json` for this machine ([getting started](../docs/getting-started.md)) |
| `tools/addrelease.py` | admits a further official Lean release (whole-tree manifest) |
| `tools/rh-sound.sh OUT [THREADS]` | reproduces the Riemann Hypothesis run ([benchmarks](../docs/benchmarks.md#reproducing-the-riemann-hypothesis-runs)) |

Only an ACCEPTED with trust `sound`, `sound-conditional` or `notary` counts; every other outcome, including DECLINED,
NO-VERDICT and ERROR, is not accepted ([output formats](../docs/reference/result-json.md)).

## Layout

| directory | contents | trusted? |
|---|---|---|
| `bin/` | `fv` and `fastverify` | wiring |
| `lib/` | the orchestrator (`fastverify.py`), `sound-auto` (`autotune.py`), toolchain verification (`toolchain.py`) | verdict mapping only |
| `build/` | the official build B0 and the fast builds B1-B3 ([build/README.md](build/README.md)) | no |
| `export/` | the official exporter E0, the native exporter E1, the closure guard ([export/README.md](export/README.md)) | no |
| `check/sound/` | the sound judge, Lean 4.36 and 4.37.0-rc1, and its self-test inputs ([README](check/sound/README.md)) | yes |
| `check/lowmem/` | the low-memory and ultra-low-memory judges ([README](check/lowmem/README.md)) | yes |
| `check/notary/` | the notary judge, EXPERIMENTAL ([README](check/notary/README.md)) | yes |
| `check/frontier/` | conditional verdicts ([README](check/frontier/README.md)) | wiring |
| `check/xversion/` | the cross-version gate ([README](check/xversion/README.md)) | yes |
| `check/official/` | the unmodified official `lake comparator` (C0, the `reference` preset) | official |
| `check/warm/` | the warm delta judge: research code, not in v0.1 | - |
| `check/checkB/`, `check/prechk/` | legacy research checks C3 / C4, trust `UNSAFE` ([README](check/checkB/README.md)) | no |
| `overlap/` | opt-in overlap of the kernel leg with the build ([README](overlap/README.md)) | partly |
| `tools/` | services, daemons, CI action, advisory tools, reproduction scripts (`tools/reproduce/`) | no, except where a tool runs a judge |
| `config/`, `toolchains/` | component pins and whole-tree manifests of the official and the build toolchains | pins |
| `schemas/` | the `result.json` and API envelope schema | - |
| `bench/` | benchmark harnesses ([bench/README.md](bench/README.md)) | no |
| `tests/` | regression tests, component suites, soundness gates ([tests/README.md](tests/README.md)) | - |
| `pipeline/` | the earlier fast pipeline, used only by the regression tests to show its divergences | no |

Tools with their own README: [cli](tools/cli/README.md), [fvwork](tools/fvwork/README.md),
[fvserve](tools/fvserve/README.md), [http](tools/http/README.md), [mcp](tools/mcp/README.md),
[audit](tools/audit/README.md), [lowmem](tools/lowmem/README.md), and the EXPERIMENTAL
[ci-action](tools/ci-action/README.md) and [subcontract](tools/subcontract/README.md).

Every pinned binary, its sha256, sources and rebuild: [PROVENANCE.md](PROVENANCE.md) and the judge READMEs. The
repository ships sources and recipes, no binaries. Running very large verifications on one host:
[large runs](../docs/large-runs.md).

## Requirements

Linux x86-64 with glibc, bubblewrap 0.5 or later, Python 3.10 or later for the daily-use tools (the core runs with 3.8),
the official Lean toolchains through elan, and C/C++ and Rust toolchains to build the fast components. Details and the
glibc requirements of the pinned binaries: [getting started](../docs/getting-started.md).

## Tests

| command | what |
|---|---|
| `tests/run_all.sh [--heavy] [--jobs J] [--work DIR] [IDS...]` | the regression suite against the official flow; one row per case in `tests/results/<stamp>-<label>.tsv`; exit 0 iff no FAIL or ERROR |
| `check/sound/test/run.sh` (set `CHECK_SOUND_TEST_DIR`) and `check/sound/test/preset.sh` | the sound judge's unit cases and sound mode in the orchestrator |
| `tests/package/run.sh`, `tests/export/run.sh`, `tests/toolchain/run.sh`, `tests/package/retired-checkA.sh` | component suites |
| `tests/sound-gates/gates.py` | the soundness gates of the trusted components (some corpora are not in the repository) |

The index of all tests and what each needs: [tests/INDEX.md](tests/INDEX.md); the work directory must lie outside `/tmp`,
`/home`, `/var` and `/run`, which the judge's sandbox hides ([getting started](../docs/getting-started.md#7-run-the-tests)).
