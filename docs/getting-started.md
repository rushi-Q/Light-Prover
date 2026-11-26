# Getting started

This guide installs Light-Prover (the `fastverify/` package) on one Linux machine, builds the pinned fast components from
[`sources/`](../sources/), runs a first verification and runs the tests. Daily workflows are in the
[user guide](user-guide.md).

Two things to know first:

- **The repository ships sources and recipes, no binaries.** Every fast binary is built from the vendored `sources/` and
  the stage sources and patches under `fastverify/` (each stage's provenance recipe) and pinned by sha256; the package refuses to run a stage whose binary is missing or differs. Not every pin is rebuildable from the
  repository alone: the PGO kernel libraries of the judge's `pleanchecker` legs need a 4.1 GB build bundle (compiler,
  C/C++ sysroot, PGO profile; `fastverify/PROVENANCE.md`) that is not shipped; without it you build the
  release-library variants, which have other sha256 values and must be pinned by you. The official options (official `lake build`, official
  `lean4export`, official `lake comparator`) need no fast binary, so the `reference` preset needs only the official
  tools of section 3.
- **Not everything is redistributed.** The Lean proof of the Riemann Hypothesis used in the benchmarks is not included
  (its author published it without a license; [benchmarks.md](benchmarks.md#reproducing-the-riemann-hypothesis-runs)
  says where to get it). A few build inputs are not shipped either; they are named in section 4.

Path variables used below. The package never reads them from the environment: `tools/configure.py` writes the first two
(and the package path) into `fastverify/config/components.json`.

| variable | meaning |
|---|---|
| `$LIGHT_LEAN` | the repository root, the directory that contains `fastverify/` |
| `$ELAN_HOME` | the elan home that holds the official Lean toolchains (default `~/.elan`) |
| `$SCRATCH` | a local scratch directory for your own work (set it yourself; outside `/tmp`, `/home`, `/var` and `/run`). The pinned fast binaries live at the absolute paths named in the stage manifests (commonly `/scratch/fastverify-next/<stage>/`), independently of it |

## 1. Prerequisites

- Linux x86-64 with glibc (musl-based distributions such as Alpine are not supported, as for the official Lean
  releases).
- `bwrap` (bubblewrap 0.5 or later, for `--clearenv`; RHEL 8 and Ubuntu 20.04 ship 0.4), `git`, `bc`, and
  `/usr/bin/python3`: 3.10 or later for the daily-use tools, 3.8 or later for the core orchestrator alone. The package
  runs Python with `-I` under `env -i`; `--preset sound` has been run end to end with Python 3.9 on Rocky Linux 8.
- elan, with the official toolchains `leanprover/lean4:v4.33.1` (projects) and `leanprover/lean4:v4.36.0` (comparator
  and judge). The package verifies both installed trees file by file against `fastverify/toolchains/*.json` and refuses
  otherwise. Projects on other official releases are added later with `fastverify/tools/addrelease.py`
  ([user guide](user-guide.md#lean-versions)).
- The official `lean4export` v4.33.0 (section 3).
- To build the fast components: a C/C++ toolchain (g++; clang 18 for the PGO builds of the kernel libraries; cmake for
  the optional patched kernel) and Rust 1.97.1, the version the default pinned Rust binaries were built with (`check/notary`'s `gruszka-r7` used 1.99.1).
- Host limits: `vm.max_map_count` must allow one `mmap` per project module plus 16,384 (for a project of the size of the
  Riemann Hypothesis proof, at least about 192,000). Source verification checks this while preparing the project (after
  the preflight) and refuses instead of reporting REJECTED.
- glibc: the default and low-memory judges' pinned binaries need glibc 2.17 and no dynamic `libstdc++` (the Lean 4.37.0-rc1 judge needs 2.25; the ultra-low-memory and notary Rust binaries target glibc 2.34);
  the portable PGO and zygote build toolchains need 2.17. On hosts with glibc older than 2.29 (for example RHEL or Rocky
  8), `fastverify/build/build.sh` compiles the planner and the `fast-exact` plugin with the host `cc`; if no host
  compiler works, the fast build declines and the official build runs.
- Memory: small projects run on a laptop-class machine; `fv doctor` recommends a preset and a thread count. Large
  exports need more memory or a low-memory judge ([user guide](user-guide.md#choose-a-preset-and-judge-for-your-hardware)).

## 2. Get the repository

The repository is private: the https clone needs a GitHub account with access to it.

```bash
git clone <repository-url> Light-Prover
cd Light-Prover
export LIGHT_LEAN=$PWD ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
```

## 3. Official toolchains and the official exporter

```bash
elan toolchain install leanprover/lean4:v4.33.1
elan toolchain install leanprover/lean4:v4.36.0

# official lean4export v4.33.0 (commit 15f6055), built with the official Lake 4.33.1
git clone https://github.com/leanprover/lean4export "$LIGHT_LEAN/env/tools/lean4export"
cd "$LIGHT_LEAN/env/tools/lean4export" && git checkout v4.33.0
PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/bin:/usr/bin:/bin" lake build
cd "$LIGHT_LEAN"
```

The result must be `$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export`; its sha256 is pinned in
`fastverify/config/components.template.json` (`805ab4cc…`). For Lean 4.36 projects the package uses the `leanexport`
bundled with the official 4.36.0 release.

## 4. Build the pinned fast components

The recipes need g++ and cargo (Rust 1.97.1); the byte-identical PGO builds of the 4.36 kernel libraries also need a
build bundle that is not shipped (`fastverify/PROVENANCE.md`).

Each stage pins its binaries by sha256 (`components.json` or `pins.env` in the stage directory) and documents the exact
build in its `PROVENANCE.md`; [`fastverify/PROVENANCE.md`](../fastverify/PROVENANCE.md) lists every component. The
pinned paths are absolute and point to `/scratch/fastverify-next/<stage>/`: install the results there, or edit those
paths. `fastverify/tools/deploy.sh HOST` copies an installation (package and binaries) to another host and runs the
preflight there.

| needed for | component | recipe |
|---|---|---|
| every judge (sound, low-memory, ultra-low-memory, notary): the self-test inputs checked before each run | `selftest_comparator`, `selftest_challenge`, `selftest_good`, `selftest_bad`, `selftest_kbad` | shipped in `fastverify/check/sound/selftest/`: install them with the two commands of [its README](../fastverify/check/sound/selftest/README.md) |
| sound mode (`--preset sound`, `sound-auto`), the judge | `ccmp`, `pleanchecker`, `pleanchecker_incr`, `gruszka` (`fastverify/check/sound/pins.env`) | [`fastverify/check/sound/README.md`](../fastverify/check/sound/README.md#rebuilding); rebuild-and-compare scripts in `fastverify/tools/reproduce/`; targeted overlap: `fastverify/overlap/PROVENANCE.md` |
| judge variants (4.37, low-memory, ultra-low-memory, frontier; notary is experimental) | `ccmp`/`pleanchecker` 4.37 (`pins-437.env`), `ccmp_lowmem`, `pleanchecker_lowmem`, `gruszka_lowmem`, `ccmp_notary`/`pleanchecker_notary`/`gruszka_r7`, `fvfrontier_prep` | `fastverify/check/sound/README.md` (4.37), `fastverify/check/lowmem/README.md`, `fastverify/check/notary/README.md`, `fastverify/check/frontier/README.md` |
| native exporter E1 and closure guard | `lean4export-979c4f8`, `closure_check` | `fastverify/export/README.md`: `sources/lean4export-native` built with the official Lake 4.33.1 (`lake build`); closure guard `fastverify/export/closure/closure_check.cpp` (`g++ -O2 -std=c++17 -pthread -static`) |
| legacy research checks C3 and C4 (trust `UNSAFE`) | `gruszka`, `nl-fast`, `kcompare`, `prechk` | `fastverify/check/checkB/build.sh DIR`, `fastverify/check/prechk/build.sh` |
| the `--preset sound` build toolchain (T1, UNSAFE outside sound mode) | patched and PGO Lean 4.33.1 trees (zygote) | manifests in `fastverify/toolchains/unofficial/`; recipes in `fastverify/toolchains/s01zy-recipe/` and `fastverify/toolchains/portable-recipe/`; `fastverify/build/README.md` |

Notes on the recipes:

- They were written for the original build environment. The scripts take the sources as git repositories at pinned
  commits (`git fetch <commit>` / `git archive <commit>`): use a source repository that contains that commit, or adapt
  the step to use the vendored snapshot in `sources/<name>` directly (a fresh `git init` and commit of the snapshot has a
  different commit id). `check/checkB/build.sh` also calls a sandboxed build wrapper that is not
  part of this repository, and the zygote toolchain recipe starts from a locally built base tree. Adapt those lines.
- Byte-identical rebuilds need the same compiler and linker versions; some Rust binaries embed their build directory, so
  their sha256 depends on it.
- Without the zygote toolchain, `--preset sound-auto` simply does not use the zygote, and `--preset sound` falls back to
  the exact build B1 when its untrusted build declines. The judge is the same in every case.

## 5. Configure

```bash
python3 -I fastverify/tools/configure.py --elan-home "$ELAN_HOME" --light-lean "$LIGHT_LEAN"
fastverify/bin/fv doctor                       # host readiness, recommended preset and threads
```

`configure.py` writes `fastverify/config/components.json` from `config/components.template.json` and prints `OK`,
`MISMATCH` or `MISSING` for every pinned official file (exit 0 if and only if all match; a mismatch or a missing file
gives exit 2). `python3 -I fastverify/tools/configure.py --check-only` re-checks an existing configuration.
Run it as a user with a passwd entry (`getent passwd "$(id -u)"` prints one).

## 6. First verification

Run `fastverify/bin/fv` and `fastverify/bin/fastverify` directly, not as `bash fastverify/bin/fv`: started through
`bash FILE`, bash applies a caller's `BASH_ENV` and `SHELLOPTS` before the script's first line.

A tiny project without Mathlib (five `Nat` facts; the toy case of regression test 011). Use a fresh work directory of your
own (every `OUT` below must not exist yet):

```bash
W=$(mktemp -d "${SCRATCH:?set SCRATCH to a local directory}/fv-first.XXXXXX")
cp -r fastverify/tests/011-*/x/proj/b "$W/proj"
cp -r fastverify/tests/011-*/x/challenge "$W/challenge"

# 1. preflight: must print "preflight OK" (whole toolchain trees verified, the component checks and stage probes)
fastverify/bin/fastverify "$W/proj" "$W/challenge" "$W/out-pre" --preset reference --preflight-only

# 2. the official flow, sandboxed (official lake build + official lean4export + unmodified lake comparator)
fastverify/bin/fastverify "$W/proj" "$W/challenge" "$W/out-ref" --preset reference --threads 8

# 3. sound mode, build tuned to the host and project (needs the judge's binaries from section 4)
fastverify/bin/fastverify "$W/proj" "$W/challenge" "$W/out-sound" --preset sound-auto --threads 8
```

The challenge directory contains `comparator.json`, `lean-toolchain`, and either `challenge.export` (an optional
`.sha256` sidecar may record its digest) or
its sources (`Challenge.lean` and a lakefile, as here; the challenge is then built and exported by the official build
and exporter). For projects with dependencies it also needs `.lake/packages` at the project manifest's revisions (for
example after `lake exe cache get`), or a trusted workspace given with `--packages`. Sound mode refuses a given
`challenge.export` unless you pin it with `--challenge-sha256 HEX` and its comparator configuration with
`--comparator-sha256 HEX` (the configuration decides which statements and axioms are checked, so it is pinned like the
challenge); `fastverify/bin/fv init-challenge CHALLENGE_SRC OUT` builds and pins one officially.

Each run writes `OUT/result.json` with the verdict and the trust basis; a run that reaches the export and the check also
records per-stage times, the export sha256 and the sha256 of every component used ([result-json.md](reference/result-json.md)).
Only an ACCEPTED with trust `sound`, `sound-conditional` or `notary` counts: the reference run of step 2 prints ACCEPTED
with trust `official`, which `fv` reports as not accepted (exit 2). Exit status: 0 ACCEPTED, 1 REJECTED, 2 no verdict
(DECLINED, ERROR or refused), 3 CONDITIONAL (only with `--modulo-frontier`). `OUT` must not exist or be empty. All
options: `fastverify/bin/fastverify --help`, `fastverify/bin/fv --help`, and the [CLI reference](reference/cli.md).

## 7. Run the tests

`tools/configure.py` registers Lean 4.33.1 and 4.36.0 only; add 4.37.0-rc1 with `python3 -I fastverify/tools/addrelease.py
--elan-home "$ELAN_HOME" 4.37.0-rc1`. Some suites need it and a trusted packages workspace (the 4.37 rows of the
CLI tests, the triage and audit rows of the interface tests); without them those rows fail on a fresh clone. Every row that fails on a fresh clone for missing inputs or environment
is listed in [fastverify/tests/README.md](../fastverify/tests/README.md#running-the-test-suite-on-a-fresh-clone).

- **Regression suite** (one test per known divergence `NNN`, generality tests `gNN`, stage component tests `cNN`):

  ```bash
  fastverify/tests/run_all.sh [--heavy] [--jobs J] [--work DIR] [IDS...]
  fastverify/tests/run_all.sh --list
  ```

  It tests a snapshot of the package against the official flow and writes one row per case (PASS, PASS-DECLINE,
  WARN-DECLINE, FAIL-ACCEPT, FAIL-EXPORT, FAIL-REJECT, ...) to `fastverify/tests/results/<stamp>-<label>.tsv`; exit 0 if
  and only if there is no FAIL or ERROR row. Pass the work directory with `--work DIR` (or set `FV_TEST_WORK`); it must lie outside `/tmp`,
  `/home`, `/var` and `/run`, which the trusted check's sandbox hides. The tests need the official tools and, for the fast options, the pinned fast binaries. The heavy test
  `rh-minif-export` needs a 1,657-module subset of the Riemann Hypothesis project, which is not redistributed
  (`fastverify/tests/rh-minif-export/PROJ_NOT_INCLUDED.md`). Some tests compare against the earlier fast pipeline
  (`fastverify/pipeline/`) to show its divergences. Rows that run the official `lake comparator` live need a `HOME` whose elan home holds the official toolchains; in a sandboxed run set
  `FV_TEST_OFFICIAL=recorded` to use the recorded official verdicts instead (default `live`). Details:
  [`fastverify/tests/README.md`](../fastverify/tests/README.md).
- **The judge** (a few minutes each; only the pinned self-test exports): `fastverify/check/sound/test/run.sh` (set
  `CHECK_SOUND_TEST_DIR` to a directory outside `/tmp`, `/home`, `/var` and `/run`; default `/scratch`) and
  `fastverify/check/sound/test/preset.sh` (sound mode in the orchestrator).
- **Component suites** (each prints PASS/FAIL rows, exit 0 if and only if all pass): `fastverify/tests/package/run.sh`,
  `fastverify/tests/export/run.sh`, `fastverify/tests/toolchain/run.sh`, `fastverify/tests/package/retired-checkA.sh`,
  `fastverify/check/checkB/test/run.sh`, `fastverify/check/prechk/test/run.sh`. The build comparison is separate:
  `fastverify/build/test/cmp_official.sh PROJECT_SRC FRESH_WORK PACKAGES_WS [TC]` prints `CMP: SAME`, `DIFFERENT` or
  `DECLINED` (exit 0 also on a decline).
- **Soundness gates** of the trusted components: `fastverify/tests/sound-gates/gates.py`
  ([README](../fastverify/tests/sound-gates/README.md)). Some gates need corpora that are not in this repository (the
  lean-kernel-arena suite, the adversarial kernel corpus, the Riemann Hypothesis export).

## Next steps

- [User guide](user-guide.md): verify your own project, judge exports, conditional verdicts, daemons and services.
- [Soundness model](concepts/soundness.md): what a verdict means.
- [Benchmarks](benchmarks.md): measured results and how to reproduce them.
