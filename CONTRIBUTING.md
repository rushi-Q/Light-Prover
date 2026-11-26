# Contributing to Light-Prover

Thank you for helping. Light-Prover is only useful if its verdicts can be trusted, so one rule comes before all
others: **a change must never make it possible to report ACCEPTED (or CONDITIONAL) for something the trusted check did
not establish.** Read [docs/concepts/soundness.md](docs/concepts/soundness.md) and section 3 of [fastverify/README.md](fastverify/README.md)
(trust model) before changing anything near the check.

Participation is governed by the [Code of Conduct](CODE_OF_CONDUCT.md). Vulnerabilities, including any false ACCEPTED in
sound mode, are reported privately as described in [SECURITY.md](SECURITY.md), never in a public issue or pull request.

## Ways to contribute

- Report bugs, soundness concerns and feature ideas with the issue templates.
- Improve the documentation in `docs/` and the package reference in `fastverify/README.md`.
- Send pull requests: speed-ups of the untrusted producers, new interfaces and tools, support for more Lean releases,
  tests, and fixes.

## Repository layout

| path | contents |
|---|---|
| `fastverify/` | the package: `bin/` (entry points `fastverify`, `fv`), `lib/` (orchestrator, autotune, budgets, verification of toolchains and pins), `build/`, `export/`, `check/` (trusted check and judge variants), `overlap/`, `tools/` (services, interfaces, compression and advisory tools), `tests/`, `bench/`, `toolchains/` (manifests of the official toolchains), `config/`, `schemas/` |
| `sources/` | sources of the fast components; the third-party ones keep their own licenses (see [NOTICE](NOTICE)) |
| `docs/` | installation, user guide, soundness model, option catalogue, design notes |
| `webpage/` | the project page and the scripts that draw its figures |

## Development setup

**For the checks that CI runs** (no Lean needed): Linux x86-64, Python 3.10, Bash and git. The project's Python code
uses only the standard library; nothing has to be installed with pip.

**For the full test suites and the soundness gates**, follow [docs/getting-started.md](docs/getting-started.md):

- `bwrap` (bubblewrap) >= 0.5, git, `/usr/bin/python3`;
- elan with the official toolchains `leanprover/lean4:v4.33.1` and `leanprover/lean4:v4.36.0` (some suites also use
  `v4.37.0-rc1`), and the official lean4export v4.33.0;
- to build the fast components: a C/C++ toolchain (clang 18 for the PGO builds of the kernel libraries), cmake, and
  Rust 1.97.1; the pinned binaries are installed under `$SCRATCH/fastverify-next/`;
- `python3 -I fastverify/tools/configure.py --elan-home "$ELAN_HOME" --light-lean "$PWD"` writes the machine-local
  `fastverify/config/components.json`. It is git-ignored; never commit it.

## Running the tests

### Checks without Lean (the CI workflow)

[`.github/ci-workflow.yml`](.github/ci-workflow.yml) (to be moved to `.github/workflows/ci.yml` to enable it) byte-compiles every project Python file, runs `bash -n` on every
project shell script (outside the third-party trees `sources/` and `fastverify/check/notary/gruszka-src/`) and runs
these suites, which need neither Lean nor the pinned binaries:

```bash
export LIGHT_LEAN=$PWD
bash fastverify/check/xversion/test/run.sh                   # cross-version release gate
python3 -I fastverify/tests/sound-auto/unit.py           # sound-auto planner (lib/autotune.py)
bash fastverify/tests/budget/run.sh                      # resource budget tools
bash fastverify/tests/compress-failure-classes/run.sh                  # compression regressions
python3 -I fastverify/tools/compress/prune/test/test_prune.py
bash fastverify/tools/compress/scheme/test/run.sh
bash fastverify/tools/compress/scheme/test/attribute_test.sh
```

Each prints PASS/FAIL rows and exits non-zero on a failure. Run them before every pull request.

### Regression suite (needs the official toolchains)

```bash
fastverify/tests/run_all.sh --list                     # the tests and what each checks
fastverify/tests/run_all.sh --jobs 12 [--work DIR]     # all non-heavy tests
fastverify/tests/run_all.sh --heavy                    # + heavy tests (Mathlib-scale inputs)
fastverify/tests/run_all.sh 038 066 challenge-config                # selected tests
fastverify/tests/run_all.sh --standin                  # harness self-test: the official flow stands in -> all PASS
```

The suite holds one test per known divergence from the official flow (`NNN`) plus generality (`gNN`) and stage component (`cNN`) tests. It tests a
snapshot of the package against the official flow and writes one row per case to
`fastverify/tests/results/<stamp>-<label>.tsv`; it exits 0 iff there is no FAIL or ERROR row. The default work directory
is under `/scratch`; pass `--work DIR` elsewhere. Details: [fastverify/tests/README.md](fastverify/tests/README.md) and
`fastverify/tests/INDEX.md`.

### Component and feature suites

- Trusted check: `fastverify/check/sound/test/run.sh` (set `CHECK_SOUND_TEST_DIR` to a directory outside `/tmp`, `/home`,
  `/var` and `/run`) and `fastverify/check/sound/test/preset.sh`.
- Stages: `fastverify/tests/package/run.sh`, `fastverify/tests/export/run.sh`, `fastverify/tests/toolchain/run.sh`,
  `fastverify/tests/package/retired-checkA.sh`, `fastverify/check/checkB/test/run.sh`, `fastverify/check/prechk/test/run.sh`,
  `fastverify/build/test/cmp_official.sh PROJECT_SRC FRESH_WORK PACKAGES_WS [TC]` and the build-item tests in
  `fastverify/build/test/`.
- Sound-mode and daily-use suites `fastverify/tests/dNN-*`, `gNN-*` and the tool tests under `fastverify/tools/*/test/`:
  see `fastverify/tests/INDEX.md` for what each needs.

### Soundness gates

`fastverify/tests/sound-gates/gates.py` runs the gates of the trusted check (README in that directory). Some gates need corpora that are not in the repository (the
lean-kernel-arena suite, the adversarial kernel corpus, the RH export); ask the maintainers when a change needs them.

## Code style

- Follow the surrounding code. `.editorconfig` sets encodings, line endings and indentation.
- **Python**: standard library only; 4-space indentation, lines up to 120 columns. Entry points run as `python3 -I`
  (isolated mode), many of them under `env -i`: never let environment variables, the user site directory or the
  current directory influence anything verdict-relevant. Code on the core orchestrator path (`bin/fastverify`, `lib/`)
  must keep running on Python 3.8; the other tools target Python 3.10.
- **Shell**: `#!/bin/bash`, `set -u` (or `set -eu`), quoted expansions, 2-space indentation; every script must pass
  `bash -n`.
- **Lean, Rust, C/C++**: follow the style of the component. Third-party trees under `sources/` keep their upstream
  formatting, license files and headers; record modifications of third-party code as patch files next to the build
  recipe (as in `fastverify/check/checkB/patches/`) and keep `NOTICE` current.
- **Stage conventions**: exit 0 = ok / accept, 1 = fail / reject, 2 = declined or could not run, 3 = CONDITIONAL; every
  stage script writes one JSON object (`--json FILE`) and supports `--preflight`.
- **Fail closed**: when in doubt, decline (exit 2) or refuse. A fallback must never lower trust or silently change
  semantics, and a resource limit or host failure is no verdict, never REJECTED or ACCEPTED.
- **Tests** print one PASS/FAIL row per case and a final `RESULT` line and exit 0 iff all pass. Parts that need a
  toolchain or corpus that is missing print `SKIP` instead of failing.
- **No machine-specific data**: no host names, personal names, e-mail addresses or absolute paths of a particular
  machine in code, tests or documentation. Use `$LIGHT_LEAN`, `$ELAN_HOME`, `$SCRATCH` and `config/components.json`.

## Trusted and untrusted changes

**Untrusted producers** (the build and its transforms, exporters, schedulers, caches, daemons, services and interfaces,
compression and advisory tools) may be optimized freely, because the trusted check re-checks everything they produce.
A pull request that changes them explains why the change can at most cause REJECTED or no verdict, and adds tests.
Requests to services carry solutions only: trust parameters (challenge, comparator configuration, permitted axioms,
frontier allow-list, target theorems) stay server-side and pinned.

**Trusted components** are everything that can turn a run into ACCEPTED or CONDITIONAL
([fastverify/README.md](fastverify/README.md) section 3, [docs/concepts/soundness.md](docs/concepts/soundness.md) section 1):

- the trusted check and its wiring: `fastverify/check/sound/` (`check-sound.sh`, judge sources, pins), the judge variants
  in `fastverify/check/lowmem/`, `check/notary/` and `check/frontier/`, and the release gate
  `fastverify/check/xversion/`;
- the incremental and targeted kernel leg in `fastverify/overlap/`;
- the judge sources in `sources/pchk/` (`CCmp.lean`, `ParAxioms.lean`, `FastParse.lean`, `PChk/`);
- the required second kernel (`sources/gruszka/` and the copies and patches of it under `fastverify/check/`);
- the verdict and pin logic in `fastverify/lib/` (`decide_sound`, `decide_notary`, toolchain and integrity
  verification);
- the pins: `pins*.env`, `config/components.template.json`, the toolchain manifests in `fastverify/toolchains/`.

A change to a trusted component is merged only when all of the following hold:

1. **Independent check.** A second person who is not the author checks the code and the argument. Larger changes,
   such as a new replay or verdict path, should get two independent checks.
2. **Written soundness argument.** A new or updated soundness section in the component's README (examples:
   `fastverify/check/sound/README.md`, `fastverify/overlap/README.md`,
   `fastverify/check/xversion/README.md`) explains why the change cannot produce a false ACCEPTED.
3. **Soundness gates.** The gates of `fastverify/tests/sound-gates/` pass on a frozen copy of the package
   (`fastverify/tests/sound-gates/tools/snapshot_pkg.sh`); the gate report goes with the change:
   - `arena`: lean-kernel-arena suite - the official-kernel leg gives the label on every test, no bad test accepted;
   - adversarial suites `suitex` (adversarial kernel corpus) and `cmpx` (comparator-level corpus, both configurations):
     no bad case accepted;
   - Mathlib differential (`mathlib`, and `mathlib-e2e` for the orchestrator's verdict logic): every verdict equals the
     official one;
   - RH mutants (`mutants`): the honest RH export ACCEPTED, mutants M1-M4 REJECTED;
   - thread matrix (`threads`): identical verdicts at 1, 32, 128, 255, 256 and 384 threads;
   - where they apply: the 12 kernel-level mutation classes, the incremental / targeted gates and the unit cases
     `fastverify/check/sound/test/run.sh`.
   A `FAIL-CRITICAL` row (a reject-labelled case accepted) blocks the change; WARN rows (availability) are discussed in
   the pull request.
4. **No kernel source changes in a deciding leg.** The official Lean kernel sources stay unmodified; only compiler and
   link options may differ.
5. **Pins and provenance.** Rebuilt binaries are pinned by sha256 in the stage's pins file, their build is recorded in
   [fastverify/PROVENANCE.md](fastverify/PROVENANCE.md), and they can be rebuilt byte for byte (`fastverify/tools/reproduce/`).

## Commits and pull requests

- Branch from `main` and keep one logical change per pull request.
- Commit messages: a summary line in the imperative mood of at most 72 characters, a blank line, then what changed and
  why. Reference issues and test directories where they apply (for example `Fixes #12`, `tests/066-...`).
- Fill in the pull request template, including the trusted-components section. CI must pass.
- Update the documentation and add an entry to the topmost unreleased section of [CHANGELOG.md](CHANGELOG.md) for
  user-visible changes.
- Do not commit generated or machine-local files (`fastverify/config/components.json`, build outputs, work directories,
  large exports), secrets or personal data.
- By contributing you agree that your contribution is licensed under the Apache License, Version 2.0 (section 5 of
  [LICENSE](LICENSE)). Third-party code must come with a compatible license, keep its notices and be listed in
  [NOTICE](NOTICE).
