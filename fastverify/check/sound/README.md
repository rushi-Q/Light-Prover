# Sound judge (`check/sound/`)

The trusted check behind `--preset sound`, `--preset sound-auto`, `fv verify`, `fv check` and the services. It decides
whether an export proves the target statements of a pinned challenge from the permitted axioms. Lean 4.36 is the
default judge (`pins.env`); the Lean 4.37.0-rc1 judge uses the same script with `--pins pins-437.env`.

```
check/sound/check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--pins FILE] [--hide FILE]
                           [--kernel NAME] [--require-kernel NAME] [--skip-kernel NAME] [--private-inputs]
                           [--require-sorried-holes] ...
check/sound/check-sound.sh --preflight [--pins FILE]
```

Exit 0 ACCEPTED, 1 REJECTED, 2 no verdict (DECLINED or ERROR). `check-sound-svc.sh` is the same script with an integrity
cache for long-running services.

## What it runs

Three legs, each on the judge's private copy of the export:

1. **Comparison leg `ccmp`**: the official `lake comparator` judge code. `compareAt` checks that every target has
   exactly the statement of the official challenge export (with the definitions the statement mentions), and
   `checkAxioms` checks that the targets' closure uses only the permitted axioms. Only the parsing is concurrent.
2. **Official-kernel leg `pleanchecker`**: a parallel driver of `Lean.Replay` that hands every declaration of the
   targets' closure to the unmodified official Lean kernel (the v4.36.0 sources; for 4.37 the v4.37.0-rc1 release
   libraries). The driver chooses only the order of the kernel calls.
3. **Second kernel `gruszka`**: an independent kernel implementation. It can only veto and is mandatory.

ACCEPTED requires all three legs to accept. A definite rejection by any leg gives REJECTED; anything else (a crash, a
timeout, a memory kill, a leg that cannot decide) gives no verdict.

## Pinned binaries

The script verifies every pinned file by sha256 before and after each run and runs a self-test first. The self-test
inputs are shipped in `selftest/`; install them at their pinned paths with the commands in `selftest/README.md`.

Lean 4.36 (`pins.env`):

<!-- PINS:BEGIN check/sound/pins.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `ccmp` | `4e82fe00f73f96c54471475d4def2d8bfafc239b9694557faffa70179b6b216d` | comparison leg: the official `lake comparator` judge code (`compareAt`, `checkAxioms`), concurrent parsing | `check/sound/src` | `tools/reproduce/rebuild-pchk.sh` (`lake build ccmp`, official 4.36 toolchain, release libraries) | yes |
| `pleanchecker` | `53957eed5fda7baa728708b87ed85508dd5e4fe9f3c99318bda0451451fbc65a` | official-kernel leg: parallel `Lean.Replay` walk with the unmodified v4.36.0 kernel sources (PGO + ThinLTO build) | `check/sound/src` | objects with `lake build pleanchecker`; kernel libraries and link with `tools/reproduce/portable-pgo.sh` in the pinned manylinux_2_28 image | with the build bundle only |
| `gruszka` | `ece04e7458efafd34e71330e982bf3b46904d48ff5f1089c7094844c9562fe58` | independent second kernel (veto only, mandatory) | `sources/gruszka` + `check/checkB/patches/gruszka-combined-v6.diff` | `tools/reproduce/portable-gruszka.sh default` (digest-pinned manylinux2014 image, offline Rust 1.97.1) | yes |
| `selftest_comparator` | `9c77b8d2c3c5fb92a8681e5f9d9d9bde0a8ff0fe35ecc5a31ac3024ff4f12802` | self-test configuration | `check/sound/selftest/comparator.json` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_challenge` | `f83cfdd3029814bd61d88e808b2c2e33344ca893214cfec0faa15c66c1048af0` | self-test challenge export | `check/sound/selftest/challenge.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_good` | `cbc6a26ce8c2c9b4e97085d6822c33026eb36e15ba24a5be0ec8f25746e4d281` | self-test export (must be ACCEPTED) | `check/sound/selftest/good.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_bad` | `a48f2d1c4c8e6d5b4be291f72a64926c9afa8398508e02fb68cec2df73a0513f` | self-test export (must be REJECTED) | `check/sound/selftest/bad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `pleanchecker_incr` | `6a9092380325cc6f6ae94234e671aa67ba6a5daf163e642611d01c0762b91b7f` | targeted-overlap leg (opt-in `--overlap-targets`) | `check/sound/src` + `overlap/src/r9d` | as `pleanchecker`, with the incremental module | with the build bundle only |
| `snapshot_exporter` | `4ac1016d928ccec86869d392ab6f3485fa139bd361ba484154f80126af4bd9cd` | untrusted snapshot exporter of the opt-in targeted overlap | the native exporter + `overlap/src/e1-snap.diff` | as the native exporter (`export/README.md`) | - |
| `con_leche` | `8fff3f055d032b66d5262cb6db4fb916328b4931a98634630f7481b1e3449308` | opt-in extra veto kernel: `con-leche --verified` of the official Lean v4.37.0-rc1 release, unchanged | official release | copied from the release | = release file |
| `nanoda` | `5c34d6124b19dfd23c7d0377b520893cf8adec5c23fa0c809dde9e38eb201ffe` | opt-in extra veto kernel: `nanoda_bin` 0.4.31 of the official Lean v4.37.0-rc1 release, unchanged | official release | copied from the release | = release file |
| `selftest_kbad` | `2a3d286b326a1051de0f04609157c80efa767258afa5553904cf85d219639dfe` | self-test export of the extra kernels (must be rejected) | `check/sound/selftest/selftest-kbad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
<!-- PINS:END -->

Lean 4.37.0-rc1 (`pins-437.env`):

<!-- PINS:BEGIN check/sound/pins-437.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `ccmp` | `e046aa895f20d9a2edd127e07264d10d5a330c178ff4b2a3308f0cd21c217ddd` | comparison leg, Lean 4.37.0-rc1 judge code | `check/sound/src-437` | `tools/reproduce/rebuild-437.sh` (official 4.37.0-rc1 toolchain, release libraries) | yes |
| `pleanchecker` | `acf82e8321cbfebc53a6fbadc4f2f6fc535a44b7eb6468431abf4af995993135` | official-kernel leg, Lean 4.37.0-rc1 release libraries, encapsulated replay | `check/sound/src-437` | `tools/reproduce/rebuild-437.sh` | yes |
| `gruszka` | `ece04e7458efafd34e71330e982bf3b46904d48ff5f1089c7094844c9562fe58` | independent second kernel (veto only, mandatory) | `sources/gruszka` + `check/checkB/patches/gruszka-combined-v6.diff` | `tools/reproduce/portable-gruszka.sh default` (digest-pinned manylinux2014 image, offline Rust 1.97.1) | yes |
| `selftest_comparator` | `9c77b8d2c3c5fb92a8681e5f9d9d9bde0a8ff0fe35ecc5a31ac3024ff4f12802` | self-test configuration | `check/sound/selftest/comparator.json` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_challenge` | `f83cfdd3029814bd61d88e808b2c2e33344ca893214cfec0faa15c66c1048af0` | self-test challenge export | `check/sound/selftest/challenge.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_good` | `cbc6a26ce8c2c9b4e97085d6822c33026eb36e15ba24a5be0ec8f25746e4d281` | self-test export (must be ACCEPTED) | `check/sound/selftest/good.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_bad` | `a48f2d1c4c8e6d5b4be291f72a64926c9afa8398508e02fb68cec2df73a0513f` | self-test export (must be REJECTED) | `check/sound/selftest/bad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `con_leche` | `8fff3f055d032b66d5262cb6db4fb916328b4931a98634630f7481b1e3449308` | opt-in extra veto kernel: `con-leche --verified` of the official Lean v4.37.0-rc1 release, unchanged | official release | copied from the release | = release file |
| `nanoda` | `5c34d6124b19dfd23c7d0377b520893cf8adec5c23fa0c809dde9e38eb201ffe` | opt-in extra veto kernel: `nanoda_bin` 0.4.31 of the official Lean v4.37.0-rc1 release, unchanged | official release | copied from the release | = release file |
| `selftest_kbad` | `2a3d286b326a1051de0f04609157c80efa767258afa5553904cf85d219639dfe` | self-test export of the extra kernels (must be rejected) | `check/sound/selftest/selftest-kbad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
<!-- PINS:END -->

## Rebuilding

The release-library binaries (`ccmp`, the 4.37 `pleanchecker`) rebuild byte-identically from this repository with the
official toolchain alone, as does `gruszka` with the digest-pinned container and an offline Rust 1.97.1
([PROVENANCE.md](../../PROVENANCE.md#build-bundle-for-the-pgo-kernel-libraries)). The 4.36 `pleanchecker` and `pleanchecker_incr` link the official v4.36.0 kernel and runtime
sources compiled with PGO and ThinLTO inside a digest-pinned `manylinux_2_28` container (glibc 2.17, static libstdc++);
the kernel libraries embed their source path, so the sources are mounted at the fixed build directory recorded in the recipe script
(`tools/reproduce/portable-pgo.sh`); that path is part of the pinned bytes, so a byte-identical rebuild must use it.
A byte-identical rebuild needs the 4.1 GB build bundle (clang 18.1.8, dependency headers, the v4.36.0 sources, the PGO
profile) described in [PROVENANCE.md](../../PROVENANCE.md#build-bundle-for-the-pgo-kernel-libraries), which is not shipped. Without it, build `pleanchecker` against the
official release libraries (`lake build pleanchecker` in a copy of `src/`) and pin your own sha256; the kernel code is
the same official source, only compiled differently.

The pins are absolute paths under `/scratch/fastverify-next/`; install the binaries there or edit the pins files.

## Why an ACCEPTED is sound

The claim (see [soundness model](../../../docs/concepts/soundness.md)): the judged export proves every target statement
of the official challenge export from the permitted axioms. It rests on three facts.

**The statements and axioms are checked by the official code.** `ccmp` runs the comparator's own `compareAt` and
`checkAxioms` on the official challenge export and the solution export, with the comparator's kernel primitives. The
configuration is checked by the script itself: the permitted axioms must be `propext`, `Quot.sound` and
`Classical.choice` (a configuration with other axioms is refused unless `--extra-axioms FILE` lists them), and the caller's challenge and comparator
pins must match the private copies. Challenges of other Lean releases go through the cross-version gate
([`check/xversion/`](../xversion/README.md)) first.

**Every declaration is checked by the official kernel.** `pleanchecker` replays the targets' closure through the official
kernel's `addDecl`, as `Lean.Replay` does; it skips `unsafe` and `partial` records as the official replay does. Two veto
checks are added around the kernel and can only add failures: an inductive block whose types contain a loose bound
variable is rejected before the kernel sees it (Lean issue #16489, fixed only in the 4.37 kernel), and after the replay
every export record whose name is in the kernel environment must equal the kernel's constant, with quotient records
under their official names (#15100, #15101). The records of an inductive block never enter an environment the kernel
reads: the kernel generates the block's constructors and recursors itself, and the export's records are only compared
with them. Parallelism changes the order of the kernel calls, not the environment each call sees.

**A second, independent kernel must agree.** `gruszka` replays the same export; its rejection is a veto. Known kernel
defects exploitable by crafted exports are caught by both kernel legs.

The wiring cannot turn a failure into ACCEPTED: each leg writes its own output file and the script reads the leg's
exit status and its own result lines only, so text that a declaration name puts into a log cannot forge a verdict. The
export and the configuration are copied to a private directory before the check and their change stamps are verified
after it, so a file rewritten during the run is not judged. All binaries are verified by sha256 before and after the
run.

### Lean 4.37: the encapsulated replay

With `--hide FILE` the 4.37 kernel leg replays each declaration in an environment where the listed definitions and all
earlier theorems are visible by their types only, as the 4.37 module system sees them. Hiding a body removes unfolding
rules; it adds none. A declaration that type-checks with fewer unfolding rules therefore type-checks with all of them, so
an acceptance in the reduced environment is an acceptance in the full one. A kernel error in the reduced environment is
re-checked in the full environment, which decides. The hide list is untrusted: a wrong list costs time, never a
verdict. This monotonicity argument was checked by reading the kernel; its confirmation by a Lean kernel maintainer is
pending. Without `--hide` the 4.37 leg runs the plain replay.

### Extra veto kernels (opt-in)

`check-sound.sh --kernel NAME` (`--extra-kernel NAME` in `bin/fastverify`) adds `con-leche` or `nanoda` (the unchanged binaries of the official 4.37.0-rc1
release) as further kernels on the same private copy. Each must pass its own self-test. An extra kernel can only remove
an acceptance: its rejection is a veto, and if it cannot decide, the verdict stays as the three legs decided unless the
kernel was made mandatory with `--require-kernel`.

### Targeted overlap (opt-in)

`--overlap-targets FILE` starts the longest kernel jobs (`pleanchecker_incr`) while the build is still running, each on
an environment taken from a snapshot export. In the final replay such a job's kernel call is skipped only if the final
export holds the same constant, every constant it reaches is present and equal in both, and the kernel-implicit
constants agree; ACCEPTED then also requires every skipped job to have succeeded. Otherwise the final export is replayed
without skips ([overlap/](../../overlap/README.md)).

## Data files

- `hints/default.txt`: scheduling hints for the kernel replay (one declaration name per line, 279 names: the long kernel
  jobs of the Riemann Hypothesis proof). The workers start these jobs first; hints change only the order, never what is
  checked. `--hints FILE|none` replaces them; `hints/mkhints.sh LOG MIN_MS` builds a list from the slow-job lines of a
  check log.
- `hide/lean-4.37.0-rc1-no-expose.txt`: the hide list of the encapsulated replay (36,285 names: the non-exposed
  definitions of the dependencies of a Lean 4.37.0-rc1 project with Mathlib 31ce06e). Untrusted and availability only.
  For another Mathlib pin, regenerate it by comparing the public and private `.olean` parts of every module.

## Known limitations

The second kernel declines or rejects some valid corner cases (availability only), the 4.37 judge rejects some valid
structure-eta proofs, and the opt-in extra kernels have their own false rejects. All of them, with workarounds:
[docs/limitations.md](../../../docs/limitations.md#assurance).

One residual of the v0.1 binaries: an export that redeclares an existing inductive block is rejected, but in a short
window after the rejection is certain the kernel can read mismatched generated constants (availability only; 8,993 such
mutants caused no crash). A three-line guard that closes the window is planned for the next rebuild of the replay legs.

## Tests

`test/run.sh` (unit cases of the script, about a minute), `test/preset.sh` (sound mode in the orchestrator), `test/xk.sh`
and `test/xk-preset.sh` (extra kernels). The soundness gates of every pinned binary: `tests/sound-gates/`.
