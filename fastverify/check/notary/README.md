# Notary judge (`check/notary/`, EXPERIMENTAL in v0.1)

A variant of the [sound judge](../sound/README.md) for a final sign-off: kernel legs built only from the official
release libraries (no PGO rebuild), and a check that every leg judged the same environment. Its ACCEPTED carries trust
`notary`. It is experimental in v0.1: `--preset notary`, `--check CN` and `fv check --notary` are refused without `--experimental`,
and the preset supports exactly one kernel configured by the challenge.

```
check/notary/check-notary.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--kernels LIST] [--json FILE] ...
```

Exit 0 ACCEPTED, 1 REJECTED, 2 no verdict.

## What it runs

1. `ccmp-notary`: the official comparator judge code (`compareAt`, `checkAxioms`) against the official v4.36.0 release
   libraries.
2. `pleanchecker-notary`: the parallel `Lean.Replay` driver of the sound judge, linked against the unmodified official
   v4.36.0 release libraries, without the targeted-overlap module.
3. `gruszka-r7`: the independent second kernel (veto only).

Each of the three legs computes a canonical SHA-256 digest of the environment it actually parsed and judged. ACCEPTED
requires every leg to accept and all digests and constant counts to agree. Kernels selected with `--kernels` (`con-ron`,
`con-leche`, `nanoda`, unchanged binaries of the official release) are mandatory: each must accept.

## Pinned binaries

<!-- PINS:BEGIN check/notary/pins.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `ccmp_notary` | `388abf3dbf83241bf27702138d784cdeba78f3e10a0129a4d38a5d79c26a7eaa` | notary comparison leg with the environment digest | `check/notary/src-ccmp-388abf3d` | `lake build ccmp-notary` (official 4.36 toolchain) | yes |
| `pleanchecker_notary` | `7fed15cfb9c5c95c582d3198d93abd9ac139ad9029cacbefb2eb6d2c8acea53b` | notary official-kernel leg, unmodified v4.36.0 release libraries, environment digest | `check/notary/src` | `lake build pleanchecker-notary` | yes |
| `gruszka_r7` | `5aea77f5f4367dc55df1dfe43299c37ee6de3359870a1dda7ca07ca9e3516489` | notary second kernel and third digest leg | as `gruszka` + `check/notary/gruszka-r7-digest.diff` | `tools/reproduce/portable-gruszka.sh notary` | yes |
| `selftest_comparator` | `9c77b8d2c3c5fb92a8681e5f9d9d9bde0a8ff0fe35ecc5a31ac3024ff4f12802` | self-test configuration | `check/sound/selftest/comparator.json` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_challenge` | `f83cfdd3029814bd61d88e808b2c2e33344ca893214cfec0faa15c66c1048af0` | self-test challenge export | `check/sound/selftest/challenge.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_good` | `cbc6a26ce8c2c9b4e97085d6822c33026eb36e15ba24a5be0ec8f25746e4d281` | self-test export (must be ACCEPTED) | `check/sound/selftest/good.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_bad` | `a48f2d1c4c8e6d5b4be291f72a64926c9afa8398508e02fb68cec2df73a0513f` | self-test export (must be REJECTED) | `check/sound/selftest/bad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
<!-- PINS:END -->

## Rebuilding

All three binaries rebuild byte-identically. In copies of the source trees, offline, with the official 4.36 toolchain:

```bash
TC36=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0      # verified by lib/toolchain.py
env -i PATH="$TC36/bin:/usr/bin:/bin" HOME=/tmp LANG=C.UTF-8 bash -c 'cd COPY_OF/check/notary/src && lake build pleanchecker-notary'
env -i PATH="$TC36/bin:/usr/bin:/bin" HOME=/tmp LANG=C.UTF-8 bash -c 'cd COPY_OF/check/notary/src-ccmp-388abf3d && lake build ccmp-notary'
fastverify/tools/reproduce/portable-gruszka.sh notary GRUSZKA_SRC OUT BUNDLE
```

`src-ccmp-388abf3d/` is the exact tree the pinned `ccmp-notary` was built from; `ref_digest.py` is an independent Python
implementation of the environment digest over NDJSON exports.

## Why an ACCEPTED is sound

The argument of the sound judge applies leg by leg: the official comparator code checks statements and axioms, the
official kernel replays every declaration of the targets' closure, and the second kernel can only veto. The kernel legs
use the release libraries exactly as the official Lean 4.36 binaries do, so no compiler-option change sits between the
official kernel source and the check.

The digest adds one guarantee: the three legs judged byte-for-byte the same environment. A difference between the legs'
parsers, or a file that changes while the legs read it, would give different digests, and the judge declines. The digest
is computed over each leg's in-memory environment, not over the file, so it attests what was checked. The wiring rules
of the sound judge (private copies, per-leg outputs, sha256 checks before and after the run, configuration checks, the
cross-version gate) apply unchanged.

## Known limitations

See [docs/limitations.md](../../../docs/limitations.md) (notary: one configured kernel in v0.1, mandatory
configured kernels, the hint-field limit) and [benchmarks](../../../docs/benchmarks.md#judging-an-export-by-machine-budget).

## Tests

The directories of `tests/` whose names contain `notary`; the soundness gates: `tests/sound-gates/`.
