# Low-memory and ultra-low-memory judges (`check/lowmem/`)

Two variants of the [sound judge](../sound/README.md) for machines with less memory. Their verdicts carry the same trust
(`sound`); the ultra-low-memory judge has known false rejects ([limitations](../../../docs/limitations.md#assurance)); they run the legs one after another and keep less of the export in memory, so they are slower when
memory is not the constraint. `sound-auto` picks the low-memory judge when the default judge's estimated peak exceeds
the memory budget; the ultra-low-memory judge is never chosen automatically.

```
check/lowmem/check-sound-lowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE]
                                   [--mem-budget-mb MB] [--pins FILE] [--hide FILE|none] ...
check/lowmem/check-sound-ultralowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] ...
```

Exit 0 ACCEPTED, 1 REJECTED, 2 no verdict. Measured: the 61.6 GB Riemann Hypothesis export in a 128 GB limit (low-memory)
and in a 64 GB limit (ultra-low-memory), [benchmarks](../../../docs/benchmarks.md#judging-an-export-by-machine-budget).

## What they run

**Low-memory judge** (`check-sound-lowmem.sh`, Lean 4.36 `pins.env`, Lean 4.37.0-rc1 `pins-437.env`): the comparison leg is
replaced by `ccmp-lowmem`; the two kernel legs are the default judge's `pleanchecker` and `gruszka`, run one after the
other.

**Ultra-low-memory judge** (`check-sound-ultralowmem.sh`, `pins-ultralowmem.env`): `ccmp-lowmem`, then
`pleanchecker-lowmem` (the official-kernel leg with a paged expression store) and `gruszka-lowmem` (the second kernel with
a disk-backed store).

ACCEPTED requires every leg to accept, as in the default judge.

## Pinned binaries

Low-memory, Lean 4.36 (`pins.env`):

<!-- PINS:BEGIN check/lowmem/pins.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `ccmp_lowmem` | `da4b77b02b2bff0f1b661724ed9c6a170dbe1302a655326c51f9ee73863837e8` | streaming comparison leg: builds only the expressions `compareAt` reads | `check/lowmem/src` + `check/sound/src` | the recipe below (`leanc lowmem_arena.c` + `lake build ccmp-lowmem` in bubblewrap) | yes |
| `pleanchecker` | `53957eed5fda7baa728708b87ed85508dd5e4fe9f3c99318bda0451451fbc65a` | official-kernel leg: parallel `Lean.Replay` walk with the unmodified v4.36.0 kernel sources (PGO + ThinLTO build) | `check/sound/src` | objects with `lake build pleanchecker`; kernel libraries and link with `tools/reproduce/portable-pgo.sh` in the pinned manylinux_2_28 image | with the build bundle only |
| `gruszka` | `ece04e7458efafd34e71330e982bf3b46904d48ff5f1089c7094844c9562fe58` | independent second kernel (veto only, mandatory) | `sources/gruszka` + `check/checkB/patches/gruszka-combined-v6.diff` | `tools/reproduce/portable-gruszka.sh default` (digest-pinned manylinux2014 image, offline Rust 1.97.1) | yes |
| `selftest_comparator` | `9c77b8d2c3c5fb92a8681e5f9d9d9bde0a8ff0fe35ecc5a31ac3024ff4f12802` | self-test configuration | `check/sound/selftest/comparator.json` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_challenge` | `f83cfdd3029814bd61d88e808b2c2e33344ca893214cfec0faa15c66c1048af0` | self-test challenge export | `check/sound/selftest/challenge.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_good` | `cbc6a26ce8c2c9b4e97085d6822c33026eb36e15ba24a5be0ec8f25746e4d281` | self-test export (must be ACCEPTED) | `check/sound/selftest/good.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_bad` | `a48f2d1c4c8e6d5b4be291f72a64926c9afa8398508e02fb68cec2df73a0513f` | self-test export (must be REJECTED) | `check/sound/selftest/bad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `pleanchecker_incr` | `6a9092380325cc6f6ae94234e671aa67ba6a5daf163e642611d01c0762b91b7f` | targeted-overlap leg (opt-in `--overlap-targets`) | `check/sound/src` + `overlap/src/r9d` | as `pleanchecker`, with the incremental module | with the build bundle only |
<!-- PINS:END -->

Low-memory, Lean 4.37.0-rc1 (`pins-437.env`):

<!-- PINS:BEGIN check/lowmem/pins-437.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `ccmp_lowmem` | `a1fbc56d958eb228752ec2184dfc7df7e1594f25647e3ce85287b444ce432b97` | streaming comparison leg, Lean 4.37.0-rc1 | `check/lowmem/src-437` | `tools/reproduce/rebuild-lowmem-437.sh` | yes |
| `pleanchecker` | `acf82e8321cbfebc53a6fbadc4f2f6fc535a44b7eb6468431abf4af995993135` | official-kernel leg, Lean 4.37.0-rc1 release libraries, encapsulated replay | `check/sound/src-437` | `tools/reproduce/rebuild-437.sh` | yes |
| `gruszka` | `ece04e7458efafd34e71330e982bf3b46904d48ff5f1089c7094844c9562fe58` | independent second kernel (veto only, mandatory) | `sources/gruszka` + `check/checkB/patches/gruszka-combined-v6.diff` | `tools/reproduce/portable-gruszka.sh default` (digest-pinned manylinux2014 image, offline Rust 1.97.1) | yes |
| `selftest_comparator` | `9c77b8d2c3c5fb92a8681e5f9d9d9bde0a8ff0fe35ecc5a31ac3024ff4f12802` | self-test configuration | `check/sound/selftest/comparator.json` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_challenge` | `f83cfdd3029814bd61d88e808b2c2e33344ca893214cfec0faa15c66c1048af0` | self-test challenge export | `check/sound/selftest/challenge.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_good` | `cbc6a26ce8c2c9b4e97085d6822c33026eb36e15ba24a5be0ec8f25746e4d281` | self-test export (must be ACCEPTED) | `check/sound/selftest/good.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_bad` | `a48f2d1c4c8e6d5b4be291f72a64926c9afa8398508e02fb68cec2df73a0513f` | self-test export (must be REJECTED) | `check/sound/selftest/bad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
<!-- PINS:END -->

Ultra-low-memory (`pins-ultralowmem.env`):

<!-- PINS:BEGIN check/lowmem/pins-ultralowmem.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `ccmp_lowmem` | `da4b77b02b2bff0f1b661724ed9c6a170dbe1302a655326c51f9ee73863837e8` | streaming comparison leg: builds only the expressions `compareAt` reads | `check/lowmem/src` + `check/sound/src` | the recipe below (`leanc lowmem_arena.c` + `lake build ccmp-lowmem` in bubblewrap) | yes |
| `pleanchecker` | `53957eed5fda7baa728708b87ed85508dd5e4fe9f3c99318bda0451451fbc65a` | official-kernel leg: parallel `Lean.Replay` walk with the unmodified v4.36.0 kernel sources (PGO + ThinLTO build) | `check/sound/src` | objects with `lake build pleanchecker`; kernel libraries and link with `tools/reproduce/portable-pgo.sh` in the pinned manylinux_2_28 image | with the build bundle only |
| `gruszka` | `ece04e7458efafd34e71330e982bf3b46904d48ff5f1089c7094844c9562fe58` | independent second kernel (veto only, mandatory) | `sources/gruszka` + `check/checkB/patches/gruszka-combined-v6.diff` | `tools/reproduce/portable-gruszka.sh default` (digest-pinned manylinux2014 image, offline Rust 1.97.1) | yes |
| `pleanchecker_lowmem` | `d27c3bddaf31e1a402d67d92ae9ab21899a1b2a433652e836a51f0459b170a41` | ultra-low-memory official-kernel leg: paged expression store, unmodified v4.36.0 release libraries | `check/lowmem/src-ultralowmem/src/pleanchecker-lowmem` | `check/lowmem/src-ultralowmem/build-pleanchecker-lowmem.sh` | yes |
| `gruszka_lowmem` | `bbbeafcf3b19262cf5de4c1ffe21225f92d45da72607693114617fbef075eabe` | disk-backed second kernel (veto only) | as `gruszka` + `check/lowmem/src-ultralowmem/patches/gruszka-lowmem.patch` | `tools/reproduce/portable-gruszka.sh lowmem` | yes |
| `selftest_comparator` | `9c77b8d2c3c5fb92a8681e5f9d9d9bde0a8ff0fe35ecc5a31ac3024ff4f12802` | self-test configuration | `check/sound/selftest/comparator.json` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_challenge` | `f83cfdd3029814bd61d88e808b2c2e33344ca893214cfec0faa15c66c1048af0` | self-test challenge export | `check/sound/selftest/challenge.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_good` | `cbc6a26ce8c2c9b4e97085d6822c33026eb36e15ba24a5be0ec8f25746e4d281` | self-test export (must be ACCEPTED) | `check/sound/selftest/good.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `selftest_bad` | `a48f2d1c4c8e6d5b4be291f72a64926c9afa8398508e02fb68cec2df73a0513f` | self-test export (must be REJECTED) | `check/sound/selftest/bad.export` | shipped; install: `check/sound/selftest/README.md` | = shipped file |
| `pleanchecker_incr` | `6a9092380325cc6f6ae94234e671aa67ba6a5daf163e642611d01c0762b91b7f` | targeted-overlap leg (opt-in `--overlap-targets`) | `check/sound/src` + `overlap/src/r9d` | as `pleanchecker`, with the incremental module | with the build bundle only |
<!-- PINS:END -->

## Rebuilding

Every binary specific to these judges is built against the official release libraries and rebuilds byte-identically.
`ccmp-lowmem` (Lean 4.36), offline, from the repository root:

```bash
TC36=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0      # verified by lib/toolchain.py
BDIR=<build directory>                                      # the recorded build used a fixed directory; rebuilding elsewhere has not been compared byte for byte
rm -rf "$BDIR" && mkdir -p "$BDIR"
cp -a fastverify/check/sound/src/{FastParse.lean,ParAxioms.lean,CCmp.lean,CCmpMain.lean,Main.lean,PChk,lean-toolchain,lake-manifest.json} "$BDIR/"
cp -a fastverify/check/lowmem/src/{lowmem_arena.c,LowMemParse.lean,CCmpLowMem.lean,CCmpLowMemMain.lean,lakefile.toml} "$BDIR/"
env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind "$TC36" "$TC36" --bind "$BDIR" "$BDIR" --chdir "$BDIR" \
  --setenv HOME /tmp --setenv PATH "$TC36/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 \
  -- bash -c "\"$TC36/bin/leanc\" -c -O3 -Wall -Wextra -Wno-unused-parameter -isystem /usr/include -isystem /usr/include/x86_64-linux-gnu lowmem_arena.c -o lowmem_arena.o && lake build ccmp ccmp-lowmem"
sha256sum "$BDIR/.lake/build/bin/ccmp" "$BDIR/.lake/build/bin/ccmp-lowmem"   # = the ccmp and ccmp_lowmem pins
```

The 4.37 `ccmp-lowmem` is built the same way from `src-437/` with the 4.37.0-rc1 toolchain
(`tools/reproduce/rebuild-lowmem-437.sh`), `pleanchecker-lowmem` with `src-ultralowmem/build-pleanchecker-lowmem.sh`,
and `gruszka-lowmem` with `tools/reproduce/portable-gruszka.sh lowmem`. The shared kernel legs are rebuilt as described
in [`check/sound/`](../sound/README.md#rebuilding).

## Why an ACCEPTED is sound

**`ccmp-lowmem` computes the official result.** It reads the export in two passes. The first pass validates every line
as the official export parser does and builds the constant-dependency graph without building expressions; the axiom
check runs on that graph and visits exactly the constants the official `checkAxioms` visits. The second pass builds
expressions only for the constants that the official `compareAt` reads (the targets and the challenge's statement
closure) and then runs the unmodified `compareAt` on them. Constant names are keyed exactly as the official reader keys
them. Where the streaming reader cannot follow the official reader exactly (an export it cannot index, a name index it
does not accept), it declines or rejects; it never accepts what the official reader would refuse.

**The low-memory judge's kernel legs are the default judge's**, with the same binaries and pins; running them one after
the other changes nothing in what each checks.

**`pleanchecker-lowmem` only removes unfolding rules.** It runs the same replay with the official v4.36.0 release
libraries but keeps expressions in a paged, reference-counted store and, after a theorem has been checked, replaces it
in the environment that later declarations see by an axiom of the same name, universe parameters and type. In the
v4.36.0 kernel a theorem and such an axiom behave identically except that the theorem's value can be unfolded, so the
replacement shrinks definitional equality and never extends it: a declaration accepted against the reduced environment
is accepted against the full one. Some valid proofs do need a theorem's value (a theorem used as the major premise of a
subsingleton eliminator whose motive is a type); the judge then retries with those theorems kept, and if the retry still
fails it answers REJECTED, never ACCEPTED. `gruszka-lowmem` is the default second kernel with a disk-backed store and
smaller worker tables; it can only veto.

The wiring rules of the default judge apply unchanged: private copies with change stamps, per-leg output files, sha256
checks of every pinned file before and after the run, the configuration checks and the cross-version gate.

## Known limitations

The streaming reader rejects some exports that the official reader would also refuse but reports them differently; the
ultra-low-memory judge gives no verdict when the closure of the failing declarations exceeds its budget. Details: [docs/limitations.md](../../../docs/limitations.md#assurance) and
[performance](../../../docs/limitations.md#performance).

## Tests

The directories of `tests/` whose names contain `lowmem`; the soundness gates of the pinned binaries: `tests/sound-gates/`.
