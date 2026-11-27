# Provenance of the pinned components

What each pinned binary is, its sha256, where its sources are and how to rebuild it. The repository ships sources and
recipes, no binaries; every stage refuses to run when a pinned file is missing or has another sha256. Pins are absolute
paths under `/scratch/fastverify-next/` (install the binaries there or edit the pins files); `fastverify/tools/deploy.sh
HOST` copies an installation to another host and runs its preflight there.

Path variables: `$FASTVERIFY` = this package, `$ELAN_HOME` = the elan home with the official toolchains, `$LIGHT_LEAN` =
the repository root.

## 1. Official toolchains (verified, not rebuilt)

| component | pin | used for |
|---|---|---|
| Lean 4.33.1, 4.36.0, 4.37.0-rc1 and the other admitted releases | whole-tree manifests `toolchains/leanprover--lean4---v*.json`; tarball provenance in `toolchains/RELEASES.md`; admission table `check/xversion/releases.json` | builds, the official exporter, the official comparator (C0), the judges' release libraries |
| `lake comparator` (C0) | part of the verified 4.36.0 tree (4.37.0-rc1 tree for 4.37 challenges) | the `reference` preset |
| bundled `leanexport` (4.35 and later) | part of the verified release tree | the official exporter E0 of those releases |

## 2. The judges

Each judge has one document with its legs, its pinned binaries and their sha256, how to rebuild each binary, its
soundness argument and its known limitations. Each judge script verifies every file of its pins file by sha256 at the
start and at the end of every run.

| judge | pins file | document |
|---|---|---|
| sound judge, Lean 4.36 (default) and Lean 4.37.0-rc1 | `check/sound/pins.env`, `check/sound/pins-437.env` | [check/sound/README.md](check/sound/README.md) |
| low-memory judge (4.36, 4.37.0-rc1) and ultra-low-memory judge | `check/lowmem/pins.env`, `pins-437.env`, `pins-ultralowmem.env` | [check/lowmem/README.md](check/lowmem/README.md) |
| low-memory and ultra-low-memory judge (4.36) on arm64 macOS | `check/sound/macos/pins.env` | [check/sound/macos/README.md](check/sound/macos/README.md) |
| notary judge (EXPERIMENTAL in v0.1) | `check/notary/pins.env` | [check/notary/README.md](check/notary/README.md) |
| conditional verdicts (frontier preparer) | `check/frontier/pins.env` | [check/frontier/README.md](check/frontier/README.md) |
| cross-version gate (no binary) | `check/xversion/releases.json` | [check/xversion/README.md](check/xversion/README.md) |

The judges' self-test inputs (`selftest_*` pins) are shipped in `check/sound/selftest/`; install them at the pinned paths
with the commands in [its README](check/sound/selftest/README.md).

Byte-identical rebuilds: every release-library Lean binary and every `gruszka` build rebuild byte-for-byte from this
repository. The 4.36 PGO kernel libraries of `pleanchecker` / `pleanchecker_incr` need a 4.1 GB build bundle (compiler,
sysroot, headers, PGO profile) that is not shipped (see below); without it, build the release-library variant and pin
its sha256 yourself. The rebuild-and-compare scripts are in `tools/reproduce/`.

The macOS judge runs four programs that are compiled on the Mac, from the sources of the Linux recipes with no file
changed for macOS: `ccmp-lowmem` (eight names of `check/sound/src` and five of `check/lowmem/src`), `pleanchecker`
(`check/sound/src`), `pleanchecker-lowmem` (`check/lowmem/src-ultralowmem/src/pleanchecker-lowmem`) and `gruszka`
(`sources/gruszka` with `check/checkB/patches/gruszka-combined-v6.diff`, Rust 1.97.1 and the 31 crates of its
`Cargo.lock`). The three Lean programs are linked from the unmodified libraries of the official Lean 4.36.0 release for
arm64 macOS, so the official kernel is not compiled there; the C code is compiled, and all four programs are linked, by
the clang and the lld of that toolchain. `check/sound/macos/pins.env` pins the sha256 of each program and the
fingerprint of its sources, and a run compares the three programs of its script and the self-test inputs with these pins
before its first leg and after its last. Where the programs are is not pinned: the record of the machine
(`config/pins-macos.env`, not tracked) names their paths. `check/sound/macos/build-judge-macos.sh OUTDIR` rebuilds all
four and stops unless they have the pinned bytes. They were rebuilt byte for byte on two Macs with macOS 27.2.1, an M4
with the Command Line Tools and an M5 Pro with Xcode: the Lean programs in nine builds and `gruszka` in seven, in
different folders, with one, two and four build jobs and with the toolchain installed at another place. A Mac with
another macOS release was not measured.

### Build bundle for the PGO kernel libraries

The PGO scripts of `tools/reproduce/` read a build-environment bundle (variable or argument `BUNDLE`, about 4.1 GB, not
shipped): `BUNDLE/cenv` (the conda clang 18.1.8 environment), `BUNDLE/deps/root/usr`, `BUNDLE/kb` and `BUNDLE/dl/cmake`
(dependency headers, GMP, pkg-config, cmake 3.31.6), `BUNDLE/kopt/` (the v4.36.0 source archive, the mimalloc v3.4.5
download and the PGO profile) and `BUNDLE/objs-*` (the `pleanchecker` object sets). The Rust scripts take a directory
with offline `rustup/` and `cargo/` copies; the docker-based scripts need docker on the host.

## 3. Exporters (untrusted)

| component | sha256 | source and build |
|---|---|---|
| native exporter E1, Lean 4.33.1 | `6b26eb16c45e201dc90af2ad6a876d77a745ee8274c72bb64e85c3bb0c5fe404` | `sources/lean4export-native`, built with the official Lake 4.33.1 (`export/README.md`) |
| native exporter E1, Lean 4.36.0 | `bb25a91e10fa83c61e462d4d2fa664a7b20da3370233cdacbc3f1fe16277c0b2` | the same source, built with the official 4.36.0 toolchain (`export/README.md`) |
| native exporter E1, Lean 4.37.0-rc1 | `174f3962414c76d79634c9d104c4986f065c86c55c723d66885bb7e5237ae8db` | plus `export/native-exporter-f04.patch` and `native-exporter-d22-v437.patch` (`export/README.md`) |
| closure guard | `60b84139b18e352ddcaf79e36e1c44d79e5636efe26dc3c47f6a727eac4211cc` | `export/closure/closure_check.cpp` (`g++ -O2 -std=c++17 -pthread -static`) |
| low-memory exporter, Lean 4.33.1 | `a86e719879d88f189b6e58001deb0411426dedabcee6b4318883ba6b4caaecba` | the native exporter plus an output-neutral memory patch (`export/README.md`) |
| low-memory exporter, Lean 4.37.0-rc1 | `9c4ae13d05feb8028f250d78ca39692ffefdc10fbf19383ef036f0faaa770f1e` | the 4.37 exporter plus the memory patch (`export/README.md`) |
| official exporter `lean4export` v4.33.0 | `805ab4cc6a88dcef109644d201c3142261f524aecaf58b04913a9f029e21e9b5` | the official repository at v4.33.0, built with the official Lake 4.33.1 (getting started, section 3) |
| native exporter E1 and closure guard, macOS (Apple silicon, Lean 4.33.1) | none in the tree: the system's C++ compiler builds the guard and the exporter's C++ core, so they are not the same bytes on every Mac. `config/components.macos.json` pins the fingerprints of their sources (`export_sources`); the recipe writes the sha256 of what it built into `config/export-macos.env` on that Mac | `export/build-macos.sh`: `sources/lean4export-native` with `export/native-exporter-macos.patch`, built with the official Lake 4.33.1, and `export/closure/closure_check.cpp` (`c++ -O2 -std=c++17 -pthread`) (`export/README.md`) |
| official exporter `lean4export` v4.33.0, macOS | `e775ccfbe86c08fa9fea1ec1fe45c46ed168cf48236ff8ba429aa28b05c0623e` (`config/components.macos.json`; `tools/configure.py` writes it into the machine's `config/components.json`) | the official repository at v4.33.0, built on the Mac with the official Lake 4.33.1 |

## 4. Build toolchains (untrusted, `--preset sound` only)

| component | pin | notes |
|---|---|---|
| patched and PGO Lean 4.33.1 toolchains (`toolchain-T1`) | whole-tree manifests in `toolchains/unofficial/` | v4.33.1 plus 36 performance patches (`lean4-7586a50cec-*`), its PGO build (`lean4-d5e35ef223-*`) and the zygote toolchain on top (`lean4-s01zy-3cf5641cbd-*`; diff `toolchains/s01zy-recipe/s01zy.patch`); the patch series of the base is not published; portable rebuilds: `toolchains/portable-recipe/`; `build/README.md` |
| PGO Lean 4.37.0-rc1 toolchain | `toolchains/unofficial/lean4-v4.37.0-rc1-pgo-portable.json` | experimental; its PGO profile was lost, so it cannot be rebuilt byte-for-byte |

Without these toolchains `sound-auto` does not use them and `--preset sound` falls back to the exact build; verdicts do
not depend on them.

## 5. Other pinned components

| component | pins | provenance |
|---|---|---|
| legacy research checks C3 / C4 (`gruszka`, `nl-fast`, `kcompare`) | `check/checkB/components.json` | `check/checkB/README.md`, `check/checkB/build.sh` |
| `prechk` gate of C3 / C4 | `check/prechk/pins.env` | `check/prechk/build.sh` (fully static, no third-party code) |
| `fvserve` compile worker (optional, untrusted) | built locally | `tools/fvserve/fork/build.sh TC OUT` with the official 4.33.1 toolchain; needs Linux 5.13 or later with Landlock |
| `expaudit` of `fv audit` (advisory, untrusted) | `tools/audit/bin/expaudit`, sha256 `4b4b11b41decfbf117cab63b810feb2a8f0f2bab0435f6f62b380c6310f8c55a` | `std`-only Rust crate `tools/audit/expaudit/`, built in a manylinux2014 container (glibc 2.16) |
| `exphash` of `fv lookup` (advisory, untrusted) | `tools/dupfind/bin/exphash`, sha256 in `tools/dupfind/bin/SHA256SUMS` | `tools/compress/exphash`, built with `tools/reproduce/portable-exphash.sh` (Rust 1.97.1, manylinux2014) |

## 6. Published sources

The `SHA256SUMS` files next to the published sources list their hashes. Pinned binaries are not shipped; they are
rebuilt from these sources (see [../docs/getting-started.md](../docs/getting-started.md)) and verified against the pins in
`check/*/pins*.env` and `config/components.template.json`.

