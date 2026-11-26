# Portable rebuilds of the PGO and zygote build toolchains

The unofficial build toolchains of `--preset sound` (`lean4-s01zy-3cf5641cbd-pgo`, the zygote toolchain;
`lean4-d5e35ef223-pgo`; `lean4-7586a50cec-nopgo`) rebuilt from the same sources, patches, githash pin, PGO profile and
CMake options so that they start wherever the official Lean release starts (glibc 2.17 or later, nothing else from the
host). Names: `lean4-s01zy-3cf5641cbd-pgo-portable`, `lean4-d5e35ef223-pgo-portable`, `lean4-7586a50cec-nopgo-portable`,
and for Lean 4.37.0-rc1 `lean4-v4.37.0-rc1-pgo-portable` ([below](#lean-4370-rc1)). Like the originals they are untrusted
build-stage binaries: the judge checks everything they produce, and regression tests 004 014 020 031 037 040 046 048 050
052 061 apply. The patch series of the 4.33.1 base trees is not published
([provenance](../../PROVENANCE.md#4-build-toolchains-untrusted---preset-sound-only)), so this recipe records how the pinned
trees were built; it cannot be rerun from this repository alone.

**Why.** The original trees need from the host `libstdc++.so.6`, `libgmp.so.10`, `libuv.so.1`, `libssl.so.3`,
`libcrypto.so.3` and glibc 2.38 or later (PGO trees, built on Ubuntu 24.04) or 2.34 (nopgo, Ubuntu 22.04). They start on
none of 16 stock distribution images (not even `ubuntu:24.04`, which lacks libuv1), nor on Ubuntu 22.04 (glibc 2.35),
GitHub `ubuntu-22.04` runners or RHEL 8/9; there `--preset sound` loses the zygote. The official release links
GMP, libuv, OpenSSL and libc++ statically and needs only GLIBC_2.17.

## Recipe

The originals were built from the commit's tree with the githash in `src/CMakeLists.txt` pinned to the v4.33.1 release
`819816b2` (`set(GIT_SHA1 ...)` after `get_git_head_revision`), `CC=clang CXX=clang++ cmake --preset release` (ThinLTO,
since lld is found; PGO from `pgo/lean.profdata`), `make -C build/release`, tree = `build/release/stage1/{bin,include,lib}`;
s01zy = the `d0619cbcf0` tree plus `../s01zy-recipe/s01zy.patch`. The portable rebuild differs only in:

| item | original | portable |
|---|---|---|
| build userland | Ubuntu 24.04 (PGO trees) / 22.04 (nopgo) | manylinux_2_28 image (AlmaLinux 8.10, glibc 2.28) as a plain rootfs, entered with unprivileged `bwrap` (`broot.sh`; `mkroot.sh` makes it with docker) |
| compiler | Ubuntu clang 18.1.3 + lld (PGO); clang 14.0.0 + lld (nopgo) | conda-forge clang/lld 18.1.8; 14.0.6 for nopgo (`mkenv.sh`), target triple x86_64-pc-linux-gnu (`lean --version` unchanged) |
| C++ stdlib | host libstdc++ 13 (12), dynamic | gcc-toolset-13 (12) libstdc++, static and hidden: `-DLEAN_CXX_STDLIB='-Wl,-Bstatic -lstdc++ -Wl,-Bdynamic -Wl,--exclude-libs,libstdc++.a'` |
| GMP / libuv / OpenSSL | host shared libraries | the official 4.33.1 release's static archives (GMP 6.3.0, libuv 1.48.0, OpenSSL 3.6.0; sha256-checked against the pinned release manifest) and headers of those versions (`deps.sh`) |
| libm symbol versions | glibc 2.39 defaults | glibc 2.17 `libm.so.6` at link time only (`fvcc` wrappers; symlinks to create: `fvcc/LINKS.txt`) |
| build path | the recorded absolute build paths of the original trees (set in `build-tc.sh`) | the same paths, bind-mounted (`ORIGPATH` of `build-tc.sh`), so `__FILE__` strings are identical |
| stage0 githash in stage1 `.olean` headers | `d297d678...` (d5e35), empty (nopgo, s01zy) | reproduced per tree: `prep-src.sh ... git` for d5e35, `nogit` for nopgo and s01zy |
| cadical | host g++ 13 | gcc-toolset g++ with `-fPIE -pie`, static libstdc++, `--gc-sections` |

Steps (`PORT_WORK` = the work root, see the script headers): `mkroot.sh OUT` (needs docker) ->
`mkenv.sh $PORT_WORK/cenv18 $PORT_WORK/cenv14` -> `deps.sh` (inside `broot.sh`) ->
`prep-src.sh LEAN4_REPO COMMIT $PORT_WORK/src/NAME git|nogit` -> `build-tc.sh NAME ORIGPATH [J]` ->
`install-tc.py STAGE1 ORIG_MANIFEST OUT` (installs the original file layout and compares every file with the original
manifest) -> `lib/toolchain.py pin-unofficial` -> `idtest.sh` (whole `--preset sound` runs, original vs portable) ->
`compat/compat-matrix.sh` (start and elaborate in 16 distribution images).

## Pinned trees and verification

| name | tree sha256 | build |
|---|---|---|
| lean4-s01zy-3cf5641cbd-pgo-portable | 9b4404be0e583ac7014115b129695ce1f6b28c1b8e53a65c8de2338e47330640 | 429 s on 32 cores, `nogit` |
| lean4-d5e35ef223-pgo-portable | 57bab0719e32b59df243b459861832fdc7572299fae734a3c6f7d7cd1104242a | 468 s on 76 cores, `git` |
| lean4-7586a50cec-nopgo-portable | 913390cd79f89c533603b5bd6c53b26575c156215b4759838746c7c2de001feb | 416 s on 76 cores, `nogit`, clang 14.0.6 |

- Every `.olean`, `.ilean`, `.ir(.sig)`, `.olean.private/.server` (and `.hash`) of each tree's library, and for s01zy the
  2,486 `lib/temp/*.c`, is byte-identical to the original tree; only binaries, `.a`, object files and Lake traces differ.
- `objdump -T`: at most GLIBC_2.17 in every ELF, no GLIBCXX; `DT_NEEDED` only libc, libm, libdl, libpthread, libgcc_s and
  `ld.so`.
- Whole `--preset sound` runs, original vs portable, same machine and directory: rh-miniF (zygote on) 2,633
  `.olean`/`.ilean` identical and the same export; rh-mid on server A, 4 runs ABBA: 7,880 `.olean` identical, the same
  export, timing +0.5 % (noise).
- Machine C (glibc 2.35), rh-miniF `--preset sound`: 239/218 s with the fallback tree (no zygote), 195/182 s with the
  portable zygote tree.
- `compat/compat-matrix.sh`: starts and elaborates on 15 of 15 stock glibc images from `centos:7` (2.17) to `archlinux`
  (2.44), the originals on none, and every elaboration writes the official release's `.olean` bytes.
  `lib/autotune.py`'s static start probe agrees with the actual start in 126 of 126 (image, tree) cases
  (`compat/probecheck.py`).
- With `SOURCE_DATE_EPOCH`, two rebuilds on different machines are identical except 9 Lake archive files (member order =
  Lake job completion order). The pinned trees predate `SOURCE_DATE_EPOCH` and embed their build time.
- Regression test: `tests/*portable-toolchains/run.sh [--docker]`.

## Lean 4.37.0-rc1

`lean4-v4.37.0-rc1-pgo-portable` (experimental) is the unmodified official v4.37.0-rc1 source (tag `v4.37.0-rc1` =
`0b77e12952ad39077d80d8bd6b66d601f225c321`) built with PGO and ThinLTO; `--preset sound-auto` picks it for
`leanprover/lean4:v4.37.0-rc1` projects. Manifest: `toolchains/unofficial/lean4-v4.37.0-rc1-pgo-portable.json` (tree
sha256 `7043b146cc77756f...`, 34,599 files). Files in `v4.37/`.

1. `v4.37/port-pgo-lto.py src/CMakeLists.txt` ports four CMake-only changes of the 4.33 PGO line to the 4.37 file
   (`LEAN_TOOLCHAIN_CODEGEN_FLAGS`; ThinLTO by default with clang and lld on Linux; clang frontend PGO
   `LEAN_PGO_GENERATE` / `LEAN_PGO_USE`; `-Wl,-z,keep-text-section-prefix`) and sets `GIT_SHA1` to the release commit, so
   project `.olean` headers equal the release's and Mathlib cache `.olean` files import. Result: `v4.37/d21-437-build.diff`.
2. `deps437.sh`: the 4.37 release's own static GMP 6.3.0, libuv 1.53.0 and OpenSSL 4.1.0, with headers of those versions.
3. Instrumented build: `build-tc.sh` with `DEPS=.../v437 EXTRA_CMAKE="-DLEAN_PGO_GENERATE=ON -DLEAN_LTO=OFF"` (322 s on 64
   cores; needs conda `compiler-rt=18.1.8`).
4. Training: `train-pgo.sh TC WS OUT 1000 64` on a manifest-verified Mathlib `31ce06ea` workspace: 1,000 modules (seed
   21; 999 elaborated, 1 stopped after 155 s), 478 s; `llvm-profdata merge --sparse` gives `pgo/lean.profdata` (22.6 MB,
   sha256 `2d9ed39c0b4f9b071ab573c13a1b60bc1bf2ea91a81d122599b10a98e134603f`). This profile is not available, so the
   pinned tree cannot be rebuilt byte for byte; a new training run gives a different profile and tree. The profile was
   trained with an earlier `train-pgo.sh` that ran the instrumented `lean` outside a sandbox (the profile is counter data
   only); the published `train-pgo.sh` and `cmp-tc.sh` run every `lean` in bubblewrap (no network, home hidden, workspace
   and toolchain read-only).
5. Optimized build: `build-tc.sh` with `FVCC=fvcc437/bin` (clang++ links `-static-libstdc++`), `GCC_OVERRIDE=` a copy of
   gcc-toolset-13's `lib/gcc/.../13` whose `libstdc++.a` has `getentropy` weakened (`llvm-objcopy
   --weaken-symbol=getentropy`, as the release's libc++ references it), `EXTRA_CMAKE="-DLEAN_SPECIAL_VERSION_DESC=rc1
   -DLEAN_PLATFORM_TARGET=x86_64-unknown-linux-gnu"`, `SOURCE_DATE_EPOCH=1795000338` (the tag commit's time); 368 s on 64
   cores. Installed: `stage1/{bin,include,lib}` without `lib/temp`.

With that profile, two more builds from this recipe, on the same machine and on a second machine, were byte-identical
to the pinned tree (34,599 of 34,599 files). `lean --version` is byte-identical to the release's; `objdump`: at most GLIBC_2.25 (weak
`getentropy`, as the release), no libstdc++, GMP, libuv or OpenSSL in `DT_NEEDED`. It starts and elaborates exactly where
the official 4.37.0-rc1 release does (all glibc images from Amazon Linux 2, glibc 2.26, up; neither runs on CentOS 7) and
writes the same `.olean` files. `cmp-tc.sh` (Mathlib modules outside the training sample, official vs PGO, ABAB):
byte-identical `.olean` and `.ilean`. Regression tests 020, 050 and 061 apply; the patch-specific divergences of the 4.33
trees do not.

## Installing the trees on another machine

`portable-tc.sh pack NAME DIR` (on a machine with the verified tree) writes `NAME.tar.zst` and its sha256 (d5e35 and
nopgo about 0.7 GB, s01zy about 1 GB). `portable-tc.sh install NAME.tar.zst [TCDIR]` unpacks it under
`$SCRATCH/fastverify-next/tc/` and keeps it only if it verifies file by file against `toolchains/unofficial/NAME.json`;
`build/build.sh` verifies it again before every use.
