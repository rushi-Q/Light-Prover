# Build recipe of the zygote toolchain `lean4-s01zy-3cf5641cbd-pgo`

- **Source.** Commit `3cf5641cbd` of a lean4 fork that is not published separately; `s01zy.patch` = `git diff d0619cbcf0
  3cf5641cbd` (sha256 below). The base `d0619cbcf0` is `d5e35ef223` minus three import patches, plus the PGO profile
  `pgo/lean.profdata` and the class/base zygote. The patch adds THP windows, a SIGCHLD self-pipe, replicas, an rusage log,
  prefix mode and debug timings.
- **Build** (Ubuntu 24.04, Ubuntu clang 18.1.3, cmake, glibc 2.39): run `build_tc.sh` in a directory holding
  `s01zy.patch`, with `S01ZY_BASE_TREE` = a build tree of `d0619cbcf0` and `S01ZY_WORK` = a work directory. The base tree
  is a `git worktree add` of `d0619cbcf0` with the githash in `src/CMakeLists.txt` pinned to the v4.33.1 release
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, built with `CC=clang CXX=clang++ cmake --preset release
  -DCMAKE_C_COMPILER_LAUNCHER=ccache -DCMAKE_CXX_COMPILER_LAUNCHER=ccache && make -C build/release`; the pinned tree was
  configured at a fixed absolute path (recorded in `build_tc.sh`), and an identical build needs the same
  absolute path. `build_tc.sh` copies the base tree, applies the patch, then runs `make -C build/release -j256` inside
  `bwrap --dev-bind / / --bind COPY ORIGINAL` so cmake sees its original paths (incremental, about 3 min).
- **Install and pin.** The tree `build/release/stage1/{bin,include,lib}` goes to
  `/scratch/fastverify-next/tc/lean4-s01zy-3cf5641cbd-pgo/` (it needs GLIBC_2.38 and GLIBCXX_3.4.31) and is pinned file by
  file in `../unofficial/lean4-s01zy-3cf5641cbd-pgo.json` (`lib/toolchain.py pin-unofficial`; tree sha256
  `b9ef49fc5c8c4952a5b8b53aa1f7817d2008dec4384946206d3769d3624ea1bf`, 47,274 files). `bin/lean` (sha256 `a5bc57c3...`) is
  the same as `d5e35ef223-pgo`'s; the zygote code is in `lib/lean/libleanshared.so` (sha256 `4f232823...`). A rebuild
  that needs only glibc 2.17: [`../portable-recipe/`](../portable-recipe/README.md).
- **Zygote client.** `zyc.c`, compiled per build run by `build/build.sh` (system gcc, else the toolchain's `leanc`).
- **Gating.** Everything zygote-related is gated by environment variables that only `build/sched.py` sets
  (`LEAN_ZYGOTE_SOCK`, `LEAN_ZYGOTE_BASE`, `LEAN_ZYGOTE_PREFIX`, `LEAN_ZYGOTE_THP`, `LEAN_ZYGOTE_REPLICAS`,
  `LEAN_ZYGOTE_RUSAGE`); without them the binary behaves like `d0619cbcf0`. How the build uses it:
  [build/README.md](../../build/README.md).

sha256 of the files in this directory:

```
24fe5fbd1168f32fdc96239ce83c8d6446f0a2f01f4e45f3e103d8b412774df9  s01zy.patch
2b67ee7ff736ab078e9a11831d9ffe406e40283954c2c305539357e18267448b  build_tc.sh
8f11fd5fef065a378aa08ae9e11c3f21a5b1e185ed80e609ce5dbbf9cafd86fa  zyc.c
```
