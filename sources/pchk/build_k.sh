#!/bin/sh
# BUILD (kind kernel-src): pleanchecker (unchanged Lean code) linked against a Lean 4.36.0 C++ kernel/runtime built
# from k/src = lean4 v4.36.0 src/ (C++ parts + build files) + the kernel performance patches (branch c/c08k of the lean4 fork,
# see k/README). The Lean-compiled libraries (libLean/libInit/libStd/...) are the OFFICIAL toolchain's; only libleancpp/libleanrt
# (kernel, runtime) are rebuilt. ccmp is built as before (official libs; it never runs the kernel itself).
set -eux
# nanoda (official 4c544ed + speedups, nanoda/), offline; crates fetched beforehand from ./Cargo.lock
cargo build --release --locked --offline
ls -la target/release/nanoda_bin
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
CC=${CC:-clang}; CXX=${CXX:-clang++}
J=${K_JOBS:-$(nproc)}
# 1. kernel + runtime C++ libs (cmake STAGE=1 configure; only the C++ targets are built)
rm -rf k/b k/mimalloc && mkdir -p k/mimalloc/src
tar xzf k/vendor/mimalloc-v3.4.5.tar.gz -C k/mimalloc/src && mv k/mimalloc/src/mimalloc-3.4.5 k/mimalloc/src/mimalloc
cmake -S k/src -B k/b -DSTAGE=1 -DPREV_STAGE=$TC -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=$CC -DCMAKE_CXX_COMPILER=$CXX \
  -DCCACHE=OFF -DUSE_GITHASH=OFF -DLEANTAR=/usr/bin/true -DINSTALL_LEANTAR=OFF -DINSTALL_CADICAL=OFF ${K_CMAKE_ARGS:-}
make -C k/b -j$J leancpp leanrt
# 2. Lean code (pleanchecker, ccmp) with the official toolchain, as in build.sh
PATH=$TC/bin:/usr/bin:/bin lake build
# 3. relink pleanchecker's objects against the rebuilt kernel/runtime + the official Lean libraries
OBJS=$(grep '\.o' .lake/build/bin/pleanchecker.rsp | tr -d '"')
L=k/b/lib/lean; TL=$TC/lib/lean
$CXX ${K_LINK_ARGS:-} -o .lake/build/bin/pleanchecker-k $OBJS \
  -Wl,--start-group $L/libleancpp.a $TL/libLean.a -Wl,--end-group $TL/libStd.a \
  -Wl,--start-group $TL/libInit.a $L/libleanrt.a -Wl,--end-group $TL/libLake.a $TL/libLeanExport.a \
  -lgmp -luv -lssl -lcrypto -lpthread -ldl -lrt -lm -Wl,--gc-sections -pthread
ls -la .lake/build/bin
.lake/build/bin/pleanchecker-k --help >/dev/null 2>&1 || true
