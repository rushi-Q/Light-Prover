#!/bin/bash
# rebuild-pgolibs.sh PARENT [SRC] - rebuild the OFFICIAL v4.36.0 kernel+runtime libraries (leancpp, leanrt) with the S03
# PGO+ThinLTO flags in a FRESH build dir PARENT/b-ltopgo (check/sound/src/kvar2.sh recipe, compiler/link options only),
# then relink the pleanchecker objects against them and compare with the pins. SRC = `git archive v4.36.0 src` tree
# (default BUNDLE/kopt/src).
# Environment: BUNDLE (required) = the build-environment bundle (README.md: cenv/, deps/, kb/, dl/cmake/, kopt/{src,
# mimalloc,kernel.profdata}); PCHK_OBJS (required) = directory with the four pleanchecker objects (FastParse, Main, Par,
# PersistentRead .c.o.export, e.g. from rebuild-pchk.sh); PROFDATA = another profile; J = make jobs (default 32).
set -eu
: "${BUNDLE:?build-environment bundle root (see fastverify/PROVENANCE.md) (required)}"
: "${PCHK_OBJS:?directory with the four pleanchecker *.c.o.export objects (required)}"
P=$1; SRC=${2:-$BUNDLE/kopt/src}; mkdir -p "$P"
E=$BUNDLE/cenv; T=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; D=$BUNDLE/deps/root/usr; G=$BUNDLE/kb/gmp
PROF=${PROFDATA:-$BUNDLE/kopt/kernel.profdata}
export PATH=$BUNDLE/kb/bin:$BUNDLE/dl/cmake/cmake-3.31.6-linux-x86_64/bin:$E/bin:/usr/bin:/bin
export PKG_CONFIG_PATH=$G/lib/pkgconfig:$D/lib/x86_64-linux-gnu/pkgconfig
STD="--sysroot=/ -I$D/include/x86_64-linux-gnu -stdlib=libstdc++ --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/11"
LNK="-fuse-ld=lld -rtlib=libgcc -unwindlib=libgcc"
XF="-flto=thin -fprofile-instr-use=$PROF -Wno-profile-instr-unprofiled -Wno-profile-instr-out-of-date"
B=$P/b-ltopgo; rm -rf "$B"; mkdir -p "$B"
# mimalloc: the ExternalProject prefix lives next to the build dir; seed it from the bundle's download (v3.4.5, sha256-pinned by CMakeLists)
[ -d "$P/mimalloc" ] || cp -a "$BUNDLE/kopt/mimalloc" "$P/mimalloc"
echo "host $(hostname) $(date -u +%FT%TZ); clang: $($E/bin/clang --version | head -1); cmake: $(cmake --version | head -1)"
t0=$(date +%s)
cmake -S "$SRC" -B "$B" -DSTAGE=1 -DPREV_STAGE=$T -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=$E/bin/clang -DCMAKE_CXX_COMPILER=$E/bin/clang++ \
  -DCMAKE_CXX_FLAGS="$STD $XF" -DCMAKE_C_FLAGS="--sysroot=/ $XF" -DCMAKE_EXE_LINKER_FLAGS="$STD $LNK" \
  -DOPENSSL_ROOT_DIR=$D -DPKG_CONFIG_EXECUTABLE=$BUNDLE/kb/bin/pkg-config \
  -DCCACHE=OFF -DUSE_GITHASH=OFF -DLEANTAR=/usr/bin/true -DINSTALL_LEANTAR=OFF -DINSTALL_CADICAL=OFF > "$B.cfg.log" 2>&1
cmake -DCMAKE_AR=$E/bin/llvm-ar -DCMAKE_RANLIB=/bin/true "$B" >> "$B.cfg.log" 2>&1
make -C "$B" -j${J:-32} leancpp leanrt > "$B.build.log" 2>&1
echo "libs built in $(( $(date +%s) - t0 )) s"
sha256sum "$B/lib/lean/libleancpp.a" "$B/lib/lean/libleanrt.a"
echo "S03 (pinned build inputs): ade683c9b0cc0d3e206ec039cab1f2214b62cfbb8ae91d4e19ba69032185aca7 libleancpp.a / 912da49055d2dc7f87db21b72671958273768c540231bd17c3fb147949e3fa3 libleanrt.a"
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
"$H/relink-pgo.sh" "$PCHK_OBJS" "$P/link" "$B/lib/lean"
