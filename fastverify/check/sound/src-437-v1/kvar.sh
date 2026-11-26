#!/bin/bash
# S03 kvar.sh VARIANT "CFLAGS" "LINKFLAGS" OBJLIST OUT
#   Builds the OFFICIAL Lean v4.36.0 C++ kernel + runtime libraries (leancpp, leanrt) from the unmodified tag sources
#   (/scratch/S03/kopt/src = `git archive v4.36.0 src` of lineB/lean4, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9;
#   mimalloc = official v3.4.5 GitHub archive, sha256 19a43af0645c57d348e729d5b31e23e912582911bb1047f795790834d3416221)
#   with COMPILER/LINK FLAGS ONLY (no source change), then links a Lake-compiled Lean exe (object list) against them plus
#   the release's own Lean libraries (libLean/libInit/libStd/libLake/libLeanExport of the official v4.36.0 toolchain).
#   Compiler: conda-forge clang 18.1.8 (/scratch/c06/envs/cenv, has the PGO runtime + llvm-profdata), system libstdc++ 11,
#   static GMP 6.3.0 / libuv / openssl from C08's local deps (as pleanchecker-k).  Node 2 only (paths).
set -euxo pipefail
V=$1; XF=${2:-}; XL=${3:-}; OBJS=$4; OUT=$5
R=/scratch/S03/kopt
T=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
E=/scratch/c06/envs/cenv
D=/scratch/c08/deps/root/usr; G=/scratch/c08/kb/gmp
export PATH=/scratch/c08/kb/bin:/scratch/c08/dl/cmake/cmake-3.31.6-linux-x86_64/bin:$E/bin:/usr/bin:/bin
export PKG_CONFIG_PATH=$G/lib/pkgconfig:$D/lib/x86_64-linux-gnu/pkgconfig
STD="--sysroot=/ -I$D/include/x86_64-linux-gnu -stdlib=libstdc++ --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/11"
LNK="-fuse-ld=lld -rtlib=libgcc -unwindlib=libgcc"
B=$R/b-$V
if [ ! -f $B/lib/lean/libleancpp.a ]; then
rm -rf $B; mkdir -p $B
cmake -S $R/src -B $B -DSTAGE=1 -DPREV_STAGE=$T -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=$E/bin/clang -DCMAKE_CXX_COMPILER=$E/bin/clang++ \
  -DCMAKE_CXX_FLAGS="$STD $XF" -DCMAKE_C_FLAGS="--sysroot=/ $XF" -DCMAKE_EXE_LINKER_FLAGS="$STD $LNK" \
  -DOPENSSL_ROOT_DIR=$D -DPKG_CONFIG_EXECUTABLE=/scratch/c08/kb/bin/pkg-config \
  -DCCACHE=OFF -DUSE_GITHASH=OFF -DLEANTAR=/usr/bin/true -DINSTALL_LEANTAR=OFF -DINSTALL_CADICAL=OFF > $B.cfg.log 2>&1
if [[ "$XF" == *flto* ]]; then cmake -DCMAKE_AR=$E/bin/llvm-ar -DCMAKE_RANLIB=/bin/true $B >> $B.cfg.log 2>&1; fi
make -C $B -j${J:-16} leancpp leanrt > $B.build.log 2>&1
fi
L=$B/lib/lean; TL=$T/lib/lean; DL=$D/lib/x86_64-linux-gnu
$E/bin/clang++ $STD $LNK $XF $XL -o $OUT $OBJS \
  -Wl,--start-group $L/libleancpp.a $TL/libLean.a -Wl,--end-group $TL/libStd.a \
  -Wl,--start-group $TL/libInit.a $L/libleanrt.a -Wl,--end-group $TL/libLake.a $TL/libLeanExport.a \
  $G/lib/libgmp.a $DL/libuv_a.a $DL/libssl.a $DL/libcrypto.a -lpthread -ldl -lrt -lm -Wl,--gc-sections -pthread
ls -la $OUT
