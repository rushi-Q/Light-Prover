#!/bin/bash
# portable-pgo-437.sh VARIANT BUNDLE OUTROOT  - PORTABLE (manylinux_2_28, static libstdc++) build of the
# OFFICIAL v4.37.0-rc1 kernel + runtime libraries (leancpp, leanrt; unmodified tag sources, mimalloc v3.4.5 as the tag's
# CMakeLists fetches, libuv 1.53.0 headers = the release's own libuv.a) with conda clang 18.1.8 and the given flags, then the
# pleanchecker-437 Lake objects (byte-identical to `lake build` with the official 4.37 toolchain) linked against them + the
# release's static libraries. VARIANT: rel (no extra flags, sanity) | ltopgo (-flto=thin + the S03 4.36 kernel.profdata; stale
# functions unprofiled) | pgoinstr (-fprofile-instr-generate, for a fresh 4.37 profile). Same recipe as tools/reproduce/portable-pgo.sh
# (4.36), plus a libuv.pc for 1.53 so FindLibUV (pkg_search_module) does not pick the deps' 1.43.
# BUNDLE / OUTROOT: 2nd / 3rd argument or environment (required). TC37 = the official v4.37.0-rc1 toolchain tree (default: the
# verified copy under the install prefix /scratch/fastverify-next/elan); PROF = another .profdata; J = make jobs (default 32).
set -eu
V=${1:?usage: portable-pgo-437.sh rel|ltopgo|ltopgo2|pgoinstr BUNDLE OUTROOT}
BUNDLE=${2:-${BUNDLE:?build-environment bundle root, 2nd argument or environment (required)}}; BUNDLE=$(cd "$BUNDLE" && pwd)
OUTROOT=${3:-${OUTROOT:?output root, 3rd argument or environment (required)}}; mkdir -p "$OUTROOT"; OUTROOT=$(cd "$OUTROOT" && pwd)
IMG=${IMG:-quay.io/pypa/manylinux_2_28_x86_64}
# The kernel libraries embed the SOURCE PATH (__FILE__ in assert/unreachable strings): the bundle is always seen at the canonical
# path /scratch/D10/pgo437/bundle inside the container (bind mount), so a rebuild on another machine reproduces the same bytes
# (lesson from the 4.36 portable-v1 reproduction). The toolchain is likewise mounted at its canonical in-container path T.
CANON=/scratch/D10/pgo437/bundle
TCANON=/scratch/fastverify-next/elan/toolchains/leanprover--lean4---v4.37.0-rc1; TC37=${TC37:-$TCANON}
PROFMNT=(); [ -n "${PROF:-}" ] && PROFMNT=(-v "$PROF:$PROF:ro")
docker run -i --rm --user "$(id -u):$(id -g)" -v "$OUTROOT:$OUTROOT" -v "$BUNDLE:$CANON" -v "$TC37:$TCANON:ro" "${PROFMNT[@]}" -e V="$V" -e BUNDLE="$CANON" -e OUTROOT="$OUTROOT" -e J="${J:-32}" -e PROF="${PROF:-}" "$IMG" bash -s <<'IN'
set -eu
T=/scratch/fastverify-next/elan/toolchains/leanprover--lean4---v4.37.0-rc1   # canonical in-container path (mount, see above)
E=$BUNDLE/cenv; D=$BUNDLE/deps/root/usr; G=$BUNDLE/kb/gmp; KB=$BUNDLE/kb; CM=$BUNDLE/cmake; SRC=$BUNDLE/src; PROF=${PROF:-$BUNDLE/kernel.profdata}; IR=$BUNDLE/ir   # PROF env: another .profdata (e.g. a fresh 4.37 one)
TS=$(ls -d /opt/rh/gcc-toolset-* 2>/dev/null | sort -V | tail -1); GCCDIR=$(ls -d $TS/root/usr/lib/gcc/x86_64-redhat-linux/* | sort -V | tail -1)
export PATH=$CM/cmake-3.31.6-linux-x86_64/bin:$E/bin:$TS/root/usr/bin:/usr/bin:/bin:$KB/bin
mkdir -p $OUTROOT/pkgconfig $OUTROOT/out
cat > $OUTROOT/pkgconfig/libuv.pc <<PC
prefix=$T
includedir=$BUNDLE/libuv-include
libdir=$T/lib
Name: libuv
Description: libuv 1.53.0 headers (tag v1.53.0) + the official v4.37.0-rc1 release's static libuv.a
Version: 1.53.0
Libs: -L\${libdir} -luv
Cflags: -I\${includedir}
PC
export PKG_CONFIG_PATH=$OUTROOT/pkgconfig:$G/lib/pkgconfig:$D/lib/x86_64-linux-gnu/pkgconfig
STD="--sysroot=/ -I$D/include/x86_64-linux-gnu -stdlib=libstdc++ --gcc-install-dir=$GCCDIR"
LNK="-fuse-ld=lld -rtlib=libgcc -unwindlib=libgcc -static-libstdc++ -static-libgcc"
case "$V" in
  rel) XF=""; XL="";;
  ltopgo|ltopgo2) XF="-flto=thin -fprofile-instr-use=$PROF -Wno-profile-instr-unprofiled -Wno-profile-instr-out-of-date"; XL="-Wl,--thinlto-jobs=16";;
  pgoinstr) XF="-fprofile-instr-generate"; XL="-fprofile-instr-generate";;
  *) echo "unknown variant $V"; exit 2;;
esac
P=$OUTROOT/kopt; mkdir -p $P; [ -d $P/mimalloc ] || cp -a $BUNDLE/mimalloc $P/mimalloc   # CMake expects <build>/../mimalloc/src/mimalloc
B=$P/b-$V
echo "container: $(. /etc/os-release; echo $PRETTY_NAME) $(ldd --version | head -1); clang $($E/bin/clang --version | head -1 | cut -c1-40); GCCDIR=$GCCDIR; variant $V XF=[$XF]"
echo "pkg-config libuv: $(pkg-config --modversion libuv) cflags $(pkg-config --cflags libuv)"
t0=$(date +%s)
if [ ! -f $B/lib/lean/libleancpp.a ] || [ ! -f $B/lib/lean/libleanrt.a ]; then
  rm -rf $B; mkdir -p $B
  cmake -S $SRC -B $B -DSTAGE=1 -DPREV_STAGE=$T -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=$E/bin/clang -DCMAKE_CXX_COMPILER=$E/bin/clang++ \
    -DCMAKE_CXX_FLAGS="$STD $XF" -DCMAKE_C_FLAGS="--sysroot=/ $XF" -DCMAKE_EXE_LINKER_FLAGS="$STD $LNK" -DOPENSSL_ROOT_DIR=$D -DOPENSSL_INCLUDE_DIR=$D/include -DOPENSSL_CRYPTO_LIBRARY=$T/lib/libcrypto.a -DOPENSSL_SSL_LIBRARY=$T/lib/libssl.a -DPKG_CONFIG_EXECUTABLE=/usr/bin/pkg-config -DGMP_INCLUDE_DIR=$G/include -DGMP_LIBRARIES=$T/lib/libgmp.a \
    -DCCACHE=OFF -DUSE_GITHASH=OFF -DLEANTAR=/usr/bin/true -DINSTALL_LEANTAR=OFF -DINSTALL_CADICAL=OFF > $B.cfg.log 2>&1 || { echo "cmake FAILED"; grep -i -B2 -A8 "CMake Error" $B.cfg.log | head -40; exit 1; }
  grep "LIBUV_INCLUDE_DIRS\|LIBUV_LDFLAGS" $B.cfg.log | head -2
  case "$XF" in *flto*) cmake -DCMAKE_AR=$E/bin/llvm-ar -DCMAKE_RANLIB=/bin/true $B >> $B.cfg.log 2>&1;; esac
  make -C $B -j$J leancpp leanrt > $B.build.log 2>&1 || { echo "make FAILED"; grep -i -m8 "error" $B.build.log; exit 1; }
  echo "libs built in $(( $(date +%s) - t0 )) s"
fi
sha256sum $B/lib/lean/libleancpp.a $B/lib/lean/libleanrt.a
L=$B/lib/lean; TL=$T/lib/lean; N=pleanchecker-437-$V
OBJS="$IR/Main.c.o.export $IR/PChk/Par.c.o.export $IR/FastParse.c.o.export $IR/PChk/PersistentRead.c.o.export"   # Lake's order (pleanchecker.rsp)
link() { $E/bin/clang++ $STD $LNK $XF $XL -o $1 $OBJS \
    -Wl,--start-group $L/libleancpp.a $TL/libLean.a -Wl,--end-group $TL/libStd.a -Wl,--start-group $TL/libInit.a $L/libleanrt.a -Wl,--end-group $2 $TL/libLake.a $TL/libLeanExport.a \
    $T/lib/libgmp.a $T/lib/libuv.a $T/lib/libssl.a $T/lib/libcrypto.a -lpthread -ldl -lrt -lm -Wl,--gc-sections -pthread; }
if link $OUTROOT/out/$N "" 2> $OUTROOT/out/$N.link.log; then echo "linked (no libcadical)"; else
  echo "link without libcadical failed: $(grep -m1 undefined $OUTROOT/out/$N.link.log | cut -c1-160); retrying with libcadical + libc++"
  link $OUTROOT/out/$N "$TL/libcadical.a $T/lib/libc++.a $T/lib/libc++abi.a" 2>> $OUTROOT/out/$N.link.log; fi
echo "$N: $(sha256sum $OUTROOT/out/$N | cut -d' ' -f1) size $(stat -c %s $OUTROOT/out/$N) max $(objdump -T $OUTROOT/out/$N | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1) $(objdump -T $OUTROOT/out/$N | grep -o 'GLIBCXX_[0-9.]*' | sort -uV | tail -1) needed: $(objdump -p $OUTROOT/out/$N | awk '/NEEDED/{printf "%s ", $2}')"
echo "total $(( $(date +%s) - t0 )) s"
IN
