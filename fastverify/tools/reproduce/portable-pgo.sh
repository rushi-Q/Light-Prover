#!/bin/bash
# portable-pgo.sh OUTDIR  - PORTABLE rebuild of the sound check's Lean-kernel leg binaries: the OFFICIAL v4.36.0 kernel +
# runtime libraries (leancpp, leanrt) compiled with the exact S03 PGO+ThinLTO options (same sources, same profile, same
# conda clang 18.1.8) but INSIDE a manylinux_2_28 container (glibc 2.28 headers/libs, gcc-toolset libstdc++ linked
# STATICALLY), then the pleanchecker objects (plain / targeted v4 / overlap v1, byte-identical to the Lake builds) linked
# against them + the release's own static Lean libraries, GMP, libuv, OpenSSL. Result: binaries that need only
# GLIBC_2.17 and no libstdc++.so, like the official release. Needs docker.
# BUNDLE (2nd argument or environment, required) = the build-environment bundle root:
#   BUNDLE/{cenv,kb,deps,dl,kopt/{src,tests,script,mimalloc,kernel.profdata},objs-*} (see README.md).
set -eu
OUT=${1:?usage: portable-pgo.sh OUTDIR [BUNDLE]}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
IMG=${IMG:-quay.io/pypa/manylinux_2_28_x86_64}   # glibc 2.28 (manylinux2014/glibc 2.17 lacks sys/random.h and its gcc 10 libstdc++ lacks std::bit_cast, both needed by the v4.36.0 runtime)
B=${2:-${BUNDLE:?build-environment bundle root, 2nd argument or environment (required)}}; B=$(cd "$B" && pwd)
# The kernel libraries embed the SOURCE PATH (assert/unreachable messages use __FILE__), so the sources are always seen at the
# canonical path of the pinned build, /scratch/D10/bundle/kopt, inside the container (a writable bind mount, because
# tests/CMakeLists.txt configures files in place). That path is part of the pinned binaries' bytes: do not change it.
# Without it a rebuild elsewhere differs by exactly those strings. The bundle and OUTDIR are mounted at their own paths.
KOPT_HOST=$B/kopt
docker run -i --rm --user "$(id -u):$(id -g)" -v "$B:$B" -v "$OUT:$OUT" -v "$KOPT_HOST:/scratch/D10/bundle/kopt" -v "$HOME/.elan:$HOME/.elan:ro" -e HOME="$HOME" -e OUT="$OUT" -e J="${J:-32}" -e BUNDLE="$B" "$IMG" bash -s <<'IN'
set -eu
T=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
E=$BUNDLE/cenv; D=$BUNDLE/deps/root/usr; G=$BUNDLE/kb/gmp; KB=$BUNDLE/kb; CM=$BUNDLE/dl/cmake; OBJ=$BUNDLE
KOPT=/scratch/D10/bundle/kopt   # canonical source path of the pinned build (bind mount, see above)
SRC=$KOPT/src; PROF=$KOPT/kernel.profdata
TS=$(ls -d /opt/rh/gcc-toolset-* /opt/rh/devtoolset-* 2>/dev/null | sort -V | tail -1); GCCDIR=$(ls -d $TS/root/usr/lib/gcc/x86_64-redhat-linux/* | sort -V | tail -1)
export PATH=$CM/cmake-3.31.6-linux-x86_64/bin:$E/bin:$TS/root/usr/bin:/usr/bin:/bin:$KB/bin   # the bundle's pkg-config (built on glibc 2.35) cannot run here: the container's own one is used
# libuv for configure = the SAME 1.43 headers the bundle's deps provide (as in the original build), through a .pc whose paths are
# valid on this machine (the deps' own .pc files carry absolute paths of the original build host); OpenSSL libs = the release's static ones
# (the deps' .so symlinks point to the host's /usr/lib and dangle inside the container). Neither changes the kernel libraries.
mkdir -p $OUT/pkgconfig
printf 'prefix=%s\nincludedir=%s/include\nlibdir=%s/lib\nName: libuv\nDescription: libuv headers of the deps + the release libuv.a\nVersion: 1.43.0\nLibs: -L${libdir} -luv\nCflags: -I${includedir}\n' "$T" "$D" "$T" > $OUT/pkgconfig/libuv.pc
export PKG_CONFIG_PATH=$OUT/pkgconfig:$G/lib/pkgconfig:$D/lib/x86_64-linux-gnu/pkgconfig
STD="--sysroot=/ -I$D/include/x86_64-linux-gnu -stdlib=libstdc++ --gcc-install-dir=$GCCDIR"
LNK="-fuse-ld=lld -rtlib=libgcc -unwindlib=libgcc -static-libstdc++ -static-libgcc"
XF="-flto=thin -fprofile-instr-use=$PROF -Wno-profile-instr-unprofiled -Wno-profile-instr-out-of-date"; XL="-Wl,--thinlto-jobs=16"
P=$OUT/kopt; mkdir -p $P; [ -d $P/mimalloc ] || cp -a $KOPT/mimalloc $P/mimalloc
B=$P/b-ltopgo; rm -rf $B; mkdir -p $B
echo "container: $(. /etc/os-release; echo $PRETTY_NAME) $(ldd --version | head -1); clang $($E/bin/clang --version | head -1 | cut -c1-40); gcc $(gcc --version | head -1); GCCDIR=$GCCDIR"
t0=$(date +%s)
cmake -S $SRC -B $B -DSTAGE=1 -DPREV_STAGE=$T -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=$E/bin/clang -DCMAKE_CXX_COMPILER=$E/bin/clang++ \
  -DCMAKE_CXX_FLAGS="$STD $XF" -DCMAKE_C_FLAGS="--sysroot=/ $XF" -DCMAKE_EXE_LINKER_FLAGS="$STD $LNK" -DOPENSSL_ROOT_DIR=$D -DOPENSSL_INCLUDE_DIR=$D/include -DOPENSSL_CRYPTO_LIBRARY=$T/lib/libcrypto.a -DOPENSSL_SSL_LIBRARY=$T/lib/libssl.a -DPKG_CONFIG_EXECUTABLE=/usr/bin/pkg-config -DGMP_INCLUDE_DIR=$G/include -DGMP_LIBRARIES=$T/lib/libgmp.a \
  -DCCACHE=OFF -DUSE_GITHASH=OFF -DLEANTAR=/usr/bin/true -DINSTALL_LEANTAR=OFF -DINSTALL_CADICAL=OFF > $B.cfg.log 2>&1 || { echo "cmake FAILED"; grep -i -B2 -A8 "CMake Error" $B.cfg.log | head -40; exit 1; }
cmake -DCMAKE_AR=$E/bin/llvm-ar -DCMAKE_RANLIB=/bin/true $B >> $B.cfg.log 2>&1
make -C $B -j$J leancpp leanrt > $B.build.log 2>&1 || { echo "make FAILED"; grep -i -m8 "error" $B.build.log; exit 1; }
echo "libs built in $(( $(date +%s) - t0 )) s"; sha256sum $B/lib/lean/libleancpp.a $B/lib/lean/libleanrt.a
L=$B/lib/lean; TL=$T/lib/lean
link() { # link NAME OBJDIR
  local n=$1 o=$2; mkdir -p $OUT/bin
  # Lake's object order for the plain build is Main Par FastParse PersistentRead; other object sets: the same names first, then the rest sorted
  local objs=""; for f in Main.c.o.export Par.c.o.export FastParse.c.o.export PersistentRead.c.o.export; do [ -f $o/$f ] && objs="$objs $f"; done
  for f in $(ls $o | grep '\.o\.export$' | sort); do case " $objs " in *" $f "*) ;; *) objs="$objs $f";; esac; done
  echo "$n objects:$objs"
  (cd $o && $E/bin/clang++ $STD $LNK $XF $XL -o $OUT/bin/$n $objs \
    -Wl,--start-group $L/libleancpp.a $TL/libLean.a -Wl,--end-group $TL/libStd.a -Wl,--start-group $TL/libInit.a $L/libleanrt.a -Wl,--end-group $TL/libLake.a $TL/libLeanExport.a \
    $T/lib/libgmp.a $T/lib/libuv.a $T/lib/libssl.a $T/lib/libcrypto.a -lpthread -ldl -lrt -lm -Wl,--gc-sections -pthread)
  echo "$n: $(sha256sum $OUT/bin/$n | cut -d' ' -f1) max $(objdump -T $OUT/bin/$n | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1) $(objdump -T $OUT/bin/$n | grep -o 'GLIBCXX_[0-9.]*' | sort -uV | tail -1) needed: $(objdump -p $OUT/bin/$n | awk '/NEEDED/{printf "%s ", $2}')"
}
link pleanchecker $OBJ/objs-plain
link pleanchecker-targeted-v4 $OBJ/objs-d125c57
link pleanchecker-overlap-v1 $OBJ/objs-0db0e1b
echo "total $(( $(date +%s) - t0 )) s"
IN
