#!/bin/bash
# build-tc.sh NAME ORIGPATH [J]  (portable toolchains)
#   Builds the prepared source $PORT_WORK/src/NAME (prep-src.sh) with the harness recipe `CC=clang CXX=clang++ cmake --preset release
#   && make -C build/release` INSIDE the manylinux_2_28 userland (glibc 2.28, gcc-toolset-13; broot.sh = bwrap root, like docker run)
#   at the ORIGINAL build path ORIGPATH (bind mount; the C++ sources' __FILE__ strings and the stage1 Lake paths are then the same as
#   in the pinned tree). Portability options (the only differences to the original configure):
#     * clang 18.1.8 + lld 18.1.8 (conda-forge) instead of Ubuntu clang 18.1.3, against the old-glibc root;
#     * libstdc++ (gcc-toolset-13 13.3.1; 12 for nopgo) linked statically AND hidden like the release's libc++:
#       -DLEAN_CXX_STDLIB='-Wl,-Bstatic -lstdc++ -Wl,-Bdynamic -Wl,--exclude-libs,libstdc++.a';
#     * glibc-2.17 libm.so.6 as the LINK-time libm (the fvcc wrappers add -L/opt/glibc217/lib to link steps only);
#     * SOURCE_DATE_EPOCH = the commit time (reproducible __DATE__/__TIME__ in mimalloc's banner and cadical);
#     * GMP 6.3.0 / libuv 1.48.0 / OpenSSL 3.6.0 = the official release's static archives (/opt/fvdeps, deps.sh) instead of the
#       host's shared libraries; -DCCACHE=OFF.
#   Everything else (sources, patches, githash pin, PGO profile pgo/lean.profdata, ThinLTO default, -O3, flags) is the recipe's.
#   PORT_WORK (required) = the recipe's work root: src/NAME (+ NAME.SDE) from prep-src.sh, build/ (output), and the defaults
#   roots/ml228 (ROOTFS, mkroot.sh), deps/v1 (DEPS, deps.sh), glibc217/linkonly (mkroot.sh), cenv18/cenv14 (mkenv.sh).
#   FVCC (default: this directory's fvcc/bin, with the symlinks of fvcc/LINKS.txt) = the compiler wrappers.
set -euo pipefail
NAME=$1 ORIG=$2 J=${3:-128}
D=${PORT_WORK:?work root of the portable-toolchain recipe (required)}; P=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); ROOTFS=${ROOTFS:-$D/roots/ml228}; FVCC=${FVCC:-$P/fvcc/bin}; DEPS=${DEPS:-$D/deps/v1}; EXTRA_CMAKE=${EXTRA_CMAKE:-}; GXB=(); [ -n "${GCC_OVERRIDE:-}" ] && GXB=(--bind "$GCC_OVERRIDE" /opt/rh/gcc-toolset-13/root/usr/lib/gcc/x86_64-redhat-linux/13); W=$D/build/$NAME; LOG=$D/build/$NAME.log
# reproducibility: __DATE__/__TIME__ (mimalloc's banner, cadical's version) = the source commit's time, not the build time
SDE=${SOURCE_DATE_EPOCH:-$(cat $D/src/$NAME.SDE 2>/dev/null || echo 0)}
mkdir -p $D/build
if [ ! -f $W/OK.portable ]; then
  [ -e $W ] && chmod -R u+w $W && rm -rf $W
  cp -a $D/src/$NAME $W
  t0=$(date +%s)
  $P/broot.sh $ROOTFS --bind $W $ORIG --bind $DEPS /opt/fvdeps --bind $FVCC /opt/fvcc/bin \
      --bind $FVCC/clang /usr/bin/clang --bind $FVCC/clang++ /usr/bin/clang++ --bind $D/glibc217/linkonly /opt/glibc217/lib "${GXB[@]}" -- bash -c "
    set -euo pipefail; cd $ORIG
    export CC=/usr/bin/clang CXX=/usr/bin/clang++ PKG_CONFIG_PATH=/opt/fvdeps/lib/pkgconfig CMAKE_PREFIX_PATH=/opt/fvdeps SOURCE_DATE_EPOCH=$SDE
    { echo \"root: \$(. /etc/os-release; echo \$PRETTY_NAME) \$(ldd --version | head -1)\"; clang --version | head -1; ld.lld --version;
      c++ --version | head -1; echo \"rootfs $ROOTFS fvcc $FVCC SOURCE_DATE_EPOCH $SDE\"; cmake --version | head -1; git --version; echo \"pwd \$(pwd) nproc \$(nproc)\"; } > BUILDINFO.portable
    cmake --preset release -DCCACHE=OFF -DLEAN_CXX_STDLIB='-Wl,-Bstatic -lstdc++ -Wl,-Bdynamic -Wl,--exclude-libs,libstdc++.a' \
      -DOPENSSL_ROOT_DIR=/opt/fvdeps -DOPENSSL_USE_STATIC_LIBS=TRUE $EXTRA_CMAKE > cfg.portable.log 2>&1 || { tail -30 cfg.portable.log; exit 1; }
    make -C build/release -j$J > make.portable.log 2>&1 || { grep -n -i -m20 -E 'error|failed' make.portable.log; tail -20 make.portable.log; exit 1; }
  " > $LOG 2>&1 || { echo "BUILD FAILED $NAME (log $LOG)"; tail -40 $LOG; exit 1; }
  echo "$(date -u +%FT%TZ) $(( $(date +%s) - t0 ))s" > $W/OK.portable
fi
TC=$W/build/release/stage1
echo "built $NAME in $(cat $W/OK.portable)"; "$TC/bin/lean" --version
for f in bin/lean lib/lean/libleanshared.so lib/lean/libInit_shared.so bin/cadical; do
  echo "$f: $(sha256sum $TC/$f | cut -c1-16) NEEDED: $(readelf -d $TC/$f | awk '/NEEDED/{gsub(/[\[\]]/,"",$5); printf "%s ", $5}') max $(objdump -T $TC/$f | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1) $(objdump -T $TC/$f | grep -o 'GLIBCXX_[0-9.]*' | sort -uV | tail -1) $(objdump -T $TC/$f | grep -o 'GCC_[0-9.]*' | sort -uV | tail -1)"
done
