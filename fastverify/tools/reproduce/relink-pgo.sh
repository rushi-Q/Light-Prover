#!/bin/bash
# relink-pgo.sh OBJDIR OUTDIR LIBDIR - the PGO+ThinLTO link of pleanchecker (check/sound/README.md,
# kvar2.sh 'ltopgo' link line) from the 4 pleanchecker objects in OBJDIR against the official-source kernel libraries
# in LIBDIR (e.g. PARENT/b-ltopgo/lib/lean of rebuild-pgolibs.sh) + the RELEASE 4.36 Lean libraries; tries both object
# orders; prints sha256.
# Environment: BUNDLE (required) = the build-environment bundle (README.md): BUNDLE/cenv = conda clang 18.1.8,
# BUNDLE/deps/root/usr = dependency headers, BUNDLE/kopt/kernel.profdata = the PGO profile (PROFDATA overrides it).
set -eu
O=$1; OUT=$2; L=${3:?usage: relink-pgo.sh OBJDIR OUTDIR LIBDIR}; mkdir -p "$OUT"
: "${BUNDLE:?build-environment bundle root with cenv/, deps/, kopt/ (see fastverify/PROVENANCE.md) (required)}"
E=$BUNDLE/cenv; T=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; D=$BUNDLE/deps/root/usr; TL=$T/lib/lean
PROF=${PROFDATA:-$BUNDLE/kopt/kernel.profdata}
STD="--sysroot=/ -I$D/include/x86_64-linux-gnu -stdlib=libstdc++ --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/11"
LNK="-fuse-ld=lld -rtlib=libgcc -unwindlib=libgcc"
XF="-flto=thin -fprofile-instr-use=$PROF -Wno-profile-instr-unprofiled -Wno-profile-instr-out-of-date"; XL="-Wl,--thinlto-jobs=16"
echo "libs: $(sha256sum $L/libleancpp.a $L/libleanrt.a | cut -c1-16 | tr '\n' ' ')  profdata: $(sha256sum $PROF | cut -c1-16)"
link() { # link NAME OBJS...
  local n=$1; shift
  $E/bin/clang++ $STD $LNK $XF $XL -o "$OUT/$n" "$@" \
    -Wl,--start-group $L/libleancpp.a $TL/libLean.a -Wl,--end-group $TL/libStd.a \
    -Wl,--start-group $TL/libInit.a $L/libleanrt.a -Wl,--end-group $TL/libLake.a $TL/libLeanExport.a \
    $T/lib/libgmp.a $T/lib/libuv.a $T/lib/libssl.a $T/lib/libcrypto.a -lpthread -ldl -lrt -lm -Wl,--gc-sections -pthread
  sha256sum "$OUT/$n"
}
cd "$O"
link plc-alpha FastParse.c.o.export Main.c.o.export Par.c.o.export PersistentRead.c.o.export
link plc-lake  Main.c.o.export Par.c.o.export FastParse.c.o.export PersistentRead.c.o.export
link plc-main-last Par.c.o.export FastParse.c.o.export PersistentRead.c.o.export Main.c.o.export
echo "reference build: c4730cc9543b066f4849ccb50227813fb63fc39a96811c46e4a2dd26d90a19d0"
