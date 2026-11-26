#!/bin/bash
# rebuild pleanchecker-k (pchk d876802, build_k.sh steps) on a host with glibc 2.35 with a local toolchain setup (read-only use)
set -eux
# PCHK_SRC = the pchk d876802 checkout, KBUILD = the local kernel-build setup (configure.sh, link.sh, compiler, cmake)
PCHK=${PCHK_SRC:-${FV_SCRATCH:-${TMPDIR:-/tmp}}/pchk}; KB=${KBUILD:-${FV_SCRATCH:-${TMPDIR:-/tmp}}/kernel-build}
cd $PCHK
bash $KB/build/configure.sh $PCHK/k $PCHK/k/b
export PATH=$KB/kb/bin:$KB/dl/cmake/cmake-3.31.6-linux-x86_64/bin:$PATH
make -C k/b -j${J:-32} leancpp leanrt
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PATH=$TC/bin:/usr/bin:/bin lake build
OBJS=$(grep '\.o' .lake/build/bin/pleanchecker.rsp | tr -d '"')
LINKX= bash $KB/build/link.sh "$OBJS" .lake/build/bin/pleanchecker-k $PCHK/k/b/lib/lean
ls -la .lake/build/bin
