#!/bin/bash
# mkenv.sh PREFIX18 PREFIX14   - the compilers (conda-forge binaries, built for old glibc, run inside the manylinux_2_28 root):
#   PREFIX18: clang/clangxx/lld/llvm-tools 18.1.8 (clang-18 build default_h99862b1_18, lld hef48ded_1), cmake 3.31.8, make
#   PREFIX14: clang/clangxx/lld/llvm-tools 14.0.6 (clang-14 build default_h7634d5b_1, lld h07fd6de_1)  [nopgo only]
#   The fvcc/fvcc437 and fvcc14 wrappers take them from $FVCC_CENV18 / $FVCC_CENV14 (default $PORT_WORK/cenv18 and
#   $PORT_WORK/cenv14; inside the build root they must lie under $PORT_WORK, the directory broot.sh binds).
#   Exact package lists: PREFIX/conda-meta/*.json (url + sha256 of every package).
set -euo pipefail
P18=$1 P14=$2; W=$(mktemp -d)
curl -sSL -o $W/mm.tar.bz2 https://github.com/mamba-org/micromamba-releases/releases/download/2.3.3-0/micromamba-linux-64.tar.bz2
echo "e7274528ceb9c20d048a428d6c22d7e02e268f8ffb762c4c365422347c8b8ba2  $W/mm.tar.bz2" | sha256sum -c
tar -xjf $W/mm.tar.bz2 -C $W bin/micromamba; export MAMBA_ROOT_PREFIX=$W/root
$W/bin/micromamba create -y -q -p "$P18" -c conda-forge --override-channels clang=18.1.8 clangxx=18.1.8 lld=18.1.8 llvm-tools=18.1.8 cmake=3.31 make
$W/bin/micromamba create -y -q -p "$P14" -c conda-forge --override-channels clang=14.0.6 clangxx=14.0.6 lld=14.0.6 llvm-tools=14.0.6
"$P18/bin/clang" --version | head -1; "$P14/bin/clang" --version | head -1
