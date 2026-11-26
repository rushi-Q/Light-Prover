#!/bin/bash
# mkroot.sh OUTDIR   (on a host with docker)
#   The OLD-glibc build userland of the portable toolchains: the pinned manylinux_2_28 image (AlmaLinux 8.10, glibc 2.28)
#   + gcc-toolset-13 (13.3.1, libstdc++.a for static linking) + gcc-toolset-12 (12.2.1, for the clang-14 nopgo rebuild)
#   + perl-core (OpenSSL's Configure), exported as a plain directory tree so it can be used WITHOUT docker:
#   broot.sh runs commands in it with unprivileged bwrap (for build hosts with bwrap but no docker).
#   Results of the original run: ml228-gt13-v3.tar.zst sha256 1f5e45db1c4656660c7f1fd3afe8e36072b7d5c14d338695d56014a1fa7c8824
#   (v2 = without gcc-toolset-12: 279477354de704b9aee13ed10e6f0323d20d0497a76cceb38935ba6529f533b1; the packages of v2 are a
#   subset of v3 with identical versions); rpm -qa list in the tar at /root/rpm-qa.txt.
#   Also: the link-time-only glibc 2.17 libm (CentOS 7 libm-2.17.so from manylinux2014, sha256 2ff6a53615516bf6c6e9ae1df288221e
#   cb73bbc5a61e4cbb38a777da3afb0b59) -> OUTDIR/glibc217/linkonly/{libm.so.6,libm.so}. NEVER use that directory as a working
#   directory: with an empty LD_LIBRARY_PATH element (= cwd) every dynamically linked program started there loads it.
set -euo pipefail
OUT=$1; mkdir -p "$OUT/glibc217/linkonly"
IMG=quay.io/pypa/manylinux_2_28_x86_64@sha256:55a36963bc0504cdf004011001c1072306402f0b8b83be5a5eba7068f93eec53
OLD=quay.io/pypa/manylinux2014_x86_64@sha256:8a79ff36ce155d8f242dc8013d73c5e8bbe937defb15de7d7afb342c1ab537f4
docker rm -f fv-mkroot >/dev/null 2>&1 || true
docker run --name fv-mkroot "$IMG" bash -c 'dnf install -y -q gcc-toolset-13-gcc-c++ gcc-toolset-13-libstdc++-devel \
  gcc-toolset-13-binutils gcc-toolset-12-gcc-c++ gcc-toolset-12-libstdc++-devel perl-core && rpm -qa | sort > /root/rpm-qa.txt'
docker export fv-mkroot | zstd -q -T8 -o "$OUT/ml228-gt13-v3.tar.zst"; docker rm fv-mkroot >/dev/null
docker run --rm --user "$(id -u):$(id -g)" -v "$OUT/glibc217/linkonly:/out" "$OLD" cp -L /lib64/libm.so.6 /out/libm.so.6
ln -sf libm.so.6 "$OUT/glibc217/linkonly/libm.so"
sha256sum "$OUT/ml228-gt13-v3.tar.zst" "$OUT/glibc217/linkonly/libm.so.6"
echo "extract on the build node: mkdir ml228v3 && zstd -dc ml228-gt13-v3.tar.zst | tar -x -C ml228v3 --exclude='dev/*' --no-same-owner"
