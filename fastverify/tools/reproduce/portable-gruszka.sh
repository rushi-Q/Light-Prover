#!/bin/bash
# portable-gruszka.sh VARIANT GRUSZKA_SRC OUTDIR BUNDLE  - reproducible, portable build of the pinned gruszka binaries
#   VARIANT     default (check/sound pins: gruszka, `checkB/portable-v2`) | notary (check/notary pins: gruszka-r7 v2) |
#               lowmem (check/lowmem/pins-ultralowmem.env: gruszka_lowmem = + check/lowmem/src-ultralowmem/patches/gruszka-lowmem.patch)
#   GRUSZKA_SRC the gruszka 0.1.1 sources at commit 4ad120b (sources/gruszka of this repository, or
#               `git -C <gruszka repository> archive 4ad120b`); only Cargo.toml, Cargo.lock, src/ and vendor/ are used
#   OUTDIR      fresh output directory (in/ = the patched tree, w/ = the build, bin/ = the binary + SHA256SUMS)
#   BUNDLE      offline Rust 1.97.1: BUNDLE/rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu and BUNDLE/cargo/registry/
#               {index,cache} holding the crates of gruszka's Cargo.lock (no network is used or available)
# Patches (this package): check/checkB/patches/gruszka-combined-v6.diff (= gruszka-combined.diff: fixes 055/058, 053,
# 068, 039 + gruszka-05-fix-z04-9.diff + gruszka-06-fix-y3-1.diff; COMBINED=v5 rebuilds the superseded binaries 8a102d1f /
# ede8e3b9 / 7c1c7075 from gruszka-combined-v5.diff), and for VARIANT=notary also check/notary/gruszka-r7-digest.diff (cross-leg digest),
# for VARIANT=lowmem check/lowmem/src-ultralowmem/patches/gruszka-lowmem.patch (disk-backed packing, worker caps).
# Build: docker image quay.io/pypa/manylinux2014_x86_64 pinned by digest (glibc 2.17, devtoolset-10 gcc as linker / C
# compiler of libmimalloc-sys), --network none, `cargo build --release --locked --offline -p gruszka -p susz`, default
# x86-64 target, SOURCE_DATE_EPOCH fixed (mimalloc embeds __DATE__/__TIME__). Every path the binary embeds (debug info, panic locations, the C sources of mimalloc) is CANONICAL inside
# the container (/build/w/gruszka, /build/w/cargo, /opt/rust/rustup), so the result is byte-identical on any host with the
# same image, toolchain and sources (verified on two hosts: check/sound/README.md).
set -euo pipefail
V=$1; GS=$(realpath "$2"); OUT=$(mkdir -p "$3" && realpath "$3"); B=$(realpath "$4")
H=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)   # the package root
IMG=quay.io/pypa/manylinux2014_x86_64@sha256:8a79ff36ce155d8f242dc8013d73c5e8bbe937defb15de7d7afb342c1ab537f4
case $V in default|notary|lowmem) ;; *) echo "VARIANT must be default, notary or lowmem" >&2; exit 2;; esac
[ -d "$B/rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu" ] && [ -d "$B/cargo/registry/cache" ] || { echo "bad BUNDLE $B" >&2; exit 2; }
rm -rf "$OUT/in" "$OUT/w" "$OUT/bin"; mkdir -p "$OUT/in" "$OUT/w" "$OUT/bin"
cp -a "$GS/Cargo.toml" "$GS/Cargo.lock" "$GS/src" "$GS/vendor" "$OUT/in/"
rm -rf "$OUT/in/vendor/susz/tests" "$OUT/in/vendor/susz/target"
CB=${COMBINED:-v6}; case $CB in v5|v6) ;; *) echo "COMBINED must be v5 or v6" >&2; exit 2;; esac
( cd "$OUT/in" && patch -p1 --quiet --no-backup-if-mismatch < "$H/check/checkB/patches/gruszka-combined-$CB.diff" )
[ "$V" != notary ] || ( cd "$OUT/in" && patch -p1 --quiet --no-backup-if-mismatch < "$H/check/notary/gruszka-r7-digest.diff" )
[ "$V" != lowmem ] || ( cd "$OUT/in" && patch -p1 --quiet --no-backup-if-mismatch < "$H/check/lowmem/src-ultralowmem/patches/gruszka-lowmem.patch" )
find "$OUT/in" -name '*.orig' -o -name '*.rej' | grep -q . && { echo "patch left .orig/.rej files" >&2; exit 2; }
( cd "$OUT/in" && find . -type f | LC_ALL=C sort | xargs sha256sum ) > "$OUT/in.sha256"
echo "source tree ($V, combined-$CB): $(sha256sum < "$OUT/in.sha256" | cut -c1-64) ($(wc -l < "$OUT/in.sha256") files)"
docker run -i --rm --network none --user "$(id -u):$(id -g)" \
  -v "$OUT/in:/build/in:ro" -v "$OUT/w:/build/w" -v "$B/rustup:/opt/rust/rustup:ro" -v "$B/cargo/registry:/opt/rust/registry:ro" \
  -e HOME=/build/w/home "$IMG" bash -s <<'IN'
set -eu
mkdir -p /build/w/home /build/w/cargo/registry
cp -a /opt/rust/registry/index /opt/rust/registry/cache /build/w/cargo/registry/
cp -a /build/in /build/w/gruszka
TCB=/opt/rust/rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin
export RUSTUP_HOME=/opt/rust/rustup CARGO_HOME=/build/w/cargo CARGO_NET_OFFLINE=true PATH=$TCB:/opt/rh/devtoolset-10/root/usr/bin:/usr/bin:/bin
unset RUSTFLAGS CARGO_BUILD_RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
# libmimalloc-sys's options.c prints __DATE__ __TIME__: GCC takes them from SOURCE_DATE_EPOCH (= the commit time of
# gruszka 4ad120b), so the C part does not depend on the build time
export SOURCE_DATE_EPOCH=1795242059
echo "container $(ldd --version | head -1); $(rustc --version); $(cargo --version); $(cc --version | head -1)"
cd /build/w/gruszka
CARGO_TARGET_DIR=/build/w/gruszka/target cargo build --release --locked --offline -p gruszka -p susz > /build/w/build.log 2>&1 \
  || { tail -20 /build/w/build.log; exit 1; }
IN
install -m 555 "$OUT/w/gruszka/target/release/gruszka" "$OUT/bin/gruszka"
cd "$OUT/bin"; sha256sum gruszka > SHA256SUMS
n=$(objdump -d gruszka | grep -c -E '\b(insertq|extrq)\b' || true); g=$(objdump -T gruszka | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1)
echo "gruszka ($V): $(cut -c1-64 SHA256SUMS) max $g needed: $(objdump -p gruszka | awk '/NEEDED/{printf "%s ", $2}') sse4a: $n"
[ "$n" = 0 ] || { echo "non-portable instructions (SSE4a)" >&2; exit 1; }
