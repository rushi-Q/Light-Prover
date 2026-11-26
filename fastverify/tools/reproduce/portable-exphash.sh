#!/bin/bash
# portable-exphash.sh OUT BUNDLE - build exphash (tools/compress/exphash, untrusted analysis tool used by tools/dupfind)
# inside manylinux2014 with the project's offline Rust 1.97.1 -> runs on any glibc >= 2.17 host (a build on a glibc 2.35 host
# needs 2.34). BUNDLE = directory with the offline rustup/ and cargo/ copies (mounted into the container at its own path).
set -eu; OUT=${1:?usage: portable-exphash.sh OUT BUNDLE}; B=${2:?usage: portable-exphash.sh OUT BUNDLE}
FV=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd); mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd); B=$(cd "$B" && pwd)
rm -rf "$OUT/src"; mkdir -p "$OUT/src"; ( cd "$FV/tools/compress/exphash" && tar --exclude=target --exclude=test -cf - . ) | tar -xf - -C "$OUT/src"
docker run -i --rm --user "$(id -u):$(id -g)" -v "$B:$B" -v "$OUT:$OUT" -e OUT="$OUT" -e B="$B" -e CARGO_HOME_OVERRIDE="${CARGO_HOME_OVERRIDE:-}" -e HOME=/tmp/home quay.io/pypa/manylinux2014_x86_64 bash -s <<'IN'
set -eu; mkdir -p /tmp/home
export RUSTUP_HOME=$B/rustup CARGO_HOME=${CARGO_HOME_OVERRIDE:-$B/cargo} CARGO_NET_OFFLINE=true RUSTUP_TOOLCHAIN=1.97.1 PATH=$B/cargo/bin:/opt/rh/devtoolset-10/root/usr/bin:/usr/bin:/bin
cd $OUT/src && CARGO_TARGET_DIR=$OUT/target cargo build --release --locked --offline 2>&1 | tail -3
mkdir -p $OUT/bin; cp $OUT/target/release/exphash $OUT/target/release/expcompress $OUT/bin/ 2>/dev/null || cp $OUT/target/release/exphash $OUT/bin/
for b in $OUT/bin/*; do echo "$(basename $b): $(sha256sum $b | cut -d' ' -f1) max $(objdump -T $b | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1) size $(stat -c %s $b)"; done
IN
