#!/bin/bash
# portable-rust.sh SRCROOT OUTDIR BUNDLE - rebuild gruszka, nl-fast, kcompare (check/checkB/build.sh recipe: pinned commits +
# combined patches, cargo --release --locked --offline, Rust 1.97.1 from the project's offline rustup/cargo copies) INSIDE
# manylinux2014 (glibc 2.17) so the binaries need only GLIBC_2.17 (a build on a glibc 2.35 host needs 2.34). Default x86-64
# target. BUNDLE = directory with the offline rustup/ and cargo/ copies. SRCROOT, OUTDIR and BUNDLE are mounted into the
# container at their own paths (the binaries embed source paths, so keep the same paths to reproduce the same bytes).
set -eu
SRC=${1:?usage: portable-rust.sh SRCROOT OUTDIR BUNDLE}; OUT=${2:?usage: portable-rust.sh SRCROOT OUTDIR BUNDLE}; B=${3:?usage: portable-rust.sh SRCROOT OUTDIR BUNDLE}
mkdir -p "$OUT"; SRC=$(cd "$SRC" && pwd); OUT=$(cd "$OUT" && pwd); B=$(cd "$B" && pwd)
docker run -i --rm --user "$(id -u):$(id -g)" -v "$SRC:$SRC:ro" -v "$OUT:$OUT" -v "$B:$B" -e SRC="$SRC" -e OUT="$OUT" -e B="$B" -e HOME=/tmp/home quay.io/pypa/manylinux2014_x86_64 bash -s <<'IN'
set -eu; mkdir -p /tmp/home
export RUSTUP_HOME=$B/rustup CARGO_HOME=$B/cargo CARGO_NET_OFFLINE=true RUSTUP_TOOLCHAIN=1.97.1 PATH=$B/cargo/bin:/opt/rh/devtoolset-10/root/usr/bin:/usr/bin:/bin
echo "container $(ldd --version | head -1); $(rustc --version); $(cargo --version)"
for c in gruszka nano-lean kcompare; do
  d=$OUT/src-$c; rm -rf $d; cp -a $SRC/$c $d; cd $d
  case $c in gruszka) A="-p gruszka -p susz";; nano-lean) A="--bin nl-fast";; *) A="";; esac
  t0=$(date +%s); CARGO_TARGET_DIR=$d/target cargo build --release --locked --offline $A > $OUT/build-$c.log 2>&1 || { echo "$c: cargo FAILED"; tail -5 $OUT/build-$c.log; continue; }
  echo "$c built in $(( $(date +%s) - t0 )) s"
done
mkdir -p $OUT/bin; cp $OUT/src-gruszka/target/release/gruszka $OUT/src-nano-lean/target/release/nl-fast $OUT/src-kcompare/target/release/kcompare $OUT/bin/ 2>/dev/null || true
cd $OUT/bin; for b in gruszka nl-fast kcompare; do [ -f $b ] || continue; echo "$b: $(sha256sum $b | cut -d' ' -f1) max $(objdump -T $b | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1) needed: $(objdump -p $b | awk '/NEEDED/{printf "%s ", $2}') sse4a: $(objdump -d $b | grep -c -E '\b(insertq|extrq)\b' || true)"; done
IN
