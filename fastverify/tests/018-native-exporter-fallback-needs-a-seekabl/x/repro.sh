#!/bin/bash
# Finding: the native core cannot represent numeric name components >= 2^63 (nat_small dies), so it fails and relies on the
# "rewind stdout + reference implementation" fallback. That fallback needs a regular-file stdout.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-${TMPDIR:-/tmp}/$(whoami)-fpipe}; rm -rf "$WORK"; mkdir -p "$WORK/build"
L=~/.elan/toolchains/leanprover--lean4---v4.33.1
OFFEXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
NAT=${NAT_CANDIDATE:-/scratch/fastverify/exporter/lean4export}   # NAT_CANDIDATE=<exporter binary>: test a fixed build instead
if [ -z "${NAT_CANDIDATE:-}" ] && objdump -T "$NAT" 2>/dev/null | grep -q GLIBC_2.38 && ! ldd --version | head -1 | grep -qE "2\.(3[89]|[4-9][0-9])"; then
  echo "[setup] deployed native exporter needs glibc 2.38; building lean4export f581123 with official v4.33.1"
  PRE=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/lean4export-f581123  # = this build, built once on a host with a C++ compiler
  if [ -x "$PRE" ] && ! ldd "$PRE" 2>&1 | grep -q "not found"; then mkdir -p "$WORK/le/.lake/build/bin" && cp "$PRE" "$WORK/le/.lake/build/bin/lean4export" && echo "[setup] using prebuilt f581123 exporter $PRE"; else
  git -c advice.detachedHead=false clone -q $LIGHT_LEAN/lineB/lean4export "$WORK/le" && (cd "$WORK/le" &&
    git checkout -q f581123 && PATH=$L/bin:$PATH lake build >/dev/null 2>&1) || { echo "native exporter build failed"; exit 2; }
  fi
  NAT=$WORK/le/.lake/build/bin/lean4export
fi
export PATH=$L/bin:$PATH LEAN_PATH=$WORK/build:$L/lib/lean
cd "$WORK/build"; cp "$HERE"/proj/N.lean .; lean -o N.olean N.lean || exit 2
echo "== N.lean: a definition named bigNum.18446744073709551616 (Name.num component 2^64) + theorem main_thm : True"
$OFFEXP N -- main_thm 2>/dev/null | cat > off.pipe; echo "official lean4export, stdout = pipe: exit ${PIPESTATUS[0]}, $(wc -l < off.pipe) lines"
$NAT N -- main_thm 2>nat.err | cat > nat.pipe; echo "native   lean4export, stdout = pipe: exit ${PIPESTATUS[0]}, $(wc -l < nat.pipe) lines"
grep -v "^lean4export (native) \[" nat.err | sed 's/^/    stderr: /'
$NAT N -- main_thm > nat.file 2>nat2.err; echo "native   lean4export, stdout = file: exit $?, $(wc -l < nat.file) lines ($(grep -c 'falling back' nat2.err) fallback to the reference implementation)"
cmp -s off.pipe nat.file && echo "    (file output identical to the official export)"
