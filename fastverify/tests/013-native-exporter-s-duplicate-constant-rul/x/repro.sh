#!/bin/bash
# Finding 013: two export roots declaring the same theorem/axiom name with DIFFERENT statements.
# official lean4export: "import B failed, environment already contains 'foo' from A", exit 1; native: exit 0 + an export.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-${TMPDIR:-/tmp}/$(whoami)-f013}; rm -rf "$WORK"; mkdir -p "$WORK/build"
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
cd "$WORK/build"; cp "$HERE"/proj/*.lean .; for m in A B C D; do lean -o $m.olean $m.lean || exit 2; done
for args in "A B -- foo" "C D -- ax"; do
  echo "== lean4export $args   (A: theorem foo : True; B: theorem foo : 1 = 1; C: axiom ax : 1 = 1; D: axiom ax : 2 = 2)"
  $OFFEXP $args > off.out 2> off.err; echo "official lean4export: exit $?  ($(grep -m1 -o 'import.*' off.err)) lines=$(wc -l < off.out)"
  LEAN4EXPORT_VERBOSE=0 $NAT $args > nat.out 2> nat.err; echo "native   lean4export: exit $?  lines=$(wc -l < nat.out); exported: $(tail -1 nat.out | cut -c1-90)"
done
