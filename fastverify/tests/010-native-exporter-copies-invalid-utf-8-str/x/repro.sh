#!/bin/bash
# Finding 010: string literal (or name component) with invalid UTF-8 bytes: official lean4export decodes it char by char
# (Json.renderString -> String.foldl), the native exporter copies the raw bytes. Runs in ~1-2 min.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-${TMPDIR:-/tmp}/$(whoami)-f010}; rm -rf "$WORK"; mkdir -p "$WORK/build"
L=~/.elan/toolchains/leanprover--lean4---v4.33.1; T=~/.elan/toolchains/leanprover--lean4---v4.36.0
OFFEXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
PCHK=/scratch/fastverify/checkers/pchk
TG=$(cat $LIGHT_LEAN/verify/challenge/export-targets.txt)
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
export PATH=$L/bin:$PATH
cp "$HERE"/proj/*.lean "$WORK/build/"; cp "$HERE/comparator.json" "$WORK/"
echo "== 1. ORIGINAL-LEAN BUILD (official 4.33.1, kernel check ON)"
cd "$WORK/build"; lean -o Challenge.olean Challenge.lean >/dev/null 2>&1; echo "Challenge rc=$?"; lean -o Main.olean Main.lean; echo "Main rc=$?"
echo "== 2. EXPORT (same oleans) with the official lean4export v4.33.0 and the native lean4export f581123"
LEAN_PATH=$WORK/build:$L/lib/lean $OFFEXP Challenge -- $TG > ../challenge.export 2>/dev/null
LEAN_PATH=$WORK/build:$L/lib/lean $OFFEXP Main -- $TG > ../sol.official-exporter.export 2>/dev/null; echo "official lean4export rc=$?"
LEAN_PATH=$WORK/build:$L/lib/lean LEAN4EXPORT_VERBOSE=0 $NAT Main -- $TG > ../sol.native-exporter.export 2>/dev/null; echo "native lean4export rc=$?"
cd "$WORK"
if cmp -s sol.official-exporter.export sol.native-exporter.export; then echo "exports IDENTICAL"; else echo "exports DIFFER (cat -v):"; diff sol.official-exporter.export sol.native-exporter.export | cat -v; fi
echo "== 3. CHECK"
LC=$PCHK/.lake/build/bin/pleanchecker-k
if objdump -T "$LC" | grep -q GLIBC_2.38 && ! ldd --version | head -1 | grep -qE "2\.(3[89]|[4-9][0-9])"; then
  LC=${PLEANCHECKER_K:-$PCHK/.lake/build/bin/pleanchecker}; echo "(pleanchecker-k needs glibc 2.38 here; Lean-kernel replay = $LC)"; fi
for s in official-exporter native-exporter; do
  PATH=$T/bin:$PATH lake comparator --config comparator.json --challenge-from-export challenge.export --solution-from-export sol.$s.export > cmp.$s.log 2>&1
  echo "OFFICIAL lake comparator (Lean 4.36) on sol.$s.export: exit $?  ($(tail -1 cmp.$s.log))"
  CCMP_LEANCHECKER=$LC sh $PCHK/run.sh $PCHK $WORK/sol.$s.export 8 $WORK/challenge.export > pchk.$s.log 2>&1
  echo "FAST pchk run.sh on sol.$s.export: exit $?  ($(grep -m1 -E 'not contain valid UTF-8|okay' pchk.$s.log))"
done
echo "== 5. DEPLOYED BINARY (/scratch/fastverify/exporter/lean4export, needs glibc 2.38 + libuv>=1.45: ubuntu:24.04 container, no network)"
if docker image inspect ubuntu:24.04 >/dev/null 2>&1; then
  bash "$HERE/deployed-export.sh" "$WORK/build" "$WORK/sol.deployed-native.export" Main -- $TG
  if cmp -s "$WORK/sol.deployed-native.export" "$WORK/sol.native-exporter.export"; then echo "deployed native export == native export above (byte-identical)"; else echo "deployed native export DIFFERS from the local build:"; diff "$WORK/sol.deployed-native.export" "$WORK/sol.native-exporter.export" | head -5; fi
  cmp -s "$WORK/sol.deployed-native.export" "$WORK/sol.official-exporter.export" && echo "deployed == official" || echo "deployed native export != official exporter export"
else echo "(no ubuntu:24.04 docker image on this node: step skipped)"; fi
