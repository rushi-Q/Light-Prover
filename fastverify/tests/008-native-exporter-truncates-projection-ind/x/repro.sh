#!/bin/bash
# Finding 008: the native lean4export (f581123, native/fast_export.cpp) writes projection indices modulo 2^32.
# Runs in ~1-2 min. Work dir: /scratch/$USER-f008 (override with WORK=...).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-${TMPDIR:-/tmp}/$(whoami)-f008}; rm -rf "$WORK"; mkdir -p "$WORK"/{official-build,fast-build}
L=~/.elan/toolchains/leanprover--lean4---v4.33.1; T=~/.elan/toolchains/leanprover--lean4---v4.36.0
OFFEXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export   # official v4.33.0
PCHK=/scratch/fastverify/checkers/pchk
TG=$(cat $LIGHT_LEAN/verify/challenge/export-targets.txt)
# native exporter: the deployed binary if it runs here (needs glibc >= 2.38, i.e. the AMD production host), else the same commit f581123
# built with the official v4.33.1 toolchain (the C++ core native/fast_export.cpp is byte-identical source)
NAT=${NAT_CANDIDATE:-/scratch/fastverify/exporter/lean4export}   # NAT_CANDIDATE=<exporter binary>: test a fixed build instead
if [ -z "${NAT_CANDIDATE:-}" ] && objdump -T "$NAT" 2>/dev/null | grep -q GLIBC_2.38 && ! ldd --version | head -1 | grep -qE "2\.(3[89]|[4-9][0-9])"; then
  echo "[setup] deployed native exporter needs glibc 2.38; building lean4export f581123 with official v4.33.1"
  PRE=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/lean4export-f581123  # = this build, built once on a host with a C++ compiler
  if [ -x "$PRE" ] && ! ldd "$PRE" 2>&1 | grep -q "not found"; then mkdir -p "$WORK/le/.lake/build/bin" && cp "$PRE" "$WORK/le/.lake/build/bin/lean4export" && echo "[setup] using prebuilt f581123 exporter $PRE"; else
  git -c advice.detachedHead=false clone -q $LIGHT_LEAN/lineB/lean4export "$WORK/le" && (cd "$WORK/le" && git checkout -q f581123 &&
    PATH=$L/bin:$PATH lake build >/dev/null 2>&1) || { echo "native exporter build failed"; exit 2; }
  fi
  NAT=$WORK/le/.lake/build/bin/lean4export
fi
export PATH=$L/bin:$PATH
PROJ=${PROJ:-proj}
cp "$HERE"/$PROJ/*.lean "$WORK/official-build/"; cp "$HERE"/$PROJ/*.lean "$WORK/fast-build/"
echo "== 1. ORIGINAL-LEAN BUILD (official 4.33.1, kernel check on)"
cd "$WORK/official-build"; lean -o Challenge.olean Challenge.lean >/dev/null 2>&1; echo "Challenge rc=$?"
lean -o Main.olean Main.lean > main.log 2>&1; echo "Main rc=$?  ($(grep -m1 -o 'error: .*' main.log))"
echo "== 2. FAST BUILD (same, with the pipeline's -Ddebug.skipKernelTC=true)"
cd "$WORK/fast-build"; lean -Ddebug.skipKernelTC=true -o Challenge.olean Challenge.lean >/dev/null 2>&1; echo "Challenge rc=$?"
lean -Ddebug.skipKernelTC=true -o Main.olean Main.lean >/dev/null 2>&1; echo "Main rc=$?"
echo "== 3. EXPORT the fast-build oleans with the official exporter and with the native exporter (same targets as export.sh)"
cd "$WORK"
LEAN_PATH=$WORK/official-build:$L/lib/lean $OFFEXP Challenge -- $TG > challenge.export 2>/dev/null
(cd fast-build && LEAN_PATH=$WORK/fast-build:$L/lib/lean $OFFEXP Main -- $TG > ../sol.official-exporter.export 2>/dev/null); echo "official lean4export rc=$?"
(cd fast-build && LEAN_PATH=$WORK/fast-build:$L/lib/lean LEAN4EXPORT_VERBOSE=0 $NAT Main -- $TG > ../sol.native-exporter.export 2>/dev/null); echo "native lean4export rc=$?"
if cmp -s sol.official-exporter.export sol.native-exporter.export; then echo "exports IDENTICAL"; else echo "exports DIFFER:"; diff sol.official-exporter.export sol.native-exporter.export; fi
echo "== 4. CHECK"
cat > comparator.json <<'J'
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "external_kernels": {"nanoda": ["nanoda_bin"]}}
J
for s in official-exporter native-exporter; do
  PATH=$T/bin:$PATH lake comparator --config comparator.json --challenge-from-export challenge.export --solution-from-export sol.$s.export > cmp.$s.log 2>&1
  echo "OFFICIAL lake comparator (Lean 4.36) on sol.$s.export: exit $?  ($(tail -1 cmp.$s.log))"
done
LC=$PCHK/.lake/build/bin/pleanchecker-k
if ! "$LC" --help >/dev/null 2>&1 && objdump -T "$LC" | grep -q GLIBC_2.38 && ! ldd --version | head -1 | grep -qE "2\.(3[89]|[4-9][0-9])"; then
  LC=${PLEANCHECKER_K:-$PCHK/.lake/build/bin/pleanchecker}; echo "(pleanchecker-k needs glibc 2.38 here; Lean-kernel replay = $LC)"; fi
for s in official-exporter native-exporter; do
  CCMP_LEANCHECKER=$LC sh $PCHK/run.sh $PCHK $WORK/sol.$s.export 8 $WORK/challenge.export > pchk.$s.log 2>&1
  echo "FAST pchk run.sh on sol.$s.export: exit $?  ($(tail -2 pchk.$s.log | head -1))"
done
echo "== 5. DEPLOYED BINARY (/scratch/fastverify/exporter/lean4export, needs glibc 2.38 + libuv>=1.45: ubuntu:24.04 container, no network)"
if docker image inspect ubuntu:24.04 >/dev/null 2>&1; then
  bash "$HERE/deployed-export.sh" "$WORK/fast-build" "$WORK/sol.deployed-native.export" Main -- $TG
  if cmp -s "$WORK/sol.deployed-native.export" "$WORK/sol.native-exporter.export"; then echo "deployed native export == native export above (byte-identical)"; else echo "deployed native export DIFFERS from the local build:"; diff "$WORK/sol.deployed-native.export" "$WORK/sol.native-exporter.export" | head -5; fi
  cmp -s "$WORK/sol.deployed-native.export" "$WORK/sol.official-exporter.export" && echo "deployed == official" || echo "deployed native export != official exporter export"
else echo "(no ubuntu:24.04 docker image on this node: step skipped)"; fi
