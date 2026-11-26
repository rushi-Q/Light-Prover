#!/bin/bash
# tests/toolchain/run.sh [--quick] -- regression test for the TOOLCHAIN findings 004 014 020 031 037 040 046 048 050 052 061
# (the deployed PGO/patched toolchain d5e35ef223 gave different exports/verdicts than Lean 4.33.1).
# Fix: the package builds/exports/checks ONLY with the unmodified official release named by the project's
# lean-toolchain, verified against the manifest pinned in fastverify/toolchains/ (lib/toolchain.py); anything else -> DECLINE.
# Part 1 (unit, ~30 s): lib/toolchain.py accepts the official install and refuses everything else (exit 2).
# Part 2 (~6 min, skipped with --quick): the original toolchain regression (package-local copy
#   tests/toolchain/regress_toolchain.sh, inputs from tests/NNN-*/x; 22 cases for
#   004/014/020/031/037/040/050/061/052) with candidate = the toolchain the package resolves for a v4.33.1 project.
#   Deployed/patched toolchain: 22/22 DIFFERENT (see t1.sh); official (the package's T0): every line must read SAME.
# 046 (heartbeats) and 048 (address space) compare the candidate binary with the official one: with the package's
# toolchain the binary IS the official one (verified byte for byte), so they hold by construction (checked in T1: same tree).
# Part 3 (skipped with --quick, or when 4.36.0 is not enabled): tests/toolchain/v436.sh (toy 4.36.0 projects vs the
#   official 4.36 flow; the fast build must decline, verdicts and exports must equal the official ones).
# Output: one 'PASS|FAIL <case>' line per check, final 'RESULT: PASS|FAIL'. Exit 0 iff all pass. Run on any host.
main() {
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); TC="python3 -I $FV/lib/toolchain.py"
# the official 4.33.1 install as configured for this machine (config/components.json, written by tools/configure.py)
OFF=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
[ -n "$OFF" ] || OFF=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
REGRESS=$H/regress_toolchain.sh   # package-local copy of the toolchain regression (inputs from tests/NNN-*/x)
TMPB=/scratch; [ -w /scratch ] || TMPB=/tmp
W=$(mktemp -d $TMPB/fv-tctest.XXXXXX); trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
fails=0
ok()  { echo "PASS $*"; }
bad() { echo "FAIL $*"; fails=$((fails+1)); }
expect() { # expect RC "name" cmd...
  local want=$1 name=$2; shift 2; "$@" > "$W/out" 2> "$W/err"; local rc=$?
  if [ $rc = "$want" ]; then ok "$name (rc $rc) $(head -c 160 "$W/err" | tr '\n' ' ')"; else bad "$name: rc $rc, expected $want; $(head -c 300 "$W/err" | tr '\n' ' ')"; fi; }
mkproj() { mkdir -p "$W/$1"; printf '%s' "$2" > "$W/$1/lean-toolchain"; }

# ---- part 1: verifier
mkproj p-ok 'leanprover/lean4:v4.33.1
'
expect 0 "T1 resolve: project pinning leanprover/lean4:v4.33.1 -> the official install verifies" $TC resolve "$W/p-ok" --json "$W/t1.json"
[ "$(cat "$W/out")" = "$(readlink -f "$OFF")" ] && ok "T1b resolved root = official elan install" || bad "T1b resolved root $(cat "$W/out")"
mkproj p-c36 'leanprover/lean4:v4.36.0'
expect 0 "T1c resolve: v4.36.0 (comparator toolchain) verifies" $TC resolve "$W/p-c36"
FAST=; for c in /scratch/fastverify-next/tc/lean4-7586a50cec-nopgo /scratch/fastverify/tc/stage1; do [ -d "$c" ] && { FAST=$c; break; }; done
if [ -n "$FAST" ]; then
  expect 2 "T2 patched fast toolchain $FAST presented as the official v4.33.1 -> refused" $TC verify "$FAST" leanprover/lean4:v4.33.1
  mkdir -p "$W/fake-elan"; ln -s "$FAST" "$W/fake-elan/leanprover--lean4---v4.33.1"
  expect 0 "T2b resolve with a search dir holding the fast toolchain -> skipped, falls through to the official install" $TC resolve "$W/p-ok" --search "$W/fake-elan"
  [ "$(cat "$W/out")" = "$(readlink -f "$OFF")" ] && ok "T2c resolved root is the official install, not the fast toolchain" || bad "T2c resolved $(cat "$W/out")"
else echo "INFO T2 skipped: no patched toolchain tree present on $(hostname)"; fi
# a real copy of the official tree (node-local), then single modifications
cp -a "$OFF" "$W/copy"
expect 0 "T3 exact copy of the official tree verifies" $TC verify "$W/copy" leanprover/lean4:v4.33.1
chmod u+w "$W/copy/bin" "$W/copy/bin/lean"
cp "$W/copy/bin/lean" "$W/lean.orig"; python3 -I -c "import sys; f=open(sys.argv[1],\"r+b\"); f.seek(4096); b=f.read(1); f.seek(4096); f.write(bytes([b[0]^1]))" "$W/copy/bin/lean"
expect 2 "T3a one byte changed in bin/lean -> refused" $TC verify "$W/copy" leanprover/lean4:v4.33.1
cp "$W/lean.orig" "$W/copy/bin/lean"
o=$(find "$W/copy/lib/lean/Init" -name 'Prelude.olean' | head -1); chmod u+w "$o" "$(dirname "$o")"
cp "$o" "$W/olean.orig"; printf 'X' >> "$o"
expect 2 "T3b core library olean modified (020/052 class) -> refused" $TC verify "$W/copy" leanprover/lean4:v4.33.1
cp "$W/olean.orig" "$o"
touch "$W/copy/bin/extra-tool"
expect 2 "T3c extra file in the tree -> refused" $TC verify "$W/copy" leanprover/lean4:v4.33.1
rm "$W/copy/bin/extra-tool"
mv "$W/copy/bin/lake" "$W/lake.orig"
expect 2 "T3d missing file -> refused" $TC verify "$W/copy" leanprover/lean4:v4.33.1
mv "$W/lake.orig" "$W/copy/bin/lake"
chmod a-x "$W/copy/bin/lean"
expect 2 "T3e bin/lean not executable (cannot start) -> refused" $TC verify "$W/copy" leanprover/lean4:v4.33.1
chmod u+x,go+x "$W/copy/bin/lean"
expect 0 "T3f restored copy verifies again" $TC verify "$W/copy" leanprover/lean4:v4.33.1
ln -s "$OFF" "$W/link"
expect 2 "T4 symlinked toolchain directory (elan toolchain link) -> refused" $TC verify "$W/link" leanprover/lean4:v4.33.1
mkdir -p "$W/p-none"
expect 2 "T5a project without lean-toolchain -> refused" $TC resolve "$W/p-none"
mkproj p-two 'leanprover/lean4:v4.33.1
leanprover/lean4:v4.36.0'
expect 2 "T5b lean-toolchain with two lines -> refused" $TC resolve "$W/p-two"
mkproj p-stable 'stable'
expect 2 "T5c channel 'stable' -> refused" $TC resolve "$W/p-stable"
mkproj p-unpinned 'leanprover/lean4:v4.20.0'
expect 2 "T5d release without a pinned manifest -> refused" $TC resolve "$W/p-unpinned"
mkproj p-nightly 'leanprover/lean4-nightly:nightly-2025-06-01'
expect 2 "T5e nightly toolchain -> refused" $TC resolve "$W/p-nightly"
mkproj p-local '/scratch/fastverify/tc/stage1'
expect 2 "T5f lean-toolchain naming a local path -> refused" $TC resolve "$W/p-local"
python3 -I - "$W/t1.json" <<'EOF' && ok "T6 result JSON records id, root, tree digest, lean/lake version lines" || bad "T6 result JSON incomplete"
import json, sys
r = json.load(open(sys.argv[1]))
assert r["verified"] and r["id"] == "leanprover/lean4:v4.33.1" and r["tree_sha256"] == r["pinned_tree_sha256"]
assert "4.33.1" in r["lean_version"] and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in r["lean_version"], r["lean_version"]
EOF

# ---- part 2: the toolchain regression with the toolchain the package resolves
if [ "${1:-}" != --quick ]; then
  ROOT=$($TC resolve "$W/p-ok" 2>/dev/null)
  if [ -z "$ROOT" ] || [ ! -f "$REGRESS" ]; then bad "P2 cannot run (root '$ROOT', $REGRESS)"; else
    bash "$REGRESS" "$ROOT" > "$W/regress.log" 2>&1
    n_same=$(grep -c '^SAME' "$W/regress.log"); n_diff=$(grep -c '^DIFFERENT' "$W/regress.log")
    sed 's/^/  regress: /' "$W/regress.log"
    if [ "$n_diff" = 0 ] && [ "$n_same" -ge 22 ]; then ok "P2 regress_toolchain.sh with the package toolchain: $n_same SAME, 0 DIFFERENT"
    else bad "P2 regress_toolchain.sh: $n_same SAME, $n_diff DIFFERENT"; fi
  fi
fi
# ---- part 3: a second official release (generality), only if the package lists leanprover/lean4:v4.36.0
if [ "${1:-}" != --quick ]; then
  bash "$H/v436.sh" "$W/v436" > "$W/v436.log" 2>&1; v=$?
  sed 's/^/  v436: /' "$W/v436.log"
  case $v in 0) ok "P3 4.36.0 toy projects through the package = official 4.36 flow (tests/toolchain/v436.sh)";;
             3) echo "INFO P3 skipped: 4.36.0 not enabled in config/components.json";;
             *) bad "P3 tests/toolchain/v436.sh failed (exit $v)";; esac
fi
[ $fails = 0 ] && { echo "RESULT: PASS"; return 0; } || { echo "RESULT: FAIL ($fails)"; return 1; }
}
main "$@"; exit $?
