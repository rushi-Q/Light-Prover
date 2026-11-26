#!/bin/bash
# tests/gruszka-bfs/run.sh [WORKDIR] - regression test: nested occurrences found later in BFS order must be accepted (an earlier gruszka fix for 055 missed a nested
# occurrence `g α` whose parameter g is itself a parameter application `f β` (f := Box2); the same auxiliary type was then
# found later in BFS order, numNested still matched (the decline guard of the 068 fix bypassed) and the recursor check REJECTED
# valid official Lean 4.36 output). Cases (data/*.lean = the sources; exports made with the official Lean 4.36.0 lean +
# leanexport in bwrap without network): NestedBfsReject (the 22-line reproduction), OuterOnly (without the second
# constructor: the old binary declined), DeepChain (three parameter levels, Box3 γ β α), UnivPoly (universe-polymorphic
# containers), IndexedHead (indexed container head; a control the old binary already accepted).
# Rows per case: the official 4.36 lake comparator (tests/lib/official-check.sh; FV_TEST_OFFICIAL=recorded skips it) and
# the package's pinned gruszka (check/sound/pins.env), gruszka-r7 (check/notary/pins.env), check-sound.sh and
# check-notary.sh: all must ACCEPT. Exit 0 iff every row passes.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); D=$H/data
W=${1:-$(mktemp -d /tmp/gruszka-bfs-test.XXXXXX)}; mkdir -p "$W"
(cd "$D" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data integrity"; exit 1; }
pin() { awk -v n="$2" '$1=="PIN" && $2==n {print $4}' "$1"; }
GZ=$(pin "$FV/check/sound/pins.env" gruszka); GR7=$(pin "$FV/check/notary/pins.env" gruszka_r7)
echo "gruszka: $GZ; gruszka-r7: $GR7"
P=0; F=0
ok() { if [ "$2" = "$3" ]; then echo "PASS $1 (rc=$2)"; P=$((P+1)); else echo "FAIL $1: want rc=$3, got rc=$2 ${4:-}"; F=$((F+1)); fi; }
for c in NestedBfsReject OuterOnly DeepChain UnivPoly IndexedHead; do
  S=$D/$c.export
  if [ "${FV_TEST_OFFICIAL:-live}" != recorded ]; then
    bash "$FV/tests/lib/official-check.sh" "$S" "$D/Chal.export" "$D/cfg_bfs.json" > "$W/$c.off" 2>&1; rc=$?; ok "$c official-4.36" $rc 0 "$(tail -1 "$W/$c.off")"
  fi
  out=$("$GZ" "$S" 4 2>&1); rc=$?; ok "$c gruszka" $rc 0 "$out"
  out=$("$GR7" "$S" 4 2>&1); rc=$?; ok "$c gruszka-r7" $rc 0 "$out"
  "$FV/check/sound/check-sound.sh" "$S" "$D/Chal.export" "$D/cfg_bfs.json" --threads 4 --json "$W/$c.cs.json" > /dev/null 2>&1; rc=$?
  ok "$c check-sound" $rc 0 "$(cut -c1-300 "$W/$c.cs.json" 2>/dev/null)"
  "$FV/check/notary/check-notary.sh" "$S" "$D/Chal.export" "$D/cfg_bfs.json" --threads 4 --json "$W/$c.cn.json" > /dev/null 2>&1; rc=$?
  ok "$c check-notary" $rc 0 "$(cut -c1-300 "$W/$c.cn.json" 2>/dev/null)"
done
echo "gruszka-bfs: $P passed, $F failed"; [ -n "${1:-}" ] || rm -rf "$W"; [ $F = 0 ]
