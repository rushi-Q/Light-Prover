#!/bin/bash
# tests/gruszka-nested-indexed/run.sh [WORKDIR] - regression test: nested indexed inductives through a parameter must be accepted (HIGH): gruszka's 055 branch
# scanned the INDEX arguments of a nested occurrence through a parameter (Lean's replace_if_nested does not descend into
# `auxI As is`), and its packed export drops letE.nondep (Lean's == compares it); together the auxiliary count matched the
# record and the positivity check REJECTED valid official Lean 4.36 / 4.37 output. Cases (data/, sha256 in SHA256SUMS):
#   tbug36 / tbug437      TBug (indexed container IdxFam through a type-constructor parameter); official exports; the
#                         official comparator ACCEPTS -> every judge must ACCEPT
#   tchain36-nondep / tchain437-nondep  TChain (+ `let` vs `have` in two nested parameters) exported WITH nondep:true by the
#                         a strict test exporter; the official comparator ACCEPTS -> no judge may REJECT (gruszka
#                         declines: the packed format has no nondep; documented limitation)
#   tchain36-official     the same source through the official leanexport (writes nondep:false): the official comparator
#                         REJECTS (its replay merges the two auxiliary types) -> no judge may ACCEPT
# FV_TEST_OFFICIAL=recorded skips the live official runs (4.36 rows only; tests/lib/official-check.sh). Exit 0 iff all pass.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); D=$H/data
W=${1:-$(mktemp -d /tmp/gruszka-nested-indexed-test.XXXXXX)}; mkdir -p "$W"; P=0; F=0
(cd "$D" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data integrity"; exit 1; }
pin() { awk -v n="$2" '$1=="PIN" && $2==n {print $4}' "$1"; }
GZ=$(pin "$FV/check/sound/pins.env" gruszka); GR7=$(pin "$FV/check/notary/pins.env" gruszka_r7); echo "gruszka $GZ; gruszka-r7 $GR7"
ok() { case " $3 " in *" $2 "*) echo "PASS $1 (rc=$2)"; P=$((P+1));; *) echo "FAIL $1: rc=$2, allowed {$3} ${4:-}"; F=$((F+1));; esac; }
for row in "tbug36|tbug36-solution.export|tbug36-challenge.export|tbug-comparator.json|0|0" \
           "tchain36-nondep|tchain36-nondep-solution.export|tchain36-challenge.export|tchain-comparator.json|0|0 2" \
           "tchain36-official|tchain36-official-solution.export|tchain36-challenge.export|tchain-comparator.json|1|1 2"; do
  IFS='|' read -r n s c g orc allowed <<< "$row"
  if [ "${FV_TEST_OFFICIAL:-live}" != recorded ]; then
    bash "$FV/tests/lib/official-check.sh" "$D/$s" "$D/$c" "$D/$g" > "$W/$n.off" 2>&1; rc=$?; [ $rc = 0 ] || rc=1; ok "$n official-4.36" $rc "$orc"
  fi
  out=$("$GZ" "$D/$s" 4 2>&1); rc=$?; [ "$orc" = 0 ] && ga=$allowed || ga="1 2"; [ "$n" = tbug36 ] && ga=0; ok "$n gruszka" $rc "$ga" "$out"
  out=$("$GR7" "$D/$s" 4 2>&1); rc=$?; ok "$n gruszka-r7" $rc "$ga" "$out"
  "$FV/check/sound/check-sound.sh" "$D/$s" "$D/$c" "$D/$g" --threads 4 --json "$W/$n.cs.json" > /dev/null 2>&1; rc=$?; ok "$n check-sound" $rc "$allowed" "$(cut -c1-250 "$W/$n.cs.json" 2>/dev/null)"
  "$FV/check/notary/check-notary.sh" "$D/$s" "$D/$c" "$D/$g" --threads 4 --json "$W/$n.cn.json" > /dev/null 2>&1; rc=$?; ok "$n check-notary" $rc "$allowed" "$(cut -c1-250 "$W/$n.cn.json" 2>/dev/null)"
  for lj in check-sound-lowmem check-sound-ultralowmem; do
    [ -x "$FV/check/lowmem/$lj.sh" ] || continue
    "$FV/check/lowmem/$lj.sh" "$D/$s" "$D/$c" "$D/$g" --threads 4 --json "$W/$n.$lj.json" > /dev/null 2>&1; rc=$?; ok "$n $lj" $rc "$allowed" "$(cut -c1-250 "$W/$n.$lj.json" 2>/dev/null)"
  done
done
# Lean 4.37.0-rc1 exports through the 4.37 judge (check-sound --pins pins-437.env), when that toolchain is registered
if [ -f "$FV/check/sound/pins-437.env" ]; then
  "$FV/check/sound/check-sound.sh" "$D/tbug437-solution.export" "$D/tbug437-challenge.export" "$D/tbug-comparator.json" --threads 4 --pins "$FV/check/sound/pins-437.env" --json "$W/tbug437.json" > /dev/null 2>&1; rc=$?
  ok "tbug437 check-sound --pins pins-437.env" $rc "0" "$(cut -c1-250 "$W/tbug437.json")"
  "$FV/check/sound/check-sound.sh" "$D/tchain437-nondep-solution.export" "$D/tchain437-challenge.export" "$D/tchain-comparator.json" --threads 4 --pins "$FV/check/sound/pins-437.env" --json "$W/tchain437.json" > /dev/null 2>&1; rc=$?
  ok "tchain437-nondep check-sound --pins pins-437.env" $rc "0 2" "$(cut -c1-250 "$W/tchain437.json")"
fi
echo "gruszka-nested-indexed: $P passed, $F failed"; [ -n "${1:-}" ] || rm -rf "$W"; [ $F = 0 ]
