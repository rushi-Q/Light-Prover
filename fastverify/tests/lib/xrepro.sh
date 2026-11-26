#!/bin/bash
# xrepro.sh TESTDIR WORK [SCRIPT]
# Runs the original repro script of a finding (snapshot in TESTDIR/x/, default script x/repro.sh, or the one named in the
# lines of TESTDIR/REPRO) with the package as the FAST flow (x/**/fastflow.sh is a symlink to tests/lib/fastflow.sh),
# and the unmodified OFFICIAL flow (x/officialflow.sh: lake build 4.33.1 + official lean4export + lake comparator 4.36).
# Prints the full log to WORK.log and one TSV row per case (lib/parse.py) on stdout. Exit 0 iff every row is PASS*.
{ # whole script parsed before it runs (safe against edits while running)
set -u
H=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)
TD=$(cd "$1" && pwd); W=$2; id=$(basename "$TD"); case $id in [0-9][0-9][0-9]-*) id=${id:0:3};; esac
SL=${3:-$( [ -s "$TD/REPRO" ] && grep -v '^#' "$TD/REPRO" || echo repro.sh )}
mkdir -p "$(dirname "$W")"; W=$(readlink -f "$(dirname "$W")")/$(basename "$W"); L=$W.log
: > "$L"; i=0
for S in $SL; do   # every script listed in REPRO (one per line), each with its own work dir
  i=$((i+1)); WS=$W; [ $i -gt 1 ] && WS=$W.$i
  echo "@@ test $id: $TD/x/$S $WS (FV_BIN=${FV_BIN:-<package>/bin/fastverify} FV_FAST=${FV_FAST:-package})" >> "$L"
  ( cd "$TD/x" && bash "$TD/x/$S" "$WS" ) >> "$L" 2>&1
  echo "@@ repro $S exit $?" >> "$L"
  [ -n "${KEEP_WORK:-}" ] || rm -rf "$WS"
done
python3 -I "$H/parse.py" "$id" "$L" "$TD/EXPECT" | tee "$W.tsv"
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}
