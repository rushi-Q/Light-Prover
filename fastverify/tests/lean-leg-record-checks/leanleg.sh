#!/bin/bash
# tests/lean-leg-record-checks/leanleg.sh PLEANCHECKER [KERNEL_ISSUES_DIR] [DIR...]
# record check "crafted corpora ALL REJECTED by the Lean leg ALONE, controls ACCEPTED": runs the given 4.36-walk
# pleanchecker binary (exactly the trusted wrapper's way: -jT -v, LEAN_STACK_SIZE_KB=917376) in the parallel mode AND in --seq
# on (a) tests/kernel-cves/craft_cves.py (crafted here from the self-test exports), (b) the crafted dir of
# tests/kernel-issues (optional; made by its test.py with the official 4.33.1 Lean in bwrap) + its base export, (c) any
# *.export in each further DIR (optional, e.g. the analogues of mk_kernel_issue_exports.py, mk_c2_stream.py, mk_implicit_closure.py's leanleg/;
# names containing 'control' or 'honest' are controls). Attack = rc != 0, control = rc 0. A given directory without exports = FAIL.
# Prints one TSV row per (case, mode) and 'RESULT PASS n' / 'RESULT FAIL n'.
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
P=$1; KIDIR=${2:-}; shift; [ $# -gt 0 ] && shift; EXTRA=("$@"); T=${THREADS:-4}
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FV:-$LIGHT_LEAN/fastverify}
ST=${SELFTEST_DIR:-/scratch/fastverify-next/selftest}
W=$(mktemp -d "${TMPDIR:-/tmp}/leanleg.XXXXXX"); trap 'rm -rf "$W"' EXIT
/usr/bin/python3 -I "$FV/tests/kernel-cves/craft_cves.py" --selftest-dir "$ST" --out "$W/cves" > "$W/craft.log" 2>&1 || { echo "FAIL craft"; exit 1; }
pass=0; fail=0
run() { # run LABEL EXPORT WANT(attack|control)
  local lab=$1 e=$2 want=$3 m rc msg ok
  for m in par seq; do
    if [ $m = seq ]; then LEAN_STACK_SIZE_KB=917376 "$P" -j$T --seq "$e" > "$W/o" 2>&1; rc=$?
    else LEAN_STACK_SIZE_KB=917376 "$P" -j$T "$e" > "$W/o" 2>&1; rc=$?; fi
    msg=$(grep -v '^\[pchk' "$W/o" | tail -1 | tr '\t' ' ' | cut -c1-140)
    if [ $want = control ]; then [ $rc = 0 ] && ok=PASS || ok=FAIL; else [ $rc != 0 ] && ok=PASS || ok=FAIL; fi
    [ $ok = PASS ] && pass=$((pass+1)) || fail=$((fail+1))
    printf '%s\t%s\t%s\t%s\trc=%s\t%s\n' "$ok" "$lab" "$m" "$want" "$rc" "$msg"
  done
}
st_want() { case $1 in *control*|*baseline*|*honest*|C0*|base) echo control;; *) echo attack;; esac; }
for e in "$W"/cves/*.export; do n=$(basename "$e" .export); run "cves/$n" "$e" "$(st_want "$n")"; done
run "selftest/good" "$ST/good.export" control
if [ -n "$KIDIR" ]; then
  compgen -G "$KIDIR/*.export" > /dev/null || { echo "FAIL: no exports in the kernel-issues dir $KIDIR"; exit 1; }
  for e in "$KIDIR"/*.export; do n=$(basename "$e" .export); run "kernel-issues/$n" "$e" "$(st_want "$n")"; done
  [ -f "$KIDIR/../so/Solution.export" ] && run "kernel-issues/base" "$KIDIR/../so/Solution.export" control
fi
for X in "${EXTRA[@]}"; do   # further crafted dirs (mk_kernel_issue_exports.py's analogues, tests/lean-leg-record-checks/mk_c2_stream.py, ...): label = dir name
  compgen -G "$X/*.export" > /dev/null || { echo "FAIL: no exports in $X"; exit 1; }   # (never a silent skip)
  for e in "$X"/*.export; do n=$(basename "$e" .export); run "$(basename "$X")/$n" "$e" "$(st_want "$n")"; done
done
echo "binary $(sha256sum "$P" | cut -d' ' -f1)"
if [ $fail = 0 ]; then echo "RESULT PASS $pass"; else echo "RESULT FAIL $fail (pass $pass)"; fi
[ $fail = 0 ]
