#!/bin/bash
# tests/lean-leg-record-checks/incr.sh PLEANCHECKER_INCR [KERNEL_ISSUES_DIR] [DIR...]
# The incremental / targeted paths of the pleanchecker_incr leg on the crafted corpora: for every case E,
#   full-a : --incremental, commands "snap <selftest good>" then "final E"   (B's honest part taken from E, the rest FRESH)
#   full-b : --incremental, commands "snap E" then "final E"                (the crafted records arrive in a SNAPSHOT first)
#   tgt-a  : --incremental --targeted=<every theorem/definition name of good.export>, "snap good" then "final E"
#   tgt-b  : --incremental --targeted=<same>, "snap E" then "final E"
# Attack = rc != 0 (no ACCEPT), control = rc 0. Prints TSV rows and 'RESULT PASS n' / 'RESULT FAIL n'.
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
P=$1; KIDIR=${2:-}; shift; [ $# -gt 0 ] && shift; EXTRA=("$@"); T=${THREADS:-4}
FV=${FV:-$LIGHT_LEAN/fastverify}; ST=${SELFTEST_DIR:-/scratch/fastverify-next/selftest}
W=$(mktemp -d "${TMPDIR:-/tmp}/leanleg-incr.XXXXXX"); trap 'rm -rf "$W"' EXIT
/usr/bin/python3 -I "$FV/tests/kernel-cves/craft_cves.py" --selftest-dir "$ST" --out "$W/cves" > "$W/craft.log" 2>&1 || { echo "FAIL craft"; exit 1; }
# targets: every name of a theorem / definition record of good.export (lean4export 3.1 NDJSON: "thm"/"defn" objects)
/usr/bin/python3 -I - "$ST/good.export" "$W/targets.txt" <<'PY'
import json, sys
names = {}; out = []
for ln in open(sys.argv[1], encoding="utf-8"):
    o = json.loads(ln)
    if "in" in o and "str" in o: names[o["in"]] = (o["str"]["pre"], o["str"]["str"])
    elif "in" in o and "num" in o: names[o["in"]] = (o["num"]["pre"], str(o["num"]["i"]))
    for k in ("thm", "defn"):
        if k in o: out.append(o[k]["name"])
def s(i):
    parts = []
    while i:
        p, c = names[i]; parts.append(c); i = p
    return ".".join(reversed(parts))
open(sys.argv[2], "w").write("\n".join(s(i) for i in out) + "\n")
PY
pass=0; fail=0
one() { # one LABEL EXPORT WANT MODE
  local lab=$1 e=$2 want=$3 mode=$4 snap fl rc ok
  case $mode in full-a|tgt-a) snap=$ST/good.export;; *) snap=$e;; esac
  case $mode in tgt-*) fl=--targeted=$W/targets.txt;; *) fl=;; esac
  printf 'snap %s\nfinal %s\n' "$snap" "$e" | LEAN_STACK_SIZE_KB=917376 "$P" --incremental $fl -j$T -v > "$W/o" 2>&1; rc=$?
  if [ $want = control ]; then [ $rc = 0 ] && ok=PASS || ok=FAIL; else [ $rc != 0 ] && ok=PASS || ok=FAIL; fi
  [ $ok = PASS ] && pass=$((pass+1)) || fail=$((fail+1))
  printf '%s\t%s\t%s\t%s\trc=%s\t%s\n' "$ok" "$lab" "$mode" "$want" "$rc" "$(grep -E 'incr\]|rejects|accepts' "$W/o" | grep -v '^\[pchk' | tail -2 | tr '\t\n' '  ' | cut -c1-200)"
}
st_want() { case $1 in *control*|*baseline*|*honest*|C0*|base|good) echo control;; *) echo attack;; esac; }
cases=()
for e in "$W"/cves/*.export; do cases+=("cves/$(basename "$e" .export)=$e"); done
cases+=("selftest/good=$ST/good.export")
# (a given directory without exports is a FAILURE, never a silent skip)
for X in ${KIDIR:+"$KIDIR"} "${EXTRA[@]}"; do compgen -G "$X/*.export" > /dev/null || { echo "FAIL: no exports in $X"; exit 1; }; done
[ -n "$KIDIR" ] && for e in "$KIDIR"/*.export; do cases+=("kernel-issues/$(basename "$e" .export)=$e"); done
for X in "${EXTRA[@]}"; do for e in "$X"/*.export; do cases+=("$(basename "$X")/$(basename "$e" .export)=$e"); done; done
for c in "${cases[@]}"; do
  lab=${c%%=*}; e=${c#*=}; w=$(st_want "$(basename "$lab")")
  for mode in full-a full-b tgt-a tgt-b; do one "$lab" "$e" "$w" $mode; done
done
echo "binary $(sha256sum "$P" | cut -d' ' -f1)"
if [ $fail = 0 ]; then echo "RESULT PASS $pass"; else echo "RESULT FAIL $fail (pass $pass)"; fi
[ $fail = 0 ]
