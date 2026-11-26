#!/bin/bash
# test 003 (kind component: the Lean-kernel leg of the sound check CS vs the official leanchecker 4.36, inputs in x/)
# finding: 003 patched kernel infer_proj unsigned wrap: pleanchecker-k accepted `.proj S 4294967295 s` (official rejects).
# The patched kernel (old option C2) and check A (C1) were retired (archive branch archive/checkA). The
# sound check's Lean leg is check A's descendant (pchk d876802 walk) and is linked against the OFFICIAL kernel libraries:
# this test keeps the regression for it. PASS iff the pleanchecker pinned in check/sound/pins.env gives the official
# verdict on wrap/ctl0/idx1 (rows <case>/CS).
{ # whole script parsed before it runs (safe against edits while running)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FV_ROOT:-$(cd "$H/../.." && pwd)}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/003.XXXXXX")}; mkdir -p "$(dirname "$W")"; L=$W.log; : > "$L"
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
pin() { awk -v n="$1" -v k="$2" '$1=="PIN" && $2==n {print $k}' "$FV/check/sound/pins.env"; }
PLC=$(pin pleanchecker 4); want=$(pin pleanchecker 3)
if [ -z "$want" ] || [ "$(sha256sum "$PLC" 2>/dev/null | cut -d' ' -f1)" != "$want" ]; then
  echo "=== RESULT case=pinned-pleanchecker official=0 fast=3" >> "$L"
else
  for c in ctl0 idx1 wrap; do
    e=$H/x/$c.ndjson
    echo "##### $c/CS" >> "$L"
    env -i PATH=/usr/bin:/bin LEAN_ABORT_ON_PANIC=1 timeout 600 "$TC/bin/leanchecker" --from-export "$e" >> "$L" 2>&1; o=$?
    env -i PATH=/usr/bin:/bin LEAN_ABORT_ON_PANIC=1 timeout 600 "$PLC" -j4 --from-export "$e" >> "$L" 2>&1; f=$?
    [ $o = 0 ] || o=1; case $f in 0|1) ;; 124) f=E124;; *) f=1;; esac
    echo "=== RESULT case=$c/CS official=$o fast=$f" >> "$L"
  done
fi
python3 -I "$H/../lib/parse.py" 003 "$L" | tee "$W.tsv"
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}
