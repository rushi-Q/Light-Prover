#!/bin/bash
# Regression tests of two low-memory classes (a BFS fan-in bound and duplicate declarations), on every sound judge.
#  x/a01b-fanin70.export : 70 definitions X_i : Nat, X_i uses every X_j (j < i) -> 2,415 edges into a (num_decls+16)-entry
#     BFS stack; X_1 := Q02badAx, an ILLEGAL axiom; the target's proof mentions X_1..X_70. Pre-fix ccmp-lowmem pushed once
#     per EDGE without a bound (an instrumented build corrupted its arena and named the wrong axiom). Every judge must
#     REJECT, and the reason must name Q02badAx (the right axiom = the BFS saw the real graph).
#  x/a02-weak-first.export / x/a02-strong-first.export : the target declared twice under two name indices of the same Name
#     (one copy with the challenge statement and an ill-typed proof, one with statement True). Official reader:
#     'Duplicate declaration'. The low-memory COMPARISON keeps the last copy (LOW), so the verdict must come from
#     the kernel legs: every judge must give a non-ACCEPTED verdict.
# usage: a01b-a02-regress.sh [CHECK_SCRIPT [extra args...]]   (default: all sound judges of this package, default pins)
# exit 0 iff every run passes.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
F=$(cd "$HERE/../../check" && pwd)
S=/scratch/fastverify-next/selftest
W=$(mktemp -d "${TMPDIR:-/tmp}/anonymous-axiom.XXXXXX") || { echo "FAIL setup: mktemp"; exit 1; }; trap 'rm -rf "$W"' EXIT
mkdir -p "$W/wd"
( cd "$HERE/x" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL fixtures: sha256 mismatch"; exit 1; }
fails=0
run() {  # run LABEL INPUT NEED SCRIPT [args]   NEED = substring the reason must contain ('' = any non-ACCEPTED verdict)
  local lab=$1 inp=$2 need=$3 scr=$4; shift 4
  "$scr" "$inp" "$S/challenge.export" "$S/comparator.json" --threads 2 --workdir "$W/wd" "$@" > "$W/out.json" 2>/dev/null; local rc=$?
  local v why
  v=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["verdict"])' "$W/out.json" 2>/dev/null)
  why=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["reason"][:160])' "$W/out.json" 2>/dev/null)
  if [ "$rc" = 0 ] || [ "$v" = ACCEPTED ]; then echo "FAIL $lab: rc=$rc verdict=$v (false ACCEPTED)"; fails=$((fails+1)); return; fi
  if [ -z "$v" ]; then echo "FAIL $lab: rc=$rc, no verdict JSON (judge did not run?)"; fails=$((fails+1)); return; fi
  if [ -n "$need" ] && [ "$v" != REJECTED -o "${why#*$need}" = "$why" ]; then
    echo "FAIL $lab: rc=$rc verdict=$v, reason lacks '$need': $why"; fails=$((fails+1)); return; fi
  echo "PASS $lab: rc=$rc verdict=$v ($why)"
}
cases() {  # cases LABEL SCRIPT [args]
  local lab=$1; shift
  run "$lab/a01b-fanin70" "$HERE/x/a01b-fanin70.export" "Q02badAx" "$@"
  run "$lab/a02-weak-first" "$HERE/x/a02-weak-first.export" "" "$@"
  run "$lab/a02-strong-first" "$HERE/x/a02-strong-first.export" "" "$@"
}
if [ $# -gt 0 ]; then
  cases custom "$@"
else
  cases sound "$F/sound/check-sound.sh"
  cases lowmem "$F/lowmem/check-sound-lowmem.sh"
  cases ultralowmem "$F/lowmem/check-sound-ultralowmem.sh"
  cases lowmem437 "$F/lowmem/check-sound-lowmem.sh" --pins "$F/lowmem/pins-437.env"
  cases notary "$F/notary/check-notary.sh"
fi
echo "RESULT fails=$fails"
[ "$fails" = 0 ]
