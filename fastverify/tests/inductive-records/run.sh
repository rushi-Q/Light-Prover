#!/bin/bash
# tests/inductive-records/run.sh [FV_ROOT] - regression test of inductive export records
# no official-kernel leg may hand the C++ kernel an export record of an inductive block.
# Inputs (x/, sha256 in x/SHA256SUMS): the SegSol exports - sol.export (valid), m_numMotives_-1 / m_numMinors_-1
# (MyB.rec numMotives resp. numMinors lowered by one; official leanchecker: "Invalid recursor"; previously every parallel-walk
# leg crashed, exit 139, and every judge said DECLINED), Challenge.export, cfg.json; plus two exports made here by
# mkf7tests.py from sol.export: f7_selfloop (sel := sel, used by a later constructor type: liveness of the learner budget and
# of the walk's cancel token; official: "unknown constant 'sel'") and f7_taken_rec (MyB's recursor record replaced by a
# definition named MyB.rec: the walk's taken-name check; official: "already declared"). Plus two
# Bool.rec mutants of sol.export (m_BoolRec_numMotives_-1 sha256 0acdf73c..., m_BoolRec_numMinors_-1 3b96ff7b...: Init's
# Bool.rec numMotives resp. numMinors lowered by one; official: "Invalid recursor Bool.rec"; earlier legs: exit 139).
# Part A: every pinned Lean-leg binary of FV_ROOT alone (-j1 and -j8): exit code and message = official.
# Part B: every judge end to end on the SegSol exports: sol ACCEPTED, mutants REJECTED.
# Prints PASS/FAIL rows (INFO rows are not counted) and 'RESULT pass=N fail=M'; exit 0 iff no FAIL.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${1:-$(cd "$H/../.." && pwd)}
X=$H/x; (cd "$X" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL setup: x/SHA256SUMS"; echo "RESULT pass=0 fail=1"; exit 1; }
W=$(mktemp -d "${TMPDIR:-/tmp}/f7-ind.XXXXXX") || exit 2; trap 'rm -rf "$W"' EXIT
python3 -I "$H/mkf7tests.py" "$X/sol.export" "$W/x" > /dev/null || { echo "FAIL setup: mkf7tests.py"; echo "RESULT pass=0 fail=1"; exit 1; }
pass=0; fail=0
pin() { awk -v n="$2" '$1=="PIN" && $2==n {print $4}' "$FV/$1"; }
ok() { pass=$((pass+1)); echo "PASS $*"; }
ko() { fail=$((fail+1)); echo "FAIL $*"; }
leg() { # leg LABEL BIN EXPORT WANT_RC WANT_MSG_REGEX COUNT(1|0) [args...]
  local lab=$1 bin=$2 x=$3 wrc=$4 wmsg=$5 cnt=$6; shift 6
  local out rc
  out=$(LEAN_ABORT_ON_PANIC=1 LEAN_STACK_SIZE_KB=917376 timeout 150 "$bin" "$@" "$x" 2>&1); rc=$?
  local last; last=$(printf '%s\n' "$out" | grep -v '^\[pchk' | tail -1 | cut -c1-150)
  if [ "$rc" = "$wrc" ] && printf '%s' "$out" | grep -Eq -- "$wmsg"; then [ $cnt = 1 ] && ok "$lab $(basename "$x") $*: rc=$rc" || echo "INFO(ok) $lab $(basename "$x") $*: rc=$rc"
  else [ $cnt = 1 ] && ko "$lab $(basename "$x") $*: rc=$rc (want $wrc /$wmsg/) | $last" || echo "INFO(differs) $lab $(basename "$x") $*: rc=$rc (want $wrc) | $last"; fi
}
legset() { # legset LABEL BIN COUNT [extra args]
  local lab=$1 bin=$2 cnt=$3; shift 3
  [ -x "$bin" ] || { ko "$lab: pinned binary missing: $bin"; return; }
  for j in -j1 -j8; do
    leg "$lab" "$bin" "$X/sol.export" 0 "accepts the solution" $cnt $j "$@"
    leg "$lab" "$bin" "$X/m_numMotives_-1.export" 1 "Invalid recursor MyB.rec" $cnt $j "$@"
    leg "$lab" "$bin" "$X/m_numMinors_-1.export" 1 "Invalid recursor MyB.rec" $cnt $j "$@"
    # the same one-field lie on Init's Bool.rec (also exit 139 on the earlier legs)
    leg "$lab" "$bin" "$X/m_BoolRec_numMotives_-1.export" 1 "Invalid recursor Bool.rec" $cnt $j "$@"
    leg "$lab" "$bin" "$X/m_BoolRec_numMinors_-1.export" 1 "Invalid recursor Bool.rec" $cnt $j "$@"
    # (the ultra-low-memory streaming pass names the collision itself: "Duplicate declaration: MyB.rec")
    leg "$lab" "$bin" "$W/x/f7_taken_rec.export" 1 "already been declared 'MyB.rec'|Duplicate declaration: MyB.rec" $cnt $j "$@"
  done
  leg "$lab" "$bin" "$W/x/f7_selfloop.export" 1 "unknown constant 'sel'" ${SELFLOOP_COUNT:-$cnt} -j8 "$@"
}
# Part A
legset default "$(pin check/sound/pins.env pleanchecker)" 1
PCHK_F7_SYNC=1 legset default-sync "$(pin check/sound/pins.env pleanchecker)" 1
legset incr-plain "$(pin check/sound/pins.env pleanchecker_incr)" 1
legset lean437 "$(pin check/sound/pins-437.env pleanchecker)" 1
legset notary "$(pin check/notary/pins.env pleanchecker_notary)" 1
# (f7_selfloop is an INFO row for the --low-mem streaming pass: it does not terminate there - the streaming pass has no
#  cancellation of a later inductive check by an earlier rejection; pre-existing, reported to the owner F2; the judge's
#  timeout makes it DECLINED, never a verdict)
SELFLOOP_COUNT=0 legset ultralowmem-lowmem "$(pin check/lowmem/pins-ultralowmem.env pleanchecker_lowmem)" 1 --low-mem --evict=smart
# the ultra-low-memory binary's non-low-mem mode is not used by any judge; it is fixed by F2's rebuild with the F7 walk
legset ultralowmem-plain "$(pin check/lowmem/pins-ultralowmem.env pleanchecker_lowmem)" 0
# Part B
judge() { # judge LABEL EXPORT WANT_VERDICT WANT_RC SCRIPT [args...]
  local lab=$1 x=$2 wv=$3 wrc=$4; shift 4
  local w=$W/j.$lab.$(basename "$x" .export); mkdir -p "$w"
  ( cd "$w" && env -i PATH=/usr/bin:/bin HOME="$w" TMPDIR="$w" LANG=C.UTF-8 timeout 900 "$@" --json "$w/check.json" > "$w/log" 2>&1 ); local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$w/check.json" 2>/dev/null)
  [ "$rc" = "$wrc" ] && [ "$v" = "$wv" ] && ok "judge $lab $(basename "$x"): $v $rc" || ko "judge $lab $(basename "$x"): $v $rc (want $wv $wrc) | $(tail -1 "$w/log" | cut -c1-150)"
}
for n in sol m_numMotives_-1 m_numMinors_-1 m_BoolRec_numMotives_-1 m_BoolRec_numMinors_-1; do
  [ $n = sol ] && { wv=ACCEPTED; wr=0; } || { wv=REJECTED; wr=1; }
  A=("$X/$n.export" "$X/Challenge.export" "$X/cfg.json" --threads 8)
  judge check-sound "$X/$n.export" $wv $wr "$FV/check/sound/check-sound.sh" "${A[@]}"
  judge check-sound-svc "$X/$n.export" $wv $wr "$FV/check/sound/check-sound-svc.sh" "${A[@]}"
  judge check-sound-lowmem "$X/$n.export" $wv $wr "$FV/check/lowmem/check-sound-lowmem.sh" "${A[@]}"
  judge check-sound-ultralowmem "$X/$n.export" $wv $wr "$FV/check/lowmem/check-sound-ultralowmem.sh" "${A[@]}"
  judge check-sound-437 "$X/$n.export" $wv $wr "$FV/check/sound/check-sound.sh" "${A[@]}" --pins "$FV/check/sound/pins-437.env" --hide "$FV/check/sound/hide/lean-4.37.0-rc1-no-expose.txt"
  judge check-notary "$X/$n.export" $wv $wr "$FV/check/notary/check-notary.sh" "${A[@]}"
done
echo "RESULT pass=$pass fail=$fail"
[ $fail = 0 ]
