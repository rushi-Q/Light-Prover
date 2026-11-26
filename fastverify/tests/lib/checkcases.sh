#!/bin/bash
# checkcases.sh TESTDIR WORK  -- export-level regression cases: every FAST checker of the package vs the OFFICIAL comparator.
# Cases: TESTDIR/CASES, one per line (blank lines and '#' comments ignored), fields separated by '|':
#   name | challenge.export | solution.export | comparator.json | official_rc | mode | env
#   * paths relative to TESTDIR/x/ (or absolute; '@/' = tests/common/)
#   * official_rc = the official verdict recorded with the repro (0 accept, 1 reject). The official comparator is re-run live
#     (lib/official-check.sh) unless FV_TEST_OFFICIAL=recorded, or the value carries a '*' (slow official run: recorded
#     value used unless FV_TEST_OFFICIAL=live).
#   * mode: plain | path:SUBDIR (solution placed under WORK/<case>/SUBDIR/) | pipe (solution passed as /dev/stdin) |
#           nochallenge (empty CHALLENGE argument) | cwd:DIR (DIR's files copied into the checker's working dir) |
#           rlimit:KB (ulimit -v for official AND fast) | gen:SCRIPT[+MODE] (SCRIPT OUT generates the solution first, then MODE)
#   * env: extra VAR=VALUE words put into the checker's environment (pollution tests: must not change any verdict)
# Checkers: the menu's check options C3, C4 (see DEFCHK below; FV_CHECKERS overrides), called as
#   CHECKER EXPORT CHALLENGE_EXPORT COMPARATOR_JSON --threads N --json FILE [ARGS]  (exit 0 accept, 1 reject, 2 decline).
# Plus the package entry point as a pseudo-checker 'fastverify' (bin/fastverify - DIR OUT --export SOL --check C3; verdict
# ACCEPTED/REJECTED/DECLINED -> 0/1/2, ERROR -> 4), unless FV_NO_ENTRY=1.
# Output: '=== RESULT case=<name>/<checker> official=<rc> fast=<rc>' lines -> lib/parse.py rows (WORK.log, WORK.tsv).
{ # whole script parsed before it runs (safe against edits while running)
set -u
H=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd); TR=$(cd "$H/.." && pwd); FVROOT=${FV_ROOT:-$(cd "$TR/.." && pwd)}
TD=$(cd "$1" && pwd); W=$2; id=$(basename "$TD"); case $id in [0-9][0-9][0-9]-*) id=${id:0:3};; esac; X=$TD/x
mkdir -p "$W"; W=$(readlink -f "$W"); L=$W.log; : > "$L"
T=${EVAL_THREADS:-8}
# checker variants = the menu's check options: C3 check-b.sh (dual), C4 check-b.sh --single (UNSAFE). (C1/C2 = check A's
# check-a.sh were retired.) Entries NAME=SCRIPT[:ARG,...]; rows of UNSAFE variants carry '!unsafe' in the
# case name and their FAIL rows are reported as UNSAFE-FAIL-* (documented breakage of an opt-in option, not a package failure).
CB=$FVROOT/check/checkB/check-b.sh
DEFCHK="C3=$CB C4!unsafe=$CB:--single"
CHK=${FV_CHECKERS:-$DEFCHK}
# the package entry point on the same export: bin/fastverify - CHALLENGE_DIR OUT --export SOL --check C3 (pseudo-checker)
FVB=${FV_BIN:-$FVROOT/bin/fastverify}
case $FVB in *standin*) ;; *) [ -x "$FVB" ] && [ "${FV_NO_ENTRY:-0}" != 1 ] && CHK="$CHK @fastverify";; esac
rp() { case $1 in /*) echo "$1";; @/*) echo "$TR/common/${1#@/}";; '') echo "";; *) echo "$X/$1";; esac; }
trim() { local s=$1; s=${s#"${s%%[![:space:]]*}"}; s=${s%"${s##*[![:space:]]}"}; printf '%s' "$s"; }
n=0
while IFS='|' read -r name ch so cfg orc mode envs <&3; do
  name=$(trim "$name"); case $name in ''|'#'*) continue;; esac
  ch=$(rp "$(trim "$ch")"); so=$(rp "$(trim "$so")"); cfg=$(rp "$(trim "$cfg")"); orc=$(trim "$orc"); mode=$(trim "${mode:-plain}"); envs=$(trim "${envs:-}")
  [ -n "$mode" ] || mode=plain
  n=$((n+1)); C=$W/c$n; mkdir -p "$C/cwd"; echo "##### $name  (mode=$mode env=$envs)" >> "$L"
  case $mode in gen:*) g=${mode#gen:}; m2=plain; case $g in *+*) m2=${g#*+}; g=${g%%+*};; esac
    echo "  generating: $g $C/gen.export" >> "$L"; (cd "$X" && bash "$(rp "$g")" "$C/gen.export") >> "$L" 2>&1 < /dev/null; so=$C/gen.export; mode=$m2;; esac
  lim=""; case $mode in rlimit:*) lim="ulimit -v ${mode#rlimit:};";; esac
  # official verdict
  rec=${orc%\*}; live=1
  { [ "${FV_TEST_OFFICIAL:-}" = recorded ] || { [ "$orc" != "$rec" ] && [ "${FV_TEST_OFFICIAL:-}" != live ]; }; } && live=0
  if [ $live = 1 ]; then
    o=$(bash -c "$lim bash '$H/official-check.sh' '$so' '$ch' '$cfg'" >> "$L" 2>&1 < /dev/null; echo $?)
    [ "$o" = 0 ] || o=1
    echo "  official (live): $o (recorded $rec)" >> "$L"
    [ "$o" = "$rec" ] || echo "  WARNING: live official $o differs from the recorded $rec" >> "$L"
  else o=$rec; echo "  official (recorded): $o" >> "$L"; fi
  if [ -z "$CHK" ]; then echo "=== RESULT case=$name/none official=$o fast=3" >> "$L"; continue; fi
  for k in $CHK; do
    if [ "$k" = @fastverify ]; then kn=fastverify; KA=()
    else kn=${k%%=*}; ks=${k#*=}; KA=(); case $ks in *:*) IFS=, read -r -a KA <<< "${ks#*:}"; ks=${ks%%:*};; esac; k=$ks; fi
    [ "$k" = @fastverify ] || [ -x "$k" ] || { echo "=== RESULT case=$name/$kn official=$o fast=3" >> "$L"; continue; }
    sol=$C/plain/solution.export; cha=$ch
    case $mode in
      path:*) sol=$C/${mode#path:}/solution.export;;
      nochallenge) cha="";;
      cwd:*) rm -rf "$C/cwd"; mkdir -p "$C/cwd"; cp -r "$(rp "${mode#cwd:}")"/. "$C/cwd/";;
    esac
    mkdir -p "$(dirname "$sol")"; [ -e "$sol" ] || cp "$so" "$sol"
    if [ "$k" = @fastverify ]; then   # challenge dir = comparator.json + challenge.export + lean-toolchain
      CD=$C/challenge-dir; rm -rf "$CD" "$C/fvout"; mkdir -p "$CD"; cp "$cfg" "$CD/comparator.json"
      [ -n "$cha" ] && cp "$cha" "$CD/challenge.export"; echo "leanprover/lean4:${FV_TEST_TOOLCHAIN:-v4.33.1}" > "$CD/lean-toolchain"
      sx=$sol; [ "$mode" = pipe ] && sx=/dev/stdin
      (cd "$C/cwd" && bash -c "$lim env $envs timeout ${FV_CHECK_TIMEOUT:-3600} '$FVB' - '$CD' '$C/fvout' --export '$sx' ${FV_ARGS_EXPORT:---check C3} --threads $T" < "$sol") >> "$L" 2>&1
      f=$(python3 -I -c 'import json,sys
try: v=json.load(open(sys.argv[1])).get("verdict","")
except Exception: v=""
print({"ACCEPTED":0,"REJECTED":1,"DECLINED":2}.get(v,4))' "$C/fvout/result.json")
    elif [ "$mode" = pipe ]; then
      f=$(cd "$C/cwd" && bash -c "$lim env $envs timeout ${FV_CHECK_TIMEOUT:-3600} '$k' /dev/stdin '$cha' '$cfg' --threads $T --json '$C/$kn.json' ${KA[*]:-} < '$sol'" >> "$L" 2>&1; echo $?)
    else
      f=$(cd "$C/cwd" && bash -c "$lim env $envs timeout ${FV_CHECK_TIMEOUT:-3600} '$k' '$sol' '$cha' '$cfg' --threads $T --json '$C/$kn.json' ${KA[*]:-}" >> "$L" 2>&1 < /dev/null; echo $?)
    fi
    case $f in 0|1|2|4) ;; *) f=E$f;; esac
    echo "=== RESULT case=$name/$kn official=$o fast=$f" >> "$L"
  done
done 3< "$TD/CASES"
python3 -I "$H/parse.py" "$id" "$L" | tee "$W.tsv"
[ -n "${KEEP_WORK:-}" ] || rm -rf "$W"
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}
