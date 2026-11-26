#!/bin/bash
# tests/fvwork/run-release.sh RELEASE [WORKDIR] - fvwork's --build lake path on another OFFICIAL release (e.g.
# leanprover/lean4:v4.37.0-rc1): the same tiny fixture with its lean-toolchain set to RELEASE. The package must list
# RELEASE in config/components.json (tools/addrelease.py). Cases:
#   base        bin/fastverify --preset sound on the fixture (official build + the release's official exporter + CS) ACCEPTED
#   lake-init   fvwork init --build lake (cold official lake build + official exporter) + serve
#   lake-have   proof edit in Tiny/A.lean -> ACCEPTED
#   lake-sorry  `have ... := sorry` in Tiny/B.lean -> REJECTED (sorryAx)
#   lake-break  ill-typed step -> REJECTED at the build, with Lean's diagnostics
#   lake-kbad   a `decide +kernel` theorem the official kernel refuses -> REJECTED (build or trusted check)
#   lake-stmt   the target theorem's statement changed -> REJECTED (statement comparison)
#   lake-fixed  back to the original proof -> ACCEPTED
# FVTEST_PINS=FILE runs the same cases judged by another release's trusted check (serve --pins FILE; e.g. check/sound/pins-437.env).
# Prints 'PASS|FAIL case: detail' rows and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
FW=${FVWORK:-$FV/tools/fvwork/fvwork.py}
REL=${1:?usage: run-release.sh RELEASE [WORKDIR]}; case "$REL" in leanprover/lean4:*) ;; *) REL="leanprover/lean4:v${REL#v}" ;; esac
W=${2:-$(mktemp -d "${TMPDIR:-/tmp}/fvwork-release.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; fails=0; T=${EVAL_THREADS:-8}
row() { echo "$1 $2: $3"; if [ "$1" = FAIL ]; then fails=$((fails+1)); fi; return 0; }
TC=$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(c["lean_toolchains"][sys.argv[2]]["prefix"])' \
     "$FV/config/components.json" "$REL" 2>/dev/null) || { row FAIL release "$REL not in $FV/config/components.json (tools/addrelease.py)"; echo "RESULT FAIL"; exit 1; }
cp -r "$H/x" "$W/x"; for d in tiny challenge; do echo "$REL" > "$W/x/$d/lean-toolchain"; done
cp -r "$W/x/challenge" "$W/ch"
"$FV/bin/fastverify" "$W/x/tiny" "$W/ch" "$W/base" --preset sound --threads "$T" --keep-work > "$W/base.log" 2>&1
rc=$?; [ $rc = 0 ] && row PASS base "ACCEPTED ($REL)" || { row FAIL base "exit $rc (see $W/base.log)"; echo "RESULT FAIL"; exit 1; }
cp "$W/base/challenge.export" "$W/ch/"; CSHA=$(sha256sum "$W/ch/challenge.export" | cut -d' ' -f1)
WS=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["inputs"]["packages_workspace"] or "")' "$W/base/result.json")
files() { local o=$1; shift
  python3 -I -c 'import json,sys; a=sys.argv[2:]; json.dump({a[i]: a[i+1] for i in range(0, len(a), 2)}, open(sys.argv[1], "w"))' "$o" "$@"; }
ask() { local st=$1 n=$2; shift 2
  python3 -I "$FW" verify --state "$st" "$@" > "$W/$n.out" 2>&1; local rc=$?; tail -1 "$W/$n.out" > "$W/$n.json"; return $rc; }
jq_() { python3 -I -c "import json,sys; r=json.load(open(sys.argv[1])); print($2)" "$W/$1.json" 2>/dev/null; }
A_HAVE=$'theorem tinyA (n : Nat) : n + 0 = n := by\n  have _fvw : (2 : Nat) + 2 = 4 := rfl\n  rfl\n'
B_ORIG=$(cat "$W/x/tiny/Tiny/B.lean"); A_ORIG=$(cat "$W/x/tiny/Tiny/A.lean"); S_ORIG=$(cat "$W/x/tiny/Solution.lean")
B_SORRY=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  have _fvw : (2 : Nat) + 2 = 4 := sorry\n  rw [tinyA]\n'
B_BREAK=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  have _fvw : (2 : Nat) + 2 = 5 := rfl\n  rw [tinyA]\n'
B_KBAD=$(cat "$W/x/kbad/Tiny/B.lean"); S_KBAD=$(cat "$W/x/kbad/Solution.lean")
S_STMT=$'import Tiny.B\ntheorem foo : (2 : Nat) + 2 = 4 \xe2\x88\xa7 True := by\n  have h := tinyB\n  rw [tinyA] at h\n  exact \xe2\x9f\xa8h, trivial\xe2\x9f\xa9\n'
ST=$W/st
python3 -I "$FW" init --state "$ST" --project "$W/x/tiny" --challenge "$W/ch" --challenge-sha256 "$CSHA" --threads "$T" \
  --fv "$FV" --tc "$TC" ${WS:+--packages "$WS"} --build lake > "$ST.init.log" 2>&1 \
  || { row FAIL lake-init "$(tail -2 "$ST.init.log")"; echo "RESULT FAIL"; exit 1; }
# FVTEST_PINS=FILE: judge with another release's trusted check (serve --pins, e.g. check/sound/pins-437.env)
python3 -I "$FW" serve --state "$ST" --warm 1 --threads "$T" ${FVTEST_PINS:+--pins "$FVTEST_PINS"} > "$ST.serve.log" 2>&1 &
for i in $(seq 1 100); do [ -S "$ST/sock" ] && break; sleep 0.1; done
[ -S "$ST/sock" ] && row PASS lake-init "$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(c["build"], c["release"])' "$ST/config.json")" \
  || { row FAIL lake-init "no socket"; echo "RESULT FAIL"; exit 1; }
sleep 2
files "$W/have.files" Tiny/A.lean "$A_HAVE"; ask "$ST" lake-have --files "$W/have.files"; rc=$?
v=$(jq_ lake-have 'r["verdict"], r["attempts"][0]["mode"]')
[ $rc = 0 ] && [ "$v" = "ACCEPTED lake" ] && row PASS lake-have "$v ($(jq_ lake-have 'r["build_s"], r["export_s"], r["check_s"]'))" || row FAIL lake-have "exit $rc: $v $(jq_ lake-have 'r.get("why")')"
files "$W/sorry.files" Tiny/B.lean "$B_SORRY"; ask "$ST" lake-sorry --files "$W/sorry.files"; rc=$?
v=$(jq_ lake-sorry 'r["verdict"], "sorryAx" in (r.get("why") or "")')
[ $rc = 1 ] && [ "$v" = "REJECTED True" ] && row PASS lake-sorry "$v" || row FAIL lake-sorry "exit $rc: $v $(jq_ lake-sorry 'r.get("why")')"
files "$W/break.files" Tiny/B.lean "$B_BREAK"; ask "$ST" lake-break --files "$W/break.files"; rc=$?
v=$(jq_ lake-break 'r["verdict"], r["attempts"][0]["outcome"], len(r["attempts"][0].get("diagnostics", [])) > 0')
[ $rc = 1 ] && [ "$v" = "REJECTED build1 True" ] && row PASS lake-break "$v" || row FAIL lake-break "exit $rc: $v"
files "$W/kbad.files" Tiny/B.lean "$B_KBAD" Solution.lean "$S_KBAD"; ask "$ST" lake-kbad --files "$W/kbad.files"; rc=$?
v=$(jq_ lake-kbad 'r["verdict"], r["attempts"][-1]["outcome"]')
[ $rc = 1 ] && case "$v" in REJECTED*) true;; *) false;; esac && row PASS lake-kbad "$v ($(jq_ lake-kbad '(r.get("why") or "")[:80]'))" || row FAIL lake-kbad "exit $rc: $v"
files "$W/stmt.files" Tiny/B.lean "$B_ORIG"$'\n' Solution.lean "$S_STMT"; ask "$ST" lake-stmt --files "$W/stmt.files"; rc=$?
v=$(jq_ lake-stmt 'r["verdict"], r["attempts"][-1]["outcome"]')
[ $rc = 1 ] && [ "$v" = "REJECTED check1" ] && row PASS lake-stmt "$v ($(jq_ lake-stmt '(r.get("why") or "")[:80]'))" || row FAIL lake-stmt "exit $rc: $v"
files "$W/fixed.files" Tiny/A.lean "$A_ORIG"$'\n' Tiny/B.lean "$B_ORIG"$'\n' Solution.lean "$S_ORIG"$'\n'; ask "$ST" lake-fixed --files "$W/fixed.files"; rc=$?
v=$(jq_ lake-fixed 'r["verdict"]'); [ $rc = 0 ] && [ "$v" = ACCEPTED ] && row PASS lake-fixed "$v" || row FAIL lake-fixed "exit $rc: $v $(jq_ lake-fixed 'r.get("why")')"
python3 -I "$FW" stop --state "$ST" > /dev/null 2>&1
[ $fails = 0 ] && echo "RESULT PASS" || { echo "RESULT FAIL ($fails)"; exit 1; }
