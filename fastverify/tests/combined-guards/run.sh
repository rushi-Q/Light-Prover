#!/bin/bash
# tests/combined-guards/run.sh - regression test of the combined judge-side patch's guards (axiom set + definition holes
# on canonical names, cross-version step, private-copy pins) on check-sound.sh, check-sound-svc.sh and
# check-notary.sh (+ the pin check of check-frontier.sh). The low-memory judges have tests/lowmem-guards.
# Each case must give exactly the expected verdict; a guard that silently stops working shows up as ACCEPTED or as a
# different verdict.  usage: run.sh [JUDGE_SCRIPT...]   (default: the three judges of THIS package copy)
# Prints PASS/FAIL rows and RESULT pass=N fail=M; exit 0 iff all PASS. Writes only below a mktemp dir in $TMPDIR.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
F=$(cd "$HERE/../../check" && pwd)
S=/scratch/fastverify-next/selftest
X=/scratch/fastverify-next/fixtures/lean-4.37            # official 4.37 toy: hole f is NOT sorried (VERDICTS: good REJECTED)
W=$(mktemp -d "${TMPDIR:-/tmp}/combined-guards.XXXXXX") || { echo "FAIL setup: mktemp"; exit 1; }; trap 'rm -rf "$W"' EXIT
for f in "$S/challenge.export" "$S/good.export" "$S/comparator.json" "$X/challenge.export" "$X/good.export" "$X/comparator.json"; do
  [ -f "$f" ] || { echo "FAIL setup: fixture missing: $f"; exit 1; }
done
mkdir -p "$W/wd"
# configs derived from the selftest's comparator.json (theorem fvSelfTest)
python3 -I - "$S/comparator.json" "$W" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); w = sys.argv[2]
def put(name, **kw):
    d = dict(c); d.update(kw); json.dump(d, open('%s/%s.json' % (w, name), 'w'))
put('ax-sorry', permitted_axioms=c['permitted_axioms'] + ['sorryAx'])
put('ax-sorry-guillemet', permitted_axioms=c['permitted_axioms'] + ['«sorryAx»'])
put('hole-primitive', definition_names=['Nat.gcd'])
put('hole-primitive-guillemet', definition_names=['«Nat».«gcd»'])
put('hole-target', definition_names=list(c['theorem_names']))
put('ax-propext-guillemet', permitted_axioms=['«propext»', 'Quot.sound', 'Classical.choice'])
PY
# a challenge whose header names an unadmitted release (everything else = the selftest challenge)
python3 -I - "$S/challenge.export" "$W/chal-4.99.export" <<'PY'
import json, sys
src, out = sys.argv[1:3]
with open(src, 'rb') as f, open(out, 'wb') as o:
    m = json.loads(f.readline()); m['meta']['lean'] = {'githash': 'deadbeef' * 5, 'version': '4.99.0'}
    o.write((json.dumps(m, separators=(',', ':')) + '\n').encode()); o.write(f.read())
PY
CS=$(sha256sum "$S/challenge.export" | cut -c1-64); CF=$(sha256sum "$S/comparator.json" | cut -c1-64)
pass=0; fail=0
run() {  # run LABEL WANT_VERDICT WANT_SUBSTRING SCRIPT EXPORT CHALLENGE CONFIG [extra args]
  local lab=$1 want=$2 sub=$3 scr=$4 e=$5 c=$6 j=$7; shift 7
  "$scr" "$e" "$c" "$j" --threads 2 --workdir "$W/wd" "$@" > "$W/out.json" 2>/dev/null; local rc=$?
  local v why
  v=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["verdict"])' "$W/out.json" 2>/dev/null)
  why=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["reason"][:150])' "$W/out.json" 2>/dev/null)
  if [ -z "$v" ]; then echo "FAIL $lab: rc=$rc, no verdict JSON"; fail=$((fail+1)); return; fi
  if [ "$v" != "$want" ] || { [ -n "$sub" ] && [ "${why#*"$sub"}" = "$why" ]; }; then
    echo "FAIL $lab: rc=$rc verdict=$v (want $want with '$sub'): $why"; fail=$((fail+1)); return; fi
  echo "PASS $lab: rc=$rc $v ($why)"; pass=$((pass+1))
}
judge() {  # judge LABEL SCRIPT
  local l=$1 j=$2
  run "$l/honest+pins" ACCEPTED "" "$j" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --challenge-sha256 "$CS" --comparator-sha256 "$CF"
  run "$l/propext-guillemet" ACCEPTED "" "$j" "$S/good.export" "$S/challenge.export" "$W/ax-propext-guillemet.json"
  run "$l/sorryAx-permitted" DECLINED "outside GOAL S1(3)" "$j" "$S/challenge.export" "$S/challenge.export" "$W/ax-sorry.json"
  run "$l/sorryAx-guillemet" DECLINED "outside GOAL S1(3)" "$j" "$S/challenge.export" "$S/challenge.export" "$W/ax-sorry-guillemet.json"
  run "$l/hole-primitive" DECLINED "definition_names" "$j" "$S/good.export" "$S/challenge.export" "$W/hole-primitive.json"
  run "$l/hole-primitive-guillemet" DECLINED "definition_names" "$j" "$S/good.export" "$S/challenge.export" "$W/hole-primitive-guillemet.json"
  run "$l/hole-is-target" DECLINED "definition_names" "$j" "$S/good.export" "$S/challenge.export" "$W/hole-target.json"
  run "$l/437-hole-not-sorried" REJECTED "not sorried" "$j" "$X/good.export" "$X/challenge.export" "$X/comparator.json"
  # the notary decides its v0.1 kernel scope (the selftest config's nanoda on a Lean >= 4.37 release) before xversion
  if [ "$l" = check-notary ]; then run "$l/unadmitted-release" DECLINED "the challenge is Lean 4.99.0" "$j" "$S/good.export" "$W/chal-4.99.export" "$S/comparator.json"
  else run "$l/unadmitted-release" DECLINED "xversion" "$j" "$S/good.export" "$W/chal-4.99.export" "$S/comparator.json"; fi
  run "$l/wrong-challenge-pin" DECLINED "--challenge-sha256" "$j" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --challenge-sha256 "$CF"
  run "$l/wrong-config-pin" DECLINED "--comparator-sha256" "$j" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --comparator-sha256 "$CS"
  # the notary refuses a lone --challenge-sha256 first (pin-pair rule), so its row also gives the config pin
  if [ "$l" = check-notary ]; then run "$l/malformed-pin" DECLINED "64 lowercase hex" "$j" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --challenge-sha256 "${CS^^}" --comparator-sha256 "$CF"
  else run "$l/malformed-pin" DECLINED "64 lowercase hex" "$j" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --challenge-sha256 "${CS^^}"; fi
  run "$l/empty-pin" DECLINED "non-empty" "$j" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --challenge-sha256 ""
}
if [ $# -gt 0 ]; then
  for j in "$@"; do judge "$(basename "$j" .sh)" "$j"; done
else
  judge check-sound "$F/sound/check-sound.sh"
  judge check-sound-svc "$F/sound/check-sound-svc.sh"
  judge check-notary "$F/notary/check-notary.sh"
  run "check-frontier/wrong-challenge-pin" DECLINED "--challenge-sha256" "$F/frontier/check-frontier.sh" "$S/good.export" "$S/challenge.export" "$S/comparator.json" --challenge-sha256 "$CF"
  run "check-frontier/sorryAx-permitted" DECLINED "" "$F/frontier/check-frontier.sh" "$S/challenge.export" "$S/challenge.export" "$W/ax-sorry.json"
fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
