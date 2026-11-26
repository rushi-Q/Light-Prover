#!/bin/bash
# test/run.sh — regression test of tools/compress/autoshorten. Needs a workspace with a built Mathlib (PROJ, default:
# $FV_PACKAGES or the clean challenge workspace $LIGHT_LEAN/verify/challenge) and bwrap. Checks: (1) TryAt finds the closable suffixes of test/T.lean (whole proof, nested
# block, two-goal tail, a proof that simp closes with a project simp lemma) and never touches the `def` with a tactic
# block; it reports the new project dependency (deps); (2) apply.py applies them and the edited module re-elaborates;
# (3) leaf mode skips blocks with structural steps; (4) a FORGED candidate (rfl claimed to close a goal it does not
# close) is reverted by apply.py's re-elaboration; (5) no closer may use the theorem being proved (a @[simp] theorem that
# simp could only prove from itself).
set -u
H=$(cd "$(dirname "$0")" && pwd); D=$(dirname "$H")
PROJ=${PROJ:-${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}}
B=${TEST_SCRATCH:-${FV_SCRATCH:-$H}}; [ -d "$B" ] || B=$H
W=$(mktemp -d "$B/autoshorten-test.XXXXXX"); trap 'rm -rf "$W"' EXIT
fail=0; ok() { echo "PASS $1"; }; ko() { echo "FAIL $1"; fail=1; }
echo T.lean > "$W/mods.txt"; printf 'rfl\nsimp\nsimp_all\nlinarith\ngrind\n' > "$W/lad.txt"
python3 -I "$D/autoshorten.py" --proj "$PROJ" --src "$H" --modules "$W/mods.txt" --out "$W/o1" --ladder "$W/lad.txt" \
  --mode greedy --jobs 1 --hb 20000 > "$W/o1.log" 2>&1
[ "$(wc -l < "$W/o1/edits.tsv")" = 5 ] && ok "five edits" || ko "five edits ($(wc -l < "$W/o1/edits.tsv"))"
grep -q '"applied": 5, "reverted": 0' "$W/o1/apply.jsonl" && ok "applied 5, reverted 0" || ko "apply summary: $(cat "$W/o1/apply.jsonl")"
grep '"ok":true' "$W/o1/try/res/1.jsonl" | grep -q '"deps":\["P06Test.p06pred_true' && ok "new project dependency reported" || ko "deps not reported"
grep -q "refine ?_" "$W/o1/tree/T.lean" && ok "def untouched" || ko "def touched"
grep '"decl":"P06Test.selfSimp","line":44,' "$W/o1/try/res/1.jsonl" | grep -q '"ok":true' && ko "a @[simp] theorem was 'proved' from itself (env after the command)" \
  || ok "no circular success (tries run in the environment before the command)"
grep -c "dataDef" "$W/o1/try/res/1.jsonl" | grep -q '^0$' && ok "no try inside the def" || ko "tries inside the def"
"$D/blean.sh" "$PROJ" "$W/o1/tree" T.lean > "$W/re.log" 2>&1 && ok "edited module elaborates" || ko "edited module: $(head -c 300 "$W/re.log")"
python3 -I "$D/autoshorten.py" --proj "$PROJ" --src "$H" --modules "$W/mods.txt" --out "$W/o2" --ladder "$W/lad.txt" \
  --mode greedy-leaf --jobs 1 --hb 20000 > "$W/o2.log" 2>&1
[ "$(wc -l < "$W/o2/edits.tsv")" = 3 ] && grep -q "^T	25	27	replace" "$W/o2/edits.tsv" && ok "leaf mode: no block with a have" \
  || ko "leaf mode: $(cat "$W/o2/edits.tsv")"
# forged candidate: claims `rfl` closes the whole proof of `whole` (lines 7-9)
head -1 "$W/o1/try/res/1.jsonl" | python3 -I -c "
import json,sys; r=json.loads(sys.stdin.read()); r.update(tac='rfl', tmpl='rfl', ok=True); print(json.dumps(r))" > "$W/forged.jsonl"
mkdir -p "$W/o3"; python3 -I "$D/apply.py" "$PROJ" T.lean "$H" "$W/forged.jsonl" "$W/o3" > "$W/o3.log" 2>&1
grep -q '"applied": 0, "reverted": 1' "$W/o3.log" && cmp -s "$W/o3/T.lean" "$H/T.lean" && ok "forged candidate reverted" \
  || ko "forged candidate: $(cat "$W/o3.log")"
[ $fail = 0 ] && echo "ALL PASS" || echo "SOME FAILED"
exit $fail
