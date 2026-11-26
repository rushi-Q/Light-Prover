#!/bin/bash
# test_sketch.sh — End-to-End & Adversarial Test Suite for Zero-Trust Inline Proof-Sketch Subcontracting
# (`check-frontier.sh` `have ... := by sorry` abstraction + `tools/subcontract/`).
#
# Verifies:
#   1. mint.py mints SHA-256-pinned standalone sub-challenges from the frontier's S' + Lean trace_state prompts
#   2. triage.py passes clean inline `have` subgoals (0 FP) AND refutes a FALSE inline `have` with a
#      machine-checked counterexample witness BEFORE spending any prover compute!
#   3. subverify.py blocks STATEMENT_DRIFT (weakened `have`), ILLEGAL_AXIOM, and comparator.json tampering
#   4. subverify.py accepts honest proofs of inline `_fv_sorry_1` and `_fv_sorry_2`
#   5. merge.py closes `_fv_sorry_1` -> CONDITIONAL (1 remaining, rc=3), then closes `_fv_sorry_2` -> final ACCEPTED (rc=0)!
set -euo pipefail

FV=${FV_ROOT:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}   # the tree this test is in
SUB=$FV/tools/subcontract
TC433=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1
W=$(mktemp -d "${SUBCONTRACT_TEST_DIR:-${TMPDIR:-/tmp}}/subcontract-sketch-test.XXXXXX")
trap 'rm -rf "$W"' EXIT

PASS=0; FAIL=0
ok()   { echo "PASS $1: $2"; PASS=$((PASS+1)); }
fail() { echo "FAIL $1: $2"; FAIL=$((FAIL+1)); }

ICACHE=$W/icache; mkdir -m 700 -p "$ICACHE"
WS=$W/ws; mkdir -p "$WS/.lake/packages"

# 1. Build clean official Challenge + 2-have-sorry inline proof sketch
PROJ=$W/proj; CHAL=$W/chal; mkdir -p "$PROJ/Sk" "$CHAL/Sk"
for d in "$PROJ" "$CHAL"; do
  printf 'leanprover/lean4:v4.33.1\n' > "$d/lean-toolchain"
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[]}\n' > "$d/lake-manifest.json"
done
cat > "$PROJ/lakefile.toml" <<'EOF'
name = "sk"
defaultTargets = ["Sk"]
[[lean_lib]]
name = "Sk"
EOF
cat > "$CHAL/lakefile.toml" <<'EOF'
name = "sk"
defaultTargets = ["Challenge"]
[[lean_lib]]
name = "Sk"
[[lean_lib]]
name = "Challenge"
EOF
cat > "$PROJ/Sk/Defs.lean" <<'EOF'
namespace Sk
def myBound : Nat := 10
end Sk
EOF
cp "$PROJ/Sk/Defs.lean" "$CHAL/Sk/Defs.lean"
cat > "$CHAL/Challenge.lean" <<'EOF'
import Sk.Defs
namespace Sk
theorem main_sketch : ∀ n : Nat, n < myBound → n * n < 100 := by
  sorry
end Sk
EOF
cat > "$PROJ/Sk.lean" <<'EOF'
import Sk.Defs
namespace Sk
theorem main_sketch : ∀ n : Nat, n < myBound → n * n < 100 := by
  intro n h
  have h1 : n ≤ 9 := by sorry
  have h2 : n * n ≤ 9 * 9 := by sorry
  omega
end Sk
EOF
cat > "$CHAL/comparator.json" <<'EOF'
{
  "challenge_module": "Challenge",
  "solution_module": "Sk",
  "theorem_names": ["Sk.main_sketch"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
EOF
"$FV/build/official-build.sh" "$CHAL" "$WS" "$TC433" --threads 4 --json "$W/chal-b.json" > /dev/null
python3 -I - "$FV" "$CHAL" "$TC433" "$WS" <<'PY'
import sys, os
sys.path.insert(0, os.path.join(sys.argv[1], "tools", "subcontract"))
import mint as M
fv, chal, tc, ws = sys.argv[1:5]
targs = M.export_targets_for(["Sk.main_sketch", "sorryAx"], ["propext", "Quot.sound", "Classical.choice"])
M.run_exporter(chal, "Challenge", targs, os.path.join(chal, "challenge.export"), ws, tc, fv, threads=4, prefer_official=True)
PY
CHAL_SHA=$(sha256sum "$CHAL/challenge.export" | cut -d' ' -f1)
COMP_SHA=$(sha256sum "$CHAL/comparator.json" | cut -d' ' -f1)   # mint requires the comparator pin

# TEST 1: mint.py on 2-have-sorry inline proof sketch
MOUT=$W/mint
MJSON=$(python3 -I "$SUB/mint.py" --experimental "$PROJ" "$CHAL" "$MOUT" --challenge-sha256 "$CHAL_SHA" --comparator-sha256 "$COMP_SHA" --packages "$WS" --threads 4 --integrity-cache "$ICACHE")
python3 -I - "$MOUT/manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
scs = m["subchallenges"]
assert m["base_verdict"] == "CONDITIONAL", m
assert len(scs) == 2, scs
assert all(sc.get("sketch_subgoal") is True for sc in scs), scs
assert all(sc.get("comparator_sha256") for sc in scs), scs
t1 = json.load(open(scs[0]["task_json"]))
assert "n ≤ 9" in (t1.get("statement_header") or ""), t1.get("statement_header")
print("OK", [sc["lemma"] for sc in scs], "| hdr1:", t1["statement_header"])
PY
if [ $? -eq 0 ]; then ok "sketch-mint" "2 inline have-sorry subgoals minted from S' with trace_state headers"; else fail "sketch-mint" "$MJSON"; fi

# TEST 2: triage.py on clean inline sketch subgoals -> 0 FP!
TJSON=$(python3 -I "$SUB/triage.py" "$MOUT/manifest.json" --jobs 4 --out "$W/triage-clean.json")
TINFO=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); c=d["counts"]; print(c["PASS"], c["REFUTED"], c["VACUOUS"], c["AUTO_IMPLICIT_TRAP"])' "$TJSON")
if [ "$TINFO" = "2 0 0 0" ]; then ok "sketch-triage-clean" "0 FP on 2 clean inline sketch subgoals"; else fail "sketch-triage-clean" "got $TINFO"; fi

# TEST 3: triage.py on FALSE inline `have h1 : n ≤ 8 := by sorry` -> REFUTED with witness n=9!
BADPROJ=$W/badproj; cp -a "$PROJ" "$BADPROJ"
sed -i 's/n ≤ 9/n ≤ 8/' "$BADPROJ/Sk.lean"
BADM=$W/badmint
python3 -I "$SUB/mint.py" --experimental "$BADPROJ" "$CHAL" "$BADM" --challenge-sha256 "$CHAL_SHA" --comparator-sha256 "$COMP_SHA" --packages "$WS" --threads 4 --integrity-cache "$ICACHE" > /dev/null
BTJSON=$(python3 -I "$SUB/triage.py" "$BADM/manifest.json" --jobs 4 --out "$W/triage-bad.json")
python3 -I - "$W/triage-bad.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
by = {r["lemma"]: r for r in d["results"]}
r1 = by["Sk.main_sketch._fv_sorry_1"]
# Note n < 10 -> n <= 8 is false at n=9! Check if direct refutation (`omega`) or witness caught it!
assert r1["refuted"] is True and r1["status"] == "REFUTED", r1
print("REFUTED:", r1["counterexample"])
PY
if [ $? -eq 0 ]; then ok "sketch-triage-false-have" "FALSE inline have (n ≤ 8 under n < 10) kernel-REFUTED before prover dispatch!"; else fail "sketch-triage-false-have" "$BTJSON"; fi

# TEST 4: Adversarial subverify on inline sketch subgoals (drift, axiom, comparator.json tamper)
SUBS=$W/subs; mkdir -p "$SUBS"
cat > "$SUBS/atk_drift.lean" <<'EOF'
theorem _root_.Sk.main_sketch._fv_sorry_1 (n : Nat) (h : n < myBound) : n ≤ 10 := by
  unfold myBound at h; omega
EOF
cat > "$SUBS/atk_axiom.lean" <<'EOF'
axiom my_sketch_cheat : ∀ n : Nat, n < myBound → n ≤ 9
theorem _root_.Sk.main_sketch._fv_sorry_1 (n : Nat) (h : n < myBound) : n ≤ 9 := my_sketch_cheat n h
EOF
for tc in "sketch-attack-drift:atk_drift.lean:STATEMENT_DRIFT" \
          "sketch-attack-axiom:atk_axiom.lean:ILLEGAL_AXIOM"; do
  IFS=: read -r NM FILE WANT <<< "$tc"
  set +e
  OUT=$(python3 -I "$SUB/subverify.py" --experimental "$MOUT/manifest.json" "Sk.main_sketch._fv_sorry_1" "$SUBS/$FILE" --agent rogue --threads 4 --integrity-cache "$ICACHE")
  RC=$?
  set -e
  GOT=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("category"))' "$OUT")
  if [ "$RC" = 1 ] && echo "$GOT" | grep -q "REJECTED $WANT"; then ok "$NM" "rc=1 ($GOT)"; else fail "$NM" "rc=$RC got='$GOT' :: $OUT"; fi
done

# Tamper test: tamper comparator.json by injecting "sorryAx" into permitted_axioms -> must be SUBCHALLENGE_TAMPERED (rc=2)!
TCOMP=$(python3 -I -c 'import json,sys; m=json.load(open(sys.argv[1])); print(json.load(open(m["subchallenges"][0]["task_json"]))["comparator_json"])' "$MOUT/manifest.json")
cp "$TCOMP" "$TCOMP.bak"
python3 -I -c 'import json,sys; p=sys.argv[1]; d=json.load(open(p)); d["permitted_axioms"].append("sorryAx"); json.dump(d, open(p,"w"))' "$TCOMP"
set +e
OUT_TC=$(python3 -I "$SUB/subverify.py" --experimental "$MOUT/manifest.json" "Sk.main_sketch._fv_sorry_1" "$SUBS/atk_axiom.lean" --agent rogue --threads 4 --integrity-cache "$ICACHE")
RC_TC=$?
set -e
mv "$TCOMP.bak" "$TCOMP"
GOT_TC=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("category"))' "$OUT_TC")
if [ "$RC_TC" = 2 ] && [ "$GOT_TC" = "NO_VERDICT SUBCHALLENGE_TAMPERED" ]; then
  ok "sketch-attack-comp-tamper" "comparator.json tamper blocked: rc=2 ($GOT_TC)"
else
  fail "sketch-attack-comp-tamper" "expected rc=2 SUBCHALLENGE_TAMPERED, got rc=$RC_TC '$GOT_TC'"
fi

# TEST 5: Honest isolated proofs of BOTH inline sketch subgoals -> SUBPROOF_ACCEPTED!
cat > "$SUBS/good_1.lean" <<'EOF'
theorem _root_.Sk.main_sketch._fv_sorry_1 (n : Nat) (h : n < myBound) : n ≤ 9 := by
  unfold myBound at h
  omega
EOF
cat > "$SUBS/good_2.lean" <<'EOF'
theorem _root_.Sk.main_sketch._fv_sorry_2 (n : Nat) (h : n < myBound) (h1 : n ≤ 9) : n * n ≤ 9 * 9 := by
  exact Nat.mul_le_mul h1 h1
EOF
VDIR=$MOUT/verified_subproofs
for pair in "Sk.main_sketch._fv_sorry_1:good_1.lean:agent-S1" \
            "Sk.main_sketch._fv_sorry_2:good_2.lean:agent-S2"; do
  IFS=: read -r L F AG <<< "$pair"
  OUT=$(python3 -I "$SUB/subverify.py" --experimental "$MOUT/manifest.json" "$L" "$SUBS/$F" --agent "$AG" --threads 4 --integrity-cache "$ICACHE" --save-dir "$VDIR")
  VER=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("wall_s"))' "$OUT")
  if echo "$VER" | grep -q "^SUBPROOF_ACCEPTED"; then ok "sketch-subverify-$AG" "$L ($VER s)"; else fail "sketch-subverify-$AG" "$OUT"; fi
done

# TEST 6: Incremental merge! First close ONLY _fv_sorry_1 -> CONDITIONAL (1 remaining, rc=3), THEN close _fv_sorry_2 -> final ACCEPTED (rc=0)!
set +e
M1=$(python3 -I "$SUB/merge.py" --experimental "$MOUT/manifest.json" "$VDIR/Sk.main_sketch._fv_sorry_1.verified.json" --threads 4 --integrity-cache "$ICACHE")
M1_RC=$?
set -e
M1_I=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("ok"), d.get("parent_verdict"), d.get("remaining_count"))' "$M1")
if [ "$M1_RC" = 3 ] && [ "$M1_I" = "True CONDITIONAL 1" ]; then
  ok "sketch-merge-partial" "closed inline _fv_sorry_1 -> CONDITIONAL (1 remaining, rc=3)"
else
  fail "sketch-merge-partial" "expected rc=3 'True CONDITIONAL 1', got rc=$M1_RC '$M1_I' :: $M1"
fi

set +e
M2=$(python3 -I "$SUB/merge.py" --experimental "$MOUT/manifest.json" "$VDIR/Sk.main_sketch._fv_sorry_2.verified.json" --threads 4 --integrity-cache "$ICACHE")
M2_RC=$?
set -e
M2_I=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("ok"), d.get("parent_verdict"), d.get("remaining_count"), d.get("day100_complete"))' "$M2")
if [ "$M2_RC" = 0 ] && [ "$M2_I" = "True ACCEPTED 0 True" ]; then
  ok "sketch-merge-final" "closed inline _fv_sorry_2 -> UNCONDITIONAL ACCEPTED (rc=0)!"
else
  fail "sketch-merge-final" "expected rc=0 'True ACCEPTED 0 True', got rc=$M2_RC '$M2_I' :: $M2"
fi

echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" = 0 ]
