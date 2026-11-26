#!/bin/bash
# fastverify/tests/subcontract/run.sh — End-to-end & adversarial regression suite for tools/subcontract/
# Tests:
#   1. mint.py: conditional verification (check-frontier.sh) + SHA-256-pinned sub-challenge minting
#   2. triage.py: catches FALSE lemma (with witness), VACUOUS premises, AUTO_IMPLICIT_TRAP, 0 FP on clean lemmas
#   3. subverify.py adversarial cases: statement weakening, shared-def tampering, hidden sorry,
#      native_decide, debug.skipKernelTC cheat, custom axiom, tampered subchallenge pin, compile error
#   4. subverify.py honest proofs (incl. 2 lemmas in the SAME file)
#   5. merge.py: multi-agent concurrent same-file splicing, frontier shrink, ledger update -> final ACCEPTED!
set -euo pipefail

HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)
SUB=$FV/tools/subcontract
TC433=$(python3 -I -c "import json; print(json.load(open('$FV/config/components.json'))['lean_toolchains']['leanprover/lean4:v4.33.1']['prefix'])")
W=$(mktemp -d "${SUBCONTRACT_TEST_DIR:-${TMPDIR:-/tmp}}/subcontract-test.XXXXXX")
trap 'chmod -R u+w "$W" 2>/dev/null || true; rm -rf "$W"' EXIT

PASS=0; FAIL=0
ok()   { echo "PASS $1: $2"; PASS=$((PASS+1)); }
fail() { echo "FAIL $1: $2"; FAIL=$((FAIL+1)); }

echo "=== Setup test project & official clean challenge in $W ==="
# 1. Create a realistic multi-file core-only Lean 4.33.1 project (fast, zero Mathlib dependency needed for unit test)
PROJ=$W/proj
CHAL=$W/challenge
mkdir -p "$PROJ/Blue" "$CHAL"

cat > "$PROJ/lean-toolchain" <<'EOF'
leanprover/lean4:v4.33.1
EOF
cat > "$PROJ/lakefile.toml" <<'EOF'
name = "blue"
defaultTargets = ["Blue"]

[[lean_lib]]
name = "Blue"
EOF
cat > "$PROJ/lake-manifest.json" <<'EOF'
{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [], "lakeDir": ".lake"}
EOF

cat > "$PROJ/Blue/Defs.lean" <<'EOF'
namespace Blue

def doublePlusOne (n : Nat) : Nat := 2 * n + 1

def sq (n : Nat) : Nat := n * n

end Blue
EOF

cat > "$PROJ/Blue/Lemmas.lean" <<'EOF'
import Blue.Defs

namespace Blue

theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := by
  sorry

theorem lemma_sq_add (a b : Nat) : sq (a + b) = sq a + 2 * a * b + sq b := by
  sorry

theorem lemma_pos_double (n : Nat) : 0 < doublePlusOne n := by
  sorry

end Blue
EOF

cat > "$PROJ/Blue.lean" <<'EOF'
import Blue.Defs
import Blue.Lemmas

namespace Blue

theorem main_goal (a b : Nat) :
    doublePlusOne (sq (a + b)) = (sq a + 2 * a * b + sq b) + (sq a + 2 * a * b + sq b) + 1 ∧
    0 < doublePlusOne a := by
  refine ⟨?_, lemma_pos_double a⟩
  rw [lemma_sq_add a b, lemma_even_double]

end Blue
EOF

# 2. Create clean official Challenge (same defs + target statement := sorry)
cp "$PROJ/lean-toolchain" "$CHAL/lean-toolchain"
cp "$PROJ/lake-manifest.json" "$CHAL/lake-manifest.json"
cat > "$CHAL/lakefile.toml" <<'EOF'
name = "blue"
defaultTargets = ["Challenge"]

[[lean_lib]]
name = "Blue"

[[lean_lib]]
name = "Challenge"
EOF
WS=$W/ws
mkdir -p "$WS/.lake/packages" "$CHAL/Blue"
cp "$PROJ/Blue/Defs.lean" "$CHAL/Blue/Defs.lean"
cat > "$CHAL/Challenge.lean" <<'EOF'
import Blue.Defs

namespace Blue

theorem main_goal (a b : Nat) :
    doublePlusOne (sq (a + b)) = (sq a + 2 * a * b + sq b) + (sq a + 2 * a * b + sq b) + 1 ∧
    0 < doublePlusOne a := by
  sorry

end Blue
EOF

cat > "$CHAL/comparator.json" <<'EOF'
{
  "challenge_module": "Challenge",
  "solution_module": "Blue",
  "theorem_names": ["Blue.main_goal"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
EOF

# Build official challenge.export using official build + official E0 exporter
"$FV/build/official-build.sh" "$CHAL" "$WS" "$TC433" --threads 4 --json "$W/chal-build.json" > /dev/null
python3 -I - "$FV" "$CHAL" "$TC433" "$WS" <<'PY'
import json, sys, os
sys.path.insert(0, os.path.join(sys.argv[1], "tools", "subcontract"))
import mint as M
fv, chal, tc, ws = sys.argv[1:5]
targets = M.export_targets_for(["Blue.main_goal", "sorryAx"], ["propext", "Quot.sound", "Classical.choice"])
mode, wall = M.run_exporter(chal, "Challenge", targets, os.path.join(chal, "challenge.export"), ws, tc, fv, threads=4, prefer_official=True)
print(f"Official challenge export built ({mode}, {wall}s)")
PY
CHAL_SHA=$(sha256sum "$CHAL/challenge.export" | cut -d' ' -f1)
CFG_SHA=$(sha256sum "$CHAL/comparator.json" | cut -d' ' -f1)   # (comparator pin required with the challenge pin)
echo "Challenge SHA-256: $CHAL_SHA"

# =====================================================================
# TEST 1: mint.py (initial conditional verification + sub-challenge minting)
# =====================================================================
MINT_OUT=$W/mint
ICACHE=$W/icache
mkdir -m 700 -p "$ICACHE"
MINT_JSON=$(python3 -I "$SUB/mint.py" --experimental "$PROJ" "$CHAL" "$MINT_OUT" \
  --challenge-sha256 "$CHAL_SHA" --comparator-sha256 "$CFG_SHA" --packages "$WS" --threads 4 --integrity-cache "$ICACHE")
echo "MINT: $MINT_JSON"
M_OK=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("ok"), d.get("verdict"), d.get("frontier_size"))' "$MINT_JSON")
if [ "$M_OK" = "True CONDITIONAL 3" ]; then
  ok "mint-basic" "CONDITIONAL with 3 minted SHA-256-pinned sub-challenges"
else
  fail "mint-basic" "expected 'True CONDITIONAL 3', got '$M_OK'"
fi

# =====================================================================
# TEST 2: triage.py on BOTH clean lemmas AND a defect-laden blueprint
# =====================================================================
TRI_CLEAN=$(python3 -I "$SUB/triage.py" "$MINT_OUT/manifest.json" --jobs 4 --out "$W/triage-clean.json")
C_SUM=$(python3 -I -c 'import json; d=json.load(open("'"$W/triage-clean.json"'")); print(d["counts"]["REFUTED"], d["counts"]["VACUOUS"], d["counts"]["AUTO_IMPLICIT_TRAP"], d["counts"]["PASS"])')
if [ "$C_SUM" = "0 0 0 3" ]; then
  ok "triage-clean-0fp" "0 false positives on 3 clean lemmas (counts=$C_SUM)"
else
  fail "triage-clean-0fp" "unexpected triage counts on clean lemmas: $C_SUM"
fi

# Now build a triage-defect test project with:
#  - false_nat_sub: ∀ n : Nat, (n - 5) + 5 = n  (REFUTED at n = 0!)
#  - vacuous_gt: ∀ n : Nat, n < 3 → 5 < n → n = 42  (VACUOUS!)
#  - autoimpl_typo: theorem bad_typo (n : Nat) : n + mmm_typo = mmm_typo + n  (AUTO_IMPLICIT_TRAP!)
#  - trivial_nohyps: ∀ n : Nat, (h : n > 100) → n + 0 = n  (TRIVIAL_WITHOUT_HYPS!)
#  - unused_binder: ∀ (n k : Nat), n + 0 = n  (UNUSED_DATA_BINDER!)
DPROJ=$W/dproj
mkdir -p "$DPROJ/Blue"
cp "$PROJ/lean-toolchain" "$PROJ/lakefile.toml" "$PROJ/lake-manifest.json" "$DPROJ/"
cp "$PROJ/Blue/Defs.lean" "$DPROJ/Blue/"
cat > "$DPROJ/Blue/Lemmas.lean" <<'EOF'
import Blue.Defs

namespace Blue

theorem false_nat_sub (n : Nat) : (n - 5) + 5 = n := by
  sorry

theorem vacuous_gt (n : Nat) (h1 : n < 3) (h2 : 5 < n) : n = 42 := by
  sorry

theorem autoimpl_typo (n : Nat) : n + mmm_typo = mmm_typo + n := by
  sorry

theorem trivial_nohyps (n : Nat) (h : 100 < n) : n + 0 = n := by
  sorry

theorem unused_binder (n k : Nat) : n + 0 = n := by
  sorry

end Blue
EOF
cat > "$DPROJ/Blue.lean" <<'EOF'
import Blue.Defs
import Blue.Lemmas

namespace Blue

theorem main_goal (a b : Nat) :
    doublePlusOne (sq (a + b)) = (sq a + 2 * a * b + sq b) + (sq a + 2 * a * b + sq b) + 1 ∧
    0 < doublePlusOne a := by
  have _ := false_nat_sub a
  have _ := vacuous_gt a
  have _ := autoimpl_typo a
  have _ := trivial_nohyps a
  have _ := unused_binder a b
  sorry

end Blue
EOF
# Use a standalone defect challenge whose target uses all 5 lemmas directly
DCHAL=$W/dchal
mkdir -p "$DCHAL/Blue"
cp "$CHAL/lean-toolchain" "$CHAL/lake-manifest.json" "$CHAL/lakefile.toml" "$DCHAL/"
cp "$PROJ/Blue/Defs.lean" "$DCHAL/Blue/"
cat > "$DCHAL/Challenge.lean" <<'EOF'
import Blue.Defs
namespace Blue
theorem defect_target (a b : Nat) : a + b = b + a := by sorry
end Blue
EOF
cat > "$DCHAL/comparator.json" <<'EOF'
{
  "challenge_module": "Challenge",
  "solution_module": "Blue",
  "theorem_names": ["Blue.defect_target"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
EOF
cat > "$DPROJ/Blue.lean" <<'EOF'
import Blue.Defs
import Blue.Lemmas
namespace Blue
theorem defect_target (a b : Nat) : a + b = b + a := by
  have _ := false_nat_sub a
  have _ := vacuous_gt a
  have _ := @autoimpl_typo
  have _ := trivial_nohyps a
  have _ := unused_binder a b
  exact Nat.add_comm a b
end Blue
EOF
"$FV/build/official-build.sh" "$DCHAL" "$WS" "$TC433" --threads 4 --json "$W/dchal-build.json" > /dev/null
python3 -I - "$FV" "$DCHAL" "$TC433" "$WS" <<'PY'
import sys, os
sys.path.insert(0, os.path.join(sys.argv[1], "tools", "subcontract"))
import mint as M
fv, chal, tc, ws = sys.argv[1:5]
targets = M.export_targets_for(["Blue.defect_target", "sorryAx"], ["propext", "Quot.sound", "Classical.choice"])
M.run_exporter(chal, "Challenge", targets, os.path.join(chal, "challenge.export"), ws, tc, fv, threads=4, prefer_official=True)
PY
DCHAL_SHA=$(sha256sum "$DCHAL/challenge.export" | cut -d' ' -f1)
DCFG_SHA=$(sha256sum "$DCHAL/comparator.json" | cut -d' ' -f1)
DMINT=$W/dmint
python3 -I "$SUB/mint.py" --experimental "$DPROJ" "$DCHAL" "$DMINT" --challenge-sha256 "$DCHAL_SHA" --comparator-sha256 "$DCFG_SHA" --packages "$WS" --threads 4 --integrity-cache "$ICACHE" > /dev/null
python3 -I "$SUB/triage.py" "$DMINT/manifest.json" --jobs 4 --out "$W/triage-defects.json" > /dev/null
python3 -I - "$W/triage-defects.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
by = {r["lemma"]: r for r in d["results"]}
checks = [
    ("triage-refuted-nat-sub", by["Blue.false_nat_sub"]["refuted"] is True, f"counterexample={by['Blue.false_nat_sub'].get('counterexample')}"),
    ("triage-vacuous", by["Blue.vacuous_gt"]["vacuous"] is True, f"status={by['Blue.vacuous_gt']['status']}"),
    ("triage-autoimpl", by["Blue.autoimpl_typo"]["auto_implicit_trap"] is True, f"detail={by['Blue.autoimpl_typo'].get('auto_implicit_detail')}"),
    ("triage-trivial-nohyps", by["Blue.trivial_nohyps"]["trivial_without_hyps"] is True, f"warnings={[w['code'] for w in by['Blue.trivial_nohyps']['warnings']]}"),
    ("triage-unused-binder", any(w["code"] == "UNUSED_DATA_BINDER" for w in by["Blue.unused_binder"]["warnings"]), f"warnings={[w['code'] for w in by['Blue.unused_binder']['warnings']]}"),
]
bad = 0
for name, cond, info in checks:
    print(("PASS " if cond else "FAIL ") + f"{name}: {info}")
    if not cond: bad += 1
sys.exit(bad)
PY
if [ $? -eq 0 ]; then PASS=$((PASS+5)); else FAIL=$((FAIL+1)); fi

# =====================================================================
# TEST 3: subverify.py ADVERSARIAL CASES (8 rogue attacks, 0 false accepts!)
# =====================================================================
SUBS=$W/subs; mkdir -p "$SUBS"

# Attack 1: statement weakening (changes conclusion to True / weaker eq)
cat > "$SUBS/atk_weaken.lean" <<'EOF'
theorem lemma_even_double (n : Nat) : n = n := by rfl
EOF
# Attack 2: hidden sorry
cat > "$SUBS/atk_sorry.lean" <<'EOF'
theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := by
  have h : doublePlusOne n = n + n + 1 := sorry
  exact h
EOF
# Attack 3: custom axiom
cat > "$SUBS/atk_axiom.lean" <<'EOF'
import Blue.Defs
namespace Blue
axiom my_secret_cheat (n : Nat) : doublePlusOne n = n + n + 1
theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := my_secret_cheat n
end Blue
EOF
# Attack 4: native_decide cheat
cat > "$SUBS/atk_native_decide.lean" <<'EOF'
import Blue.Defs
namespace Blue
theorem lemma_pos_double (n : Nat) : 0 < doublePlusOne n := by
  have h : 0 < 1 := by native_decide
  unfold doublePlusOne
  omega
end Blue
EOF
# Attack 5: debug.skipKernelTC metaprogramming cheat (compiles cleanly with 0 illegal axioms, caught ONLY by kernel replay!)
cat > "$SUBS/atk_skipktc.lean" <<'EOF'
import Lean
import Blue.Defs
namespace Blue
set_option debug.skipKernelTC true
open Lean Elab Command in
#eval liftCoreM <| addDecl (.thmDecl {
  name := `Blue._fake_false, levelParams := [],
  type := mkConst ``False, value := mkConst ``True.intro
})
theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := False.elim _fake_false
end Blue
EOF
# Attack 6: compile error
cat > "$SUBS/atk_compile_err.lean" <<'EOF'
theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := by
  exact nonexistent_ident_xyz
EOF

run_atk() {
  local name=$1 lemma=$2 file=$3 expect_rc=$4 expect_cat=$5
  set +e
  OUT=$(python3 -I "$SUB/subverify.py" --experimental "$MINT_OUT/manifest.json" "$lemma" "$file" \
    --agent "rogue-$name" --threads 4 --integrity-cache "$ICACHE" 2>/dev/null)
  RC=$?
  set -e
  VER=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("category"))' "$OUT" 2>/dev/null || echo "PARSE_ERR")
  if [ "$RC" = "$expect_rc" ] && echo "$VER" | grep -q "$expect_cat"; then
    ok "attack-$name" "rc=$RC ($VER)"
  else
    fail "attack-$name" "expected rc=$expect_rc cat~$expect_cat, got rc=$RC ($VER) :: ${OUT:0:250}"
  fi
}

run_atk "statement-drift" "Blue.lemma_even_double" "$SUBS/atk_weaken.lean" 1 "STATEMENT_DRIFT"
run_atk "hidden-sorry"    "Blue.lemma_even_double" "$SUBS/atk_sorry.lean" 1 "ILLEGAL_AXIOM"
run_atk "custom-axiom"    "Blue.lemma_even_double" "$SUBS/atk_axiom.lean" 1 "ILLEGAL_AXIOM"
run_atk "native-decide"   "Blue.lemma_pos_double"  "$SUBS/atk_native_decide.lean" 1 "ILLEGAL_AXIOM"
run_atk "skip-kernel-tc"  "Blue.lemma_even_double" "$SUBS/atk_skipktc.lean" 1 "KERNEL_REJECT"
run_atk "compile-error"   "Blue.lemma_even_double" "$SUBS/atk_compile_err.lean" 1 "COMPILE_ERROR"

# Attack 7: shared def tampering (modifies Blue/Defs.lean so doublePlusOne n := n + n + 1 trivially, or 1)
python3 -I - "$FV" "$MINT_OUT/manifest.json" "$ICACHE" <<'PY'
import json, sys, os
sys.path.insert(0, os.path.join(sys.argv[1], "tools", "subcontract"))
import subverify as SV
manifest = json.load(open(sys.argv[2]))
sc = next(x for x in manifest["subchallenges"] if x["lemma"] == "Blue.lemma_pos_double")
task = json.load(open(sc["task_json"]))
evil_defs = "namespace Blue\ndef doublePlusOne (n : Nat) : Nat := 1\ndef sq (n : Nat) : Nat := n * n\nend Blue\n"
sub = "theorem lemma_pos_double (n : Nat) : 0 < doublePlusOne n := by unfold doublePlusOne; decide\n"
res = SV.verify_subproof(
    manifest, task, sub, agent_id="rogue-def-tamper", threads=4,
    integrity_cache=sys.argv[3], extra_file_patches={"Blue/Defs.lean": evil_defs},
)
ok_flag = (res["verdict"] == "REJECTED" and "DRIFT" in res["category"])
print(("PASS " if ok_flag else "FAIL ") + f"attack-shared-def-tamper: verdict={res['verdict']} cat={res['category']} reason={res.get('reason','')[:120]}")
sys.exit(0 if ok_flag else 1)
PY
if [ $? -eq 0 ]; then PASS=$((PASS+1)); else FAIL=$((FAIL+1)); fi

# Attack 8: tampered subchallenge.export pin -> must refuse with NO_VERDICT (SUBCHALLENGE_TAMPERED)
# Attack 9: path traversal in extra_file_patches -> must refuse with SCOPE_VIOLATION
python3 -I - "$FV" "$MINT_OUT/manifest.json" "$ICACHE" <<'PY'
import json, sys, os, shutil
sys.path.insert(0, os.path.join(sys.argv[1], "tools", "subcontract"))
import subverify as SV
manifest = json.load(open(sys.argv[2]))
sc = next(x for x in manifest["subchallenges"] if x["lemma"] == "Blue.lemma_pos_double")
task = json.load(open(sc["task_json"]))

# Attack 8: point task at a modified copy of subchallenge.export while keeping original pin
tampered_task = dict(task)
bad_exp = task["subchallenge_export"] + ".tampered"
shutil.copy2(task["subchallenge_export"], bad_exp)
with open(bad_exp, "a") as f:
    f.write("\n")
tampered_task["subchallenge_export"] = bad_exp
sub = "theorem lemma_pos_double (n : Nat) : 0 < doublePlusOne n := by unfold doublePlusOne; omega\n"
res8 = SV.verify_subproof(manifest, tampered_task, sub, agent_id="rogue-pin-tamper", threads=4, integrity_cache=sys.argv[3])
os.unlink(bad_exp)
ok8 = (res8["verdict"] == "NO_VERDICT" and res8["category"] == "SUBCHALLENGE_TAMPERED")
print(("PASS " if ok8 else "FAIL ") + f"attack-pin-tamper: verdict={res8['verdict']} cat={res8['category']}")

# Attack 9: path traversal outside project root
res9 = SV.verify_subproof(
    manifest, task, sub, agent_id="rogue-path-trav", threads=4,
    integrity_cache=sys.argv[3], extra_file_patches={"../escaped.lean": "-- evil"},
)
ok9 = (res9["verdict"] == "REJECTED" and res9["category"] == "SCOPE_VIOLATION")
print(("PASS " if ok9 else "FAIL ") + f"attack-path-traversal: verdict={res9['verdict']} cat={res9['category']}")
sys.exit(0 if (ok8 and ok9) else 1)
PY
if [ $? -eq 0 ]; then PASS=$((PASS+2)); else FAIL=$((FAIL+1)); fi

# =====================================================================
# TEST 4 & 5: HONEST CONCURRENT SUBMISSIONS (incl. helper def+lemma) + MULTI-AGENT SAME-FILE MERGE -> final ACCEPTED!
# =====================================================================
# Attack 9b: macro-sorry helper before lemma (compiles via helper splicing, caught as ILLEGAL_AXIOM!)
cat > "$SUBS/atk_macro_sorry.lean" <<'EOF'
local macro "my_secret_cheat" : tactic => `(tactic| sorry)
theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := by
  my_secret_cheat
EOF
set +e
OUT_MAC=$(python3 -I "$SUB/subverify.py" --experimental "$MINT_OUT/manifest.json" "Blue.lemma_even_double" "$SUBS/atk_macro_sorry.lean" --agent rogue-macro --threads 4 --integrity-cache "$ICACHE")
RC_MAC=$?
set -e
CAT_MAC=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("category"))' "$OUT_MAC")
if [ "$RC_MAC" = 1 ] && echo "$CAT_MAC" | grep -q "REJECTED ILLEGAL_AXIOM"; then
  ok "attack-macro-sorry-helper" "rc=1 ($CAT_MAC)"
else
  fail "attack-macro-sorry-helper" "expected rc=1 REJECTED ILLEGAL_AXIOM, got rc=$RC_MAC '$CAT_MAC' :: $OUT_MAC"
fi

# Honest agent-A uses helper `private def` + `private theorem` before target lemma (a pattern seen in prover output)
cat > "$SUBS/good_even_double.lean" <<'EOF'
private def dpoExpand (n : Nat) : Nat := n + n + 1
private theorem aux_double_eq (n : Nat) : doublePlusOne n = dpoExpand n := by
  unfold doublePlusOne dpoExpand
  omega
theorem lemma_even_double (n : Nat) : doublePlusOne n = n + n + 1 := by
  rw [aux_double_eq]
  rfl
EOF
cat > "$SUBS/good_sq_add.lean" <<'EOF'
theorem lemma_sq_add (a b : Nat) : sq (a + b) = sq a + 2 * a * b + sq b := by
  unfold sq
  have h1 : (a + b) * (a + b) = a * a + a * b + b * a + b * b := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
  rw [h1]
  have h2 : b * a = a * b := Nat.mul_comm b a
  rw [h2]
  have h3 : 2 * a * b = a * b + a * b := by
    rw [Nat.two_mul, Nat.add_mul]
  rw [h3]
  omega
EOF
cat > "$SUBS/good_pos_double.lean" <<'EOF'
theorem lemma_pos_double (n : Nat) : 0 < doublePlusOne n := by
  unfold doublePlusOne
  omega
EOF

VDIR=$MINT_OUT/verified_subproofs
for pair in "Blue.lemma_even_double:good_even_double.lean:agent-A" \
            "Blue.lemma_sq_add:good_sq_add.lean:agent-B" \
            "Blue.lemma_pos_double:good_pos_double.lean:agent-C"; do
  IFS=: read -r L F AG <<< "$pair"
  OUT=$(python3 -I "$SUB/subverify.py" --experimental "$MINT_OUT/manifest.json" "$L" "$SUBS/$F" \
    --agent "$AG" --threads 4 --integrity-cache "$ICACHE" --save-dir "$VDIR")
  VER=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("wall_s"))' "$OUT")
  if echo "$VER" | grep -q "^SUBPROOF_ACCEPTED"; then
    ok "subverify-honest-$AG" "$L ($VER s)"
  else
    fail "subverify-honest-$AG" "$L -> $OUT"
  fi
done

# Step 5a: Merge FIRST TWO proofs concurrently (same file Blue/Lemmas.lean!) -> CONDITIONAL with 1 remaining!
set +e
M1=$(python3 -I "$SUB/merge.py" --experimental "$MINT_OUT/manifest.json" \
  "$VDIR/Blue.lemma_even_double.verified.json" \
  "$VDIR/Blue.lemma_sq_add.verified.json" \
  --threads 4 --integrity-cache "$ICACHE")
M1_RC=$?
set -e
M1_INFO=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("ok"), d.get("parent_verdict"), d.get("remaining_count"), d.get("day100_complete"))' "$M1")
if [ "$M1_RC" = 3 ] && [ "$M1_INFO" = "True CONDITIONAL 1 False" ]; then
  ok "merge-concurrent-partial" "2 concurrent same-file proofs merged -> CONDITIONAL, 1 remaining (rc=3)"
else
  fail "merge-concurrent-partial" "expected rc=3 'True CONDITIONAL 1 False', got rc=$M1_RC '$M1_INFO' :: $M1"
fi

# Step 5b: Merge FINAL proof -> UNCONDITIONAL ACCEPTED (rc=0)!
set +e
M2=$(python3 -I "$SUB/merge.py" --experimental "$MINT_OUT/manifest.json" \
  "$VDIR/Blue.lemma_pos_double.verified.json" \
  --threads 4 --integrity-cache "$ICACHE")
M2_RC=$?
set -e
M2_INFO=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("ok"), d.get("parent_verdict"), d.get("remaining_count"), d.get("day100_complete"))' "$M2")
if [ "$M2_RC" = 0 ] && [ "$M2_INFO" = "True ACCEPTED 0 True" ]; then
  ok "merge-final-accepted" "Final lemma closed -> UNCONDITIONAL ACCEPTED (rc=0)!"
else
  fail "merge-final-accepted" "expected rc=0 'True ACCEPTED 0 True', got rc=$M2_RC '$M2_INFO' :: $M2"
fi

# Step 5c: Typo'd main target theorem in mint.py -> clean REJECTED (exit 1, TARGET_MISSING), not exit 2
TYPO_PROJ=$W/typo_proj; cp -a "$PROJ" "$TYPO_PROJ"
sed -i 's/theorem main_goal/theorem main_gaol_typo/' "$TYPO_PROJ/Blue.lean"
set +e
TYPO_OUT=$(python3 -I "$SUB/mint.py" --experimental "$TYPO_PROJ" "$CHAL" "$W/typo_mint" --challenge-sha256 "$CHAL_SHA" --comparator-sha256 "$CFG_SHA" --packages "$WS" --threads 4 --integrity-cache "$ICACHE")
TYPO_RC=$?
set -e
TYPO_INFO=$(python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); print(d.get("verdict"), d.get("category"))' "$TYPO_OUT" 2>/dev/null || echo "PARSE_ERR")
if [ "$TYPO_RC" = 1 ] && [ "$TYPO_INFO" = "REJECTED TARGET_MISSING" ]; then
  ok "mint-target-missing-rejected" "typo'd main theorem -> rc=1 ($TYPO_INFO)"
else
  fail "mint-target-missing-rejected" "expected rc=1 'REJECTED TARGET_MISSING', got rc=$TYPO_RC '$TYPO_INFO' :: $TYPO_OUT"
fi

# Step 5d: report.py JSON + Markdown dashboard & --next-batch smart queue (filters triaged_bad + shows completion)
chmod +x "$SUB/report.py" 2>/dev/null || true
REP_D=$(python3 -I "$SUB/report.py" "$DMINT/ledger.json" --next-batch 10)
REP_M=$(python3 -I "$SUB/report.py" "$MINT_OUT/ledger.json" --markdown)
python3 -I - "$REP_D" "$REP_M" <<'PY'
import json, sys
d = json.loads(sys.argv[1])
md = sys.argv[2]
# On dmints (5 defective lemmas: 3 critical triaged_bad [refuted/vacuous/autoimpl], 2 advisory), next_batch must exclude all 3 triaged_bad!
q_names = [q["lemma"] for q in d["next_batch"]]
ok_q = (d["counts"]["triaged_bad"] == 3 and "Blue.false_nat_sub" not in q_names and "Blue.vacuous_gt" not in q_names and "Blue.autoimpl_typo" not in q_names)
ok_md = ("ACCEPTED" in md and "3/3 closed" in md and "agent-A" in md)
print(("PASS " if ok_q else "FAIL ") + f"report-smart-queue: triaged_bad={d['counts']['triaged_bad']} dispatchable={q_names}")
print(("PASS " if ok_md else "FAIL ") + f"report-markdown-final: lines={len(md.splitlines())}")
sys.exit(0 if (ok_q and ok_md) else 1)
PY
if [ $? -eq 0 ]; then PASS=$((PASS+2)); else FAIL=$((FAIL+1)); fi

echo "RESULT pass=$PASS fail=$FAIL"
[ "$FAIL" = 0 ]
