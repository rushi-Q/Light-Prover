#!/bin/bash
# Regression test suite for fastverify/tools/audit/ (expaudit + vacuity_probe.py + audit.py).
# Uses Init-only Lean 4 cases (no Mathlib workspace needed; runs in ~12s on any host).
# Every row prints 'PASS|FAIL <case>: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff fail=0.
set -u

HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKG=$(cd "$HERE/../.." && pwd)
AUDIT_PY="$PKG/tools/audit/audit.py"
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$PKG/config/components.json")
W=${1:-$(mktemp -d "${SCRATCH:-${TMPDIR:-/tmp}}/statement-audit-test.XXXXXX")}
mkdir -p "$W"

pass=0
fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }

check_json_has() {
  local jfile=$1 want_id=$2 label=$3
  if python3 -I -c 'import json,sys; ids=[f["id"] for f in json.load(open(sys.argv[1]))["findings"]]; sys.exit(0 if sys.argv[2] in ids else 1)' "$jfile" "$want_id" 2>/dev/null; then
    ok "$label" "detected $want_id"
  else
    local got
    got=$(python3 -I -c 'import json,sys; print([f["id"] for f in json.load(open(sys.argv[1]))["findings"]])' "$jfile" 2>/dev/null || echo "unparsable")
    ko "$label" "expected $want_id, got $got"
  fi
}

# 1. Clean Init-only challenge + reading-set extraction + --fail-on WARN exit 0
mkdir -p "$W/clean"
cat > "$W/clean/Challenge.lean" << 'EOF'
def isGoodPair (a b : Nat) : Prop := a > 1 ∧ b > 1 ∧ Nat.gcd a b = 1

theorem clean_target (N : Nat) (hN : N ≥ 10) :
    ∃ a b : Nat, a ≥ N ∧ b > a ∧ isGoodPair a b ∧ (a * b + 1) % 3 ≠ 5 := by sorry

theorem guarded_sub (p : Nat) (hp : p ≥ 2) :
    ∃ k : Nat, k > p ∧ (k + (p - 1)) > p := by sorry
EOF
cat > "$W/clean/comparator.json" << 'EOF'
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["clean_target", "guarded_sub"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
python3 -I "$AUDIT_PY" "$W/clean/Challenge.lean" --config "$W/clean/comparator.json" --toolchain "$TC" \
  --probe --reading-set "$W/clean/rs.lean" --json "$W/clean/out.json" --fail-on WARN >/dev/null 2>"$W/clean/err.log"
rc=$?
st=$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["status"], d["dynamic_probes"]["ran"], d["dynamic_probes"]["probed_targets"])' "$W/clean/out.json" 2>/dev/null || echo "ERR")
if [ "$rc" = 0 ] && [ "$st" = "CLEAN True 2" ] && grep -q "def isGoodPair" "$W/clean/rs.lean"; then
  ok "clean_challenge" "status=CLEAN, isGoodPair extracted in reading set, probes_ran=True (2/2), exit=0"
else
  ko "clean_challenge" "rc=$rc st='$st' err=$(tail -c 240 "$W/clean/err.log")"
fi

# 2. Vacuity, False Subgoal, Dead Hypothesis, AutoImplicit, Exists-Implication, Junk Arith, Anti-Gaming
mkdir -p "$W/flawed"
cat > "$W/flawed/FlawedSuite.lean" << 'EOF'
set_option autoImplicit true

-- Vacuity (syntactic + semantic linear system)
theorem t_vac_bounds (n : Nat) (h1 : 10 ≤ n) (h2 : n ≤ 4) : n = 7 := by sorry
theorem t_vac_linear (a b : Nat) (h1 : a + b = 5) (h2 : 2 * a + 2 * b = 12) : a = 99 := by sorry

-- False subgoal (fails at n >= 5)
theorem t_false_sub : ∀ n : Nat, n + 10 > 2 * n + 5 := by sorry

-- Dead hypothesis (conclusion holds without premise hbig)
theorem t_dead_hyp (n : Nat) (hbig : n > 999999) : n + 0 = n := by sorry

-- AutoImplicit Prop typo + unused statement parameter
theorem t_auto_prop : ¬ RiemannHypotheis := by sorry
theorem t_unused_param (unused_k : Nat) (n : Nat) (hn : n ≥ 2) : ∃ m : Nat, m > n ∧ m % 2 = 1 := by sorry

-- Exists-Implication trap
theorem t_exists_imp : ∃ n : Nat, n > 10 → n > 1000 := by sorry

-- Unguarded Nat.sub & truncating Nat.div in bound
theorem t_nat_sub (a b : Nat) : a - b + b = a := by sorry
theorem t_nat_underflow (n : Nat) : ∃ m : Nat, m > n + (2 - 5) := by sorry
theorem t_nat_div_bound (n : Nat) (hn : n ≥ 5) : ∃ m : Nat, m > n ∧ m / 3 ≥ 1 := by sorry

-- Holes (unparameterized & un-sorried)
def hole_const : Nat := sorry
def hole_concrete (n : Nat) : Nat := n + 1
theorem t_hole_unparam (n : Nat) (hn : n ≥ 3) : ∃ m : Nat, m > n ∧ m ≥ hole_const := by sorry
theorem t_hole_concrete (n : Nat) (hn : n ≥ 3) : ∃ m : Nat, m > hole_concrete n := by sorry

-- Anti-gaming: custom axiom, native_decide helper, sorry in custom def, opaque, empty inductive, uninstantiated class, notation hijack
axiom sneaky_ax : Nat → Prop
theorem t_ax (n : Nat) : sneaky_ax n → ∃ m : Nat, m > n := by sorry

theorem helper_nd : (12 + 30 = 42) := by native_decide
theorem t_nd (n : Nat) : ∃ m : Nat, m > n ∧ m > 0 ∧ (12 + 30 = 42) := by
  refine ⟨?_, ?_, ?_, helper_nd⟩
  all_goals sorry

def sneaky_def (n : Nat) : Nat := sorry
theorem t_sorry_def (n : Nat) : ∃ m : Nat, m > sneaky_def n := by sorry

opaque opaque_val : Nat := 0
theorem t_opaque (n : Nat) : ∃ m : Nat, m > n + opaque_val := by sorry

inductive EmptyWitness : Type
theorem t_empty_ind (w : EmptyWitness) : 0 = 1 := by sorry

class MagicClass (n : Nat) : Prop where
  impossible : n > n + 1
theorem t_uninst_class (n : Nat) [MagicClass n] : n = 0 := by sorry

section OpHijack
local infixl:65 (priority := high) " + " => Nat.mul
theorem t_op_hijack (a b : Nat) (ha : a > 2) (hb : b > 2) : a + b > a := by sorry
end OpHijack
EOF

cat > "$W/flawed/comparator.json" << 'EOF'
{
  "challenge_module": "FlawedSuite",
  "solution_module": "FlawedSuite",
  "theorem_names": [
    "t_vac_bounds", "t_vac_linear", "t_false_sub", "t_dead_hyp",
    "t_auto_prop", "t_unused_param", "t_exists_imp",
    "t_nat_sub", "t_nat_underflow", "t_nat_div_bound",
    "t_hole_unparam", "t_hole_concrete",
    "t_ax", "t_nd", "t_sorry_def", "t_opaque", "t_empty_ind", "t_uninst_class", "t_op_hijack"
  ],
  "definition_names": ["hole_const", "hole_concrete"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF

python3 -I "$AUDIT_PY" "$W/flawed/FlawedSuite.lean" --config "$W/flawed/comparator.json" --toolchain "$TC" \
  --probe --json "$W/flawed/out.json" --fail-on HIGH >/dev/null 2>"$W/flawed/err.log"
rc_flawed=$?
if [ "$rc_flawed" = 1 ]; then
  ok "fail_on_gate" "--fail-on HIGH returned exit=1 on flawed suite"
else
  ko "fail_on_gate" "expected exit=1, got $rc_flawed :: $(tail -c 240 "$W/flawed/err.log")"
fi

check_json_has "$W/flawed/out.json" "F07b_CONTRADICTORY_BOUNDS" "static/vacuity_bounds"
check_json_has "$W/flawed/out.json" "D01_CONTRADICTORY_PREMISES" "dynamic/vacuity_kernel_certified"
check_json_has "$W/flawed/out.json" "D03_FALSIFIABLE_STATEMENT" "dynamic/false_subgoal_counterexample"
check_json_has "$W/flawed/out.json" "D02a_PROVABLE_WITHOUT_HYPOTHESES" "dynamic/dead_hypothesis"
check_json_has "$W/flawed/out.json" "S01_AUTO_IMPLICIT_ENABLED" "source/auto_implicit_option"
check_json_has "$W/flawed/out.json" "F07c_AUTO_IMPLICIT_PROP" "static/auto_implicit_prop_typo"
check_json_has "$W/flawed/out.json" "F07d_UNUSED_STMT_PARAM" "static/unused_param"
check_json_has "$W/flawed/out.json" "F08_EXISTS_IMPLICATION" "static/exists_implication"
check_json_has "$W/flawed/out.json" "D02b_DEGENERATE_WITNESS_PROVABLE" "dynamic/degenerate_witness"
check_json_has "$W/flawed/out.json" "F10a_NAT_SUB_UNGUARDED" "static/nat_sub_unguarded"
check_json_has "$W/flawed/out.json" "F10a_NAT_SUB_UNDERFLOW" "static/nat_sub_underflow"
check_json_has "$W/flawed/out.json" "F10b_NAT_TRUNC_IN_BOUND" "static/nat_div_in_bound"
check_json_has "$W/flawed/out.json" "F05c_UNPARAMETERIZED_HOLE" "static/unparameterized_hole"
check_json_has "$W/flawed/out.json" "F05b_UNSORRIED_HOLE" "static/unsorried_hole"
check_json_has "$W/flawed/out.json" "F02_AXIOM_IN_STMT_CLOSURE" "static/custom_axiom_stmt"
check_json_has "$W/flawed/out.json" "F02b_AXIOM_IN_PROOF_CLOSURE" "static/native_decide_axiom_closure"
check_json_has "$W/flawed/out.json" "F03b_SORRY_IN_CUSTOM_DEF" "static/sorry_in_custom_def"
check_json_has "$W/flawed/out.json" "F04_OPAQUE_IN_STMT_CLOSURE" "static/opaque_in_stmt"
check_json_has "$W/flawed/out.json" "F09a_EMPTY_INDUCTIVE_PREMISE" "static/empty_inductive"
check_json_has "$W/flawed/out.json" "F09b_UNINSTANTIATED_CUSTOM_CLASS" "static/uninstantiated_class"
check_json_has "$W/flawed/out.json" "S02_OPERATOR_NOTATION_OVERRIDE" "source/notation_hijack"

# Verify semantic linear vacuity (`t_vac_linear`: a+b=5 and 2a+2b=12) specifically received D01
if python3 -I -c 'import json,sys; fs=json.load(open(sys.argv[1]))["findings"]; sys.exit(0 if any(f["id"]=="D01_CONTRADICTORY_PREMISES" and f["decl"]=="t_vac_linear" for f in fs) else 1)' "$W/flawed/out.json" 2>/dev/null; then
  ok "dynamic/semantic_linear_vacuity" "t_vac_linear (a+b=5, 2a+2b=12) certified D01_CONTRADICTORY_PREMISES"
else
  ko "dynamic/semantic_linear_vacuity" "t_vac_linear missed by D01"
fi

# ---------------------------------------------------------------------------
# 3. Post-Proof `--solution-mode` (`F11_ZERO_PROJECT_PROOF_SUPPORT`)
# ---------------------------------------------------------------------------
mkdir -p "$W/sol"
cat > "$W/sol/SolSuite.lean" << 'EOF'
theorem project_lemma (n : Nat) : n + 0 = n := Nat.add_zero n
theorem open_blueprint_step (n : Nat) : n + 1 > n := by sorry
theorem target_bypassing_project (n : Nat) : n ≥ 0 := Nat.zero_le n
theorem target_using_project (n : Nat) : (n + 0) + 0 = n :=
  Eq.trans (project_lemma (n + 0)) (project_lemma n)
EOF

python3 -I "$AUDIT_PY" "$W/sol/SolSuite.lean" --toolchain "$TC" --no-probe --solution-mode \
  --targets "open_blueprint_step,project_lemma,target_bypassing_project,target_using_project" \
  --json "$W/sol/out.json" >/dev/null 2>"$W/sol/err.log"

if python3 -I -c 'import json,sys; fs=json.load(open(sys.argv[1]))["findings"]; sys.exit(0 if any(f["id"]=="F11_ZERO_PROJECT_PROOF_SUPPORT" and f["decl"]=="target_bypassing_project" for f in fs) else 1)' "$W/sol/out.json" 2>/dev/null; then
  ok "static/solution_zero_project_proof_support" "target_bypassing_project flagged F11_ZERO_PROJECT_PROOF_SUPPORT"
else
  ko "static/solution_zero_project_proof_support" "target_bypassing_project missed F11 :: $(cat "$W/sol/err.log" 2>/dev/null)"
fi

if python3 -I -c 'import json,sys; fs=json.load(open(sys.argv[1]))["findings"]; sys.exit(0 if not any(f["id"]=="F11_ZERO_PROJECT_PROOF_SUPPORT" and f["decl"]=="target_using_project" for f in fs) else 1)' "$W/sol/out.json" 2>/dev/null; then
  ok "static/solution_multi_lemma_clean" "target_using_project (uses project_lemma) clean under --solution-mode"
else
  ko "static/solution_multi_lemma_clean" "false F11 on target_using_project"
fi

[ $# -eq 0 ] && rm -rf "$W"
echo "RESULT pass=$pass fail=$fail"
[ "$fail" -eq 0 ]
