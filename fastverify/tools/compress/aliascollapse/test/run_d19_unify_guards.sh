#!/bin/bash
# Regression test for aliascollapse/collapse.py static G2 unify guards + --deny-unify:
# Builds a tiny core-Lean AI-FLT fixture with 3 S_X / Thm_X pairs:
#   1. S_RefSol / Thm_RefSol: proof references `solution` in a second lemma -> static guard demotes to `collapsed`
#   2. S_Cap / Thm_Cap: target short name `myHelper` appears inside proof body -> static guard demotes to `collapsed`
#   3. S_Clean / Thm_Clean: clean unify candidate -> unified unless listed in --deny-unify
# Verifies all produced trees elaborate cleanly in Lean 4.33.1 inside bwrap.
set -euo pipefail
H=$(cd "$(dirname "$0")/.." && pwd)
TC=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1
W=$(mktemp -d /tmp/d19-unify-guard.XXXXXX); trap 'rm -rf "$W"' EXIT

mkdir -p "$W/orig/P2M/Sol" "$W/orig/Theorems"
cat > "$W/orig/P2M/Tools.lean" <<'EOF'
macro "p2m_exact_reverting" t:term : tactic => `(tactic| exact $t _)
EOF

# 1. S_RefSol: extra lemma references `solution`
cat > "$W/orig/P2M/Sol/S_RefSol.lean" <<'EOF'
namespace P2MW.S_RefSol
theorem solution (n : Nat) : n = n := rfl
theorem after_sol (n : Nat) : n = n := solution n
end P2MW.S_RefSol
EOF
cat > "$W/orig/Theorems/Thm_RefSol.lean" <<'EOF'
import P2M.Tools
import P2M.Sol.S_RefSol
theorem RefSol (n : Nat) : n = n := by p2m_exact_reverting @P2MW.S_RefSol.solution
EOF

# 2. S_Cap: proof body calls helper `myHelper` which matches target short name `Foo.myHelper`
cat > "$W/orig/P2M/Sol/S_Cap.lean" <<'EOF'
namespace P2MW.S_Cap
private theorem myHelper (n : Nat) : n = n := rfl
theorem solution (n : Nat) : n = n := myHelper n
end P2MW.S_Cap
EOF
cat > "$W/orig/Theorems/Thm_Cap.lean" <<'EOF'
import P2M.Tools
import P2M.Sol.S_Cap
theorem Foo.myHelper (n : Nat) : n = n := by p2m_exact_reverting @P2MW.S_Cap.solution
EOF

# 3. S_Clean: clean unify candidate
cat > "$W/orig/P2M/Sol/S_Clean.lean" <<'EOF'
namespace P2MW.S_Clean
theorem solution (n : Nat) : n + 0 = n := Nat.add_zero n
end P2MW.S_Clean
EOF
cat > "$W/orig/Theorems/Thm_Clean.lean" <<'EOF'
import P2M.Tools
import P2M.Sol.S_Clean
theorem CleanNs.CleanThm (n : Nat) : n + 0 = n := by p2m_exact_reverting @P2MW.S_Clean.solution
EOF

# 4. S_PrivClash: M declares `private theorem _root_.PrivClash` matching card `theorem PrivClash` -> skipped (kept uncollapsed!)
cat > "$W/orig/P2M/Sol/S_PrivClash.lean" <<'EOF'
namespace P2MW.S_PrivClash
private theorem _root_.PrivClash (n : Nat) : n = n := rfl
theorem solution (n : Nat) : n = n := PrivClash n
end P2MW.S_PrivClash
EOF
cat > "$W/orig/Theorems/Thm_PrivClash.lean" <<'EOF'
import P2M.Tools
import P2M.Sol.S_PrivClash
theorem PrivClash (n : Nat) : n = n := by p2m_exact_reverting @P2MW.S_PrivClash.solution
EOF

cat > "$W/orig/Theorems/Thm_UseCleanNs.lean" <<'EOF'
import Theorems.Thm_Clean
open CleanNs
theorem useClean (n : Nat) : n + 0 = n := CleanThm n
EOF

# 5. S_Univ: card has explicit universe binder `.{u_1}` while M declares `universe u_1` -> demoted to `collapsed`!
cat > "$W/orig/P2M/Sol/S_Univ.lean" <<'EOF'
namespace P2MW.S_Univ
universe u_1
theorem solution (α : Type u_1) : ∀ a : α, a = a := fun _ => rfl
end P2MW.S_Univ
EOF
cat > "$W/orig/Theorems/Thm_Univ.lean" <<'EOF'
import P2M.Tools
import P2M.Sol.S_Univ
theorem UnivNs.UnivThm.{u_1} (α : Type u_1) : ∀ a : α, a = a := by p2m_exact_reverting @P2MW.S_Univ.solution
EOF

compile_tree() {
  local t=$1 o=$1.out; rm -rf "$o"; mkdir -p "$o"
  for m in P2M.Tools P2M.Sol.S_PrivClash Theorems.Thm_PrivClash Theorems.Thm_RefSol Theorems.Thm_Cap Theorems.Thm_Clean Theorems.Thm_UseCleanNs Theorems.Thm_Univ; do
    local f=${m//.//}
    mkdir -p "$o/$(dirname "$f")"
    env -i PATH=/usr/bin:/bin bwrap --ro-bind / / --tmpfs /tmp --bind "$t" "$t" --bind "$o" "$o" \
      --unshare-net --die-with-parent --chdir "$t" --dev /dev --proc /proc \
      --setenv LEAN_PATH "$o" "$TC/bin/lean" "$f.lean" -o "$o/$f.olean" > "$W/lean.log" 2>&1 \
      || { echo "FAIL lean on $m:"; cat "$W/lean.log"; exit 1; }
  done
}

# Run 1: static guards should demote S_RefSol & S_Cap to collapsed, unify S_Clean
python3 -I "$H/collapse.py" "$W/orig" "$W/out1" --pairs flt --unify --pairs-out "$W/p1.tsv" > "$W/s1.json"
grep -q $'^P2M.Sol.S_RefSol\tTheorems.Thm_RefSol\tcollapsed$' "$W/p1.tsv" || { cat "$W/p1.tsv"; echo "FAIL S_RefSol not demoted"; exit 1; }
grep -q $'^P2M.Sol.S_Cap\tTheorems.Thm_Cap\tcollapsed$' "$W/p1.tsv" || { cat "$W/p1.tsv"; echo "FAIL S_Cap not demoted"; exit 1; }
grep -q $'^P2M.Sol.S_Clean\tTheorems.Thm_Clean\tunified$' "$W/p1.tsv" || { cat "$W/p1.tsv"; echo "FAIL S_Clean not unified"; exit 1; }
[ -f "$W/out1/P2M/Sol/S_PrivClash.lean" ] || { echo "FAIL S_PrivClash should have been skipped (private-root-clash)"; exit 1; }
grep -q $'^P2M.Sol.S_Univ\tTheorems.Thm_Univ\tcollapsed$' "$W/p1.tsv" || { cat "$W/p1.tsv"; echo "FAIL S_Univ not demoted"; exit 1; }
grep -q 'private-root-clash' "$W/s1.json" || { cat "$W/s1.json"; echo "FAIL private-root-clash not reported"; exit 1; }
compile_tree "$W/out1"

# Run 2: --deny-unify P2M.Sol.S_Clean should demote S_Clean to collapsed too (keeping all 3 collapsed!)
echo "P2M.Sol.S_Clean" > "$W/deny_u.txt"
python3 -I "$H/collapse.py" "$W/orig" "$W/out2" --pairs flt --unify --deny-unify "$W/deny_u.txt" --pairs-out "$W/p2.tsv" > "$W/s2.json"
grep -q $'^P2M.Sol.S_Clean\tTheorems.Thm_Clean\tcollapsed$' "$W/p2.tsv" || { cat "$W/p2.tsv"; echo "FAIL --deny-unify ignored"; exit 1; }
compile_tree "$W/out2"

echo "PASS (aliascollapse D19 unify guards: ref-to-solution demoted, short-name capture demoted, --deny-unify respected, all trees elaborate)"
