#!/bin/bash
# regression test for edits_v2.py: index -> v2 list -> resolve -> apply_edits.py on base A, then the SAME v2 list on a
# shifted / edited / relocated base B (resolves by name; refuses changed declarations).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
TOOL=$HERE/../edits_v2.py
APPLY=$HERE/../apply_edits.py
T=$(mktemp -d /tmp/ev2test.XXXXXX); [ -n "${KEEP:-}" ] || trap 'rm -rf "$T"' EXIT; echo "tmp=$T"
pass=0; fail=0
ok() { if eval "$2"; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL: $1"; fi; }

mkdir -p "$T/A/src/Foo"
cat > "$T/A/src/Foo/Bar.lean" <<'EOF'
import Mathlib.Tactic

/-! Old module doc. -/

namespace Foo

/-- Old doc of one_add. -/
@[simp] theorem one_add (n : Nat) : 1 + n = n + 1 := by
  omega

-- a comment above two_add
theorem two_add (n : Nat) :
    2 + n = n + 2 := by
  omega

section
variable (m : Nat)
private theorem helper : m = m := rfl
end

mutual
def isEven : Nat → Bool
  | 0 => true
  | n+1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n+1 => isEven n
end

theorem uses_one_add (n : Nat) : 1 + n = n + 1 := one_add n

set_option maxHeartbeats 400000 in
theorem slow_one : True := trivial

instance : Inhabited Nat := ⟨0⟩

theorem _root_.rootThm : True := trivial

end Foo
EOF
cat > "$T/A/src/Foo/Baz.lean" <<'EOF'
import Foo.Bar

theorem baz : True := trivial
EOF

python3 -I "$TOOL" index "$T/A" > "$T/idx.tsv"
ok "index lists 9 named declarations" '[ "$(wc -l < "$T/idx.tsv")" -eq 9 ]'
ok "namespace after mutual/end is Foo" 'grep -q "^Foo.Bar	Foo.uses_one_add	" "$T/idx.tsv"'
ok "_root_ declaration is root-level" 'grep -q "^Foo.Bar	rootThm	" "$T/idx.tsv"'
ok "anonymous instance not indexed" '! grep -q "instInhabited" "$T/idx.tsv"'
ok "private decl in section indexed" 'grep -q "	Foo.helper	" "$T/idx.tsv"'
h() { awk -F'\t' -v d="$1" '$2==d{print $5}' "$T/idx.tsv"; }
hp() { awk -F'\t' -v d="$1" '$2==d{print $7}' "$T/idx.tsv"; }
MD=$(python3 -I -c "import hashlib,sys;print(hashlib.sha256(b'/-! Old module doc. -/').hexdigest())")
{
printf 'Foo.Bar\tFoo.one_add\t%s\tdoc\tDOCS.spine\tOne plus n commutes.\n' "$(h Foo.one_add)"
printf 'Foo.Bar\tFoo.two_add\t%s\tdoc\tDOCS.spine\tTwo plus n.\\nSecond line.\n' "$(h Foo.two_add)"
printf 'Foo.Bar\tFoo.two_add\t%s\treplace\tSTMTFMT\ttheorem two_add (n : Nat) : 2 + n = n + 2 := by\\n  omega\n' "$(h Foo.two_add)"
printf 'Foo.Bar\tFoo.isOdd\t%s\treplace\tSTMTFMT.bad\t/-- sneaky -/\\ndef isOdd : Nat → Bool\n' "$(h Foo.isOdd)"
printf 'Foo.Bar\tFoo.slow_one\t%s\tdocstring\tDOCS.spine\tSlow but true.\n' "$(hp Foo.slow_one)"
printf 'Foo.Bar\tFoo.helper\t%s\tdelete\tPRUNE.text\t\n' "$(h Foo.helper)"
printf 'Foo.Bar\tFoo.uses_one_add\t%s\trename\tRENAME.x\tuses_one_add usesOneAdd\n' "$(h Foo.uses_one_add)"
printf 'Foo.Bar\t-\t%s\tmoddoc\tDOCS.mod\t# Foo.Bar\\nAddition facts.\n' "$MD"
printf 'Foo.Baz\t-\t-\tmoddoc\tDOCS.mod\tBaz module.\n'
printf 'Foo.Baz\tbaz\t%s\tinsert_after\tDOCS.x\t\\nexample : baz = baz := rfl\n' "$(h baz)"
printf 'Foo.Bar\tFoo.one_add\t%s\tdoc\tDOCS.bad\tbad -/ payload\n' "$(h Foo.one_add)"
printf 'Foo.Bar\tFoo.nope\t%s\tdoc\tDOCS.spine\tx\n' "$(h Foo.one_add)"
printf 'Foo.Bar\tFoo.isOdd\t%s\tdoc\tDOCS.ind\t  /-- Odd. -/\n' "$(h Foo.isOdd)"
printf 'Foo.Bar\tFoo.isEven\t%s\trename\tRENAME.x\tisOdd isOddd\n' "$(h Foo.isEven)"
} > "$T/v2.tsv"
python3 -I "$TOOL" resolve "$T/A" "$T/v2.tsv" --out "$T/v1A.tsv" --refused "$T/refA.tsv" 2> "$T/sumA.json"
ok "A: 10 resolved (incl. an indented full /-- -/ payload)" '[ "$(wc -l < "$T/v1A.tsv")" -eq 10 ] && grep -q "DOCS.ind" "$T/v1A.tsv"'
ok "A: replace adding a docstring refused" 'grep -q "STMTFMT.bad.*BAD_PAYLOAD$" "$T/refA.tsv"'
ok "A: BAD_PAYLOAD refused" 'grep -q "DOCS.bad.*BAD_PAYLOAD$" "$T/refA.tsv"'
ok "A: DECL_MISSING refused" 'grep -q "Foo.nope.*DECL_MISSING$" "$T/refA.tsv"'
ok "A: RENAME_MISMATCH refused" 'grep -q "RENAME_MISMATCH$" "$T/refA.tsv"'
python3 -I "$APPLY" "$T/A" "$T/outA" "$T/v1A.tsv" --priority PRUNE.text,DOCS.spine,STMTFMT,RENAME.x,DOCS.mod,DOCS.x --copy > /dev/null
F=$T/outA/src/Foo/Bar.lean
ok "A: doc replaced" 'grep -q "^/-- One plus n commutes. -/$" "$F" && ! grep -q "Old doc" "$F"'
ok "A: attribute kept after doc" 'grep -A1 "One plus n commutes" "$F" | grep -q "^@\[simp\] theorem one_add"'
ok "A: multi-line doc inserted for two_add (DOCS before STMTFMT in priority)" 'grep -q "^/-- Two plus n.$" "$F" && grep -q "^Second line.$" "$F"'
ok "A: doc and STMTFMT compose (doc above the reformatted statement)" '[ "$(grep -A2 "^Second line.$" "$F" | tail -n 1)" = "theorem two_add (n : Nat) : 2 + n = n + 2 := by" ] && [ ! -s "$T/outA/.apply-conflicts.tsv" ]'
ok "A: docstring goes after set_option ... in (proper-span hash)" '[ "$(grep -B1 -A1 "^/-- Slow but true. -/$" "$F" | tr "\n" "|")" = "set_option maxHeartbeats 400000 in|/-- Slow but true. -/|theorem slow_one : True := trivial|" ]'
ok "A: comment above two_add kept by doc insert" 'grep -q "^-- a comment above two_add$" "$F"'
ok "A: helper deleted" '! grep -q "helper" "$F"'
ok "A: rename applied in module" 'grep -q "theorem usesOneAdd" "$F" && ! grep -q "uses_one_add" "$F"'
ok "A: module doc replaced" 'grep -q "^# Foo.Bar$" "$F" && ! grep -q "Old module doc" "$F"'
ok "A: module doc inserted after imports" '[ "$(sed -n 2,4p "$T/outA/src/Foo/Baz.lean" | tr "\n" "|")" = "/-!|Baz module.|-/|" ]'
ok "A: insert_after" 'tail -n 1 "$T/outA/src/Foo/Baz.lean" | grep -q "^example : baz = baz := rfl$"'

# base B: lines shifted, one_add's doc changed upstream (-> refused), two_add moved to another module (-> relocate)
mkdir -p "$T/B/src/Foo"
{ echo "-- upstream header line 1"; echo "-- upstream header line 2"; cat "$T/A/src/Foo/Bar.lean"; } \
  | sed 's/Old doc of one_add./Upstream doc of one_add./' \
  | python3 -I -c "
import sys; t=sys.stdin.read(); a=t.index('-- a comment above two_add'); b=t.index('section')
open('$T/two.txt','w').write(t[a:b]); sys.stdout.write(t[:a]+t[b:])" > "$T/B/src/Foo/Bar.lean"
{ printf 'import Foo.Bar\n\nnamespace Foo\n\n'; sed 1d "$T/two.txt"; printf 'end Foo\n'; } > "$T/B/src/Foo/Moved.lean"
cp "$T/A/src/Foo/Baz.lean" "$T/B/src/Foo/Baz.lean"
python3 -I "$TOOL" resolve "$T/B" "$T/v2.tsv" --out "$T/v1B.tsv" --refused "$T/refB.tsv" 2> "$T/sumB.json"
ok "B: changed one_add refused (HASH_MISMATCH)" 'grep -q "^Foo.Bar	Foo.one_add	.*DOCS.spine.*HASH_MISMATCH$" "$T/refB.tsv"'
ok "B: moved two_add refused without --relocate" 'grep -q "Foo.two_add.*DECL_MISSING$" "$T/refB.tsv"'
ok "B: shifted helper resolved at shifted lines" 'grep -q "^Foo.Bar	1[0-9]	1[0-9]	delete	PRUNE.text" "$T/v1B.tsv"'
printf 'Foo.Bar\tFoo.slow_one\t%s\tdelete\tPRUNE.text\t\n' "$(hp Foo.slow_one)" > "$T/v2del.tsv"
python3 -I "$TOOL" resolve "$T/B" "$T/v2del.tsv" --out "$T/v1Bd.tsv" 2>/dev/null
python3 -I "$APPLY" "$T/B" "$T/outBd" "$T/v1Bd.tsv" --copy > /dev/null
ok "B: delete via proper hash removes the set_option prefix too" '! grep -q "maxHeartbeats\\|slow_one" "$T/outBd/src/Foo/Bar.lean"'
python3 -I "$TOOL" resolve "$T/B" "$T/v2.tsv" --out "$T/v1Br.tsv" --refused "$T/refBr.tsv" --relocate 2> "$T/sumBr.json"
ok "B --relocate: two_add found in Foo.Moved" 'grep -q "^Foo.Moved	.*DOCS.spine" "$T/v1Br.tsv"'
ok "B --relocate: summary counts 2 relocations" 'grep -q "\"relocated\": 2" "$T/sumBr.json"'
python3 -I "$APPLY" "$T/B" "$T/outB" "$T/v1Br.tsv" --copy > /dev/null
ok "B: apply ok, helper gone, rename applied" '! grep -q helper "$T/outB/src/Foo/Bar.lean" && grep -q usesOneAdd "$T/outB/src/Foo/Bar.lean"'
echo "edits_v2 test: pass=$pass fail=$fail"
[ $fail -eq 0 ]
