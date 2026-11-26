#!/usr/bin/env python3
"""mkbases.py OUTDIR: writes the V06 base projects (Init-only, Lean 4.33.1): OUTDIR/<name>/{challenge,solution}/.
Each base = a shared prelude (definitions, compared exactly by the comparator), theorem statements (challenge: `sorry`)
and proofs (solution). Features: user inductives (recursive, indexed, mutual, nested), structures, well-founded recursion,
quotients/funext/choice, Nat/String/Char literals and kernel GMP arithmetic, let, universe polymorphism, type classes."""
import json, os, sys
BASES = {}
BASES['ind'] = dict(prelude=r'''
namespace V06
universe u
inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
def Tree.size {α : Type u} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size
def Tree.mirror {α : Type u} : Tree α → Tree α
  | .leaf => .leaf
  | .node l x r => .node r.mirror x l.mirror
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n+1)
def Vec.toList {α : Type u} {n : Nat} : Vec α n → List α
  | .nil => []
  | .cons a v => a :: v.toList
mutual
inductive Ev : Nat → Prop
  | zero : Ev 0
  | succ {n : Nat} : Od n → Ev (n+1)
inductive Od : Nat → Prop
  | succ {n : Nat} : Ev n → Od (n+1)
end
inductive Rose (α : Type) where
  | node : α → List (Rose α) → Rose α
def Rose.label {α : Type} : Rose α → α
  | .node a _ => a
structure Point where
  x : Nat
  y : Nat
def Point.add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩
def ack : Nat → Nat → Nat
  | 0, n => n+1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
termination_by m n => (m, n)
end V06
''', thms=[
 ('V06.mirror_size', '∀ {α : Type} (t : V06.Tree α), t.mirror.size = t.size',
  'by\n  intro α t\n  induction t with\n  | leaf => rfl\n  | node l x r ihl ihr => simp only [V06.Tree.mirror, V06.Tree.size, ihl, ihr]; omega'),
 ('V06.vec_len', '∀ {α : Type} {n : Nat} (v : V06.Vec α n), v.toList.length = n',
  'by\n  intro α n v\n  induction v with\n  | nil => rfl\n  | cons a v ih => simp [V06.Vec.toList, ih]'),
 ('V06.ev_four', 'V06.Ev 4', 'V06.Ev.succ (V06.Od.succ (V06.Ev.succ (V06.Od.succ V06.Ev.zero)))'),
 ('V06.point_add_comm', '∀ p q : V06.Point, p.add q = q.add p',
  'by\n  intro p q\n  cases p; cases q\n  simp [V06.Point.add, Nat.add_comm]'),
 ('V06.ack_zero', '∀ n, V06.ack 0 n = n + 1', 'by intro n; simp [V06.ack]'),
 ('V06.rose_label', 'V06.Rose.label (V06.Rose.node 3 [V06.Rose.node 4 []]) = 3', 'rfl'),
])
BASES['quot'] = dict(prelude=r'''
namespace V06
def parity : Setoid Nat := ⟨fun a b => a % 2 = b % 2, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
def Z2 : Type := Quotient parity
def Z2.mk (n : Nat) : Z2 := Quotient.mk parity n
def Z2.isEven : Z2 → Bool := Quotient.lift (fun n => n % 2 == 0) (by intro a b h; show (a % 2 == 0) = (b % 2 == 0); rw [show a % 2 = b % 2 from h])
end V06
''', thms=[
 ('V06.z2_sound', 'V06.Z2.mk 1 = V06.Z2.mk 3', 'Quotient.sound (show 1 % 2 = 3 % 2 from rfl)'),
 ('V06.z2_even', 'V06.Z2.isEven (V06.Z2.mk 6) = true', 'rfl'),
 ('V06.funext_ex', '(fun n : Nat => n + 0) = (fun n => n)', 'funext fun _ => rfl'),
 ('V06.em_ex', '∀ p : Prop, p ∨ ¬p', 'fun p => Classical.em p'),
 ('V06.choice_ex', '∃ f : Nat → Nat, ∀ n, f n = n + 1', '⟨fun n => n + 1, fun _ => rfl⟩'),
 ('V06.propext_ex', '(True ∧ True) = True', 'propext ⟨fun h => h.1, fun h => ⟨h, h⟩⟩'),
])
BASES['lit'] = dict(prelude=r'''
namespace V06
def greeting : String := "hello, wörld ∀ 🎉"
def bigNat : Nat := 123456789012345678901234567890
end V06
''', thms=[
 ('V06.str_len', '"hello".length = 5', 'by decide'),
 ('V06.str_append', '"ab" ++ "cd" = "abcd"', 'by decide'),
 ('V06.greeting_ne', 'V06.greeting ≠ ""', 'by decide'),
 ('V06.char_ex', "'a'.toNat = 97", 'rfl'),
 ('V06.big_mul', '123456789 * 987654321 = 121932631112635269', 'by decide'),
 ('V06.pow_ex', '2 ^ 64 = 18446744073709551616', 'by decide'),
 ('V06.gcd_ex', 'Nat.gcd 12 18 = 6', 'by decide'),
 ('V06.big_ex', 'V06.bigNat % 1000 = 890', 'by decide'),
 ('V06.list_ex', '[1, 2, 3].reverse = [3, 2, 1]', 'by decide'),
 ('V06.let_ex', '(let x := 5; x + x) = 10', 'rfl'),
 ('V06.fin_ex', '((5 : Fin 8) + 4) = 1', 'by decide'),
 ('V06.omega_ex', '∀ a b : Nat, a < b → a + 1 ≤ b', 'by intro a b h; omega'),
 ('V06.simp_ex', '∀ xs : List Nat, (xs ++ []).length = xs.length', 'by intro xs; simp'),
])
BASES['univ'] = dict(prelude=r'''
namespace V06
universe u v w
def compose {α : Sort u} {β : Sort v} {γ : Sort w} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
structure Box (α : Type u) : Type u where
  val : α
class Magma (α : Type u) where
  op : α → α → α
instance : Magma Nat := ⟨Nat.add⟩
def twice {α : Type u} [Magma α] (a : α) : α := Magma.op a a
end V06
''', thms=[
 ('V06.compose_assoc', '∀ {α β γ δ : Type} (h : γ → δ) (g : β → γ) (f : α → β), V06.compose h (V06.compose g f) = V06.compose (V06.compose h g) f', 'fun _ _ _ => rfl'),
 ('V06.box_eta', '∀ {α : Type} (b : V06.Box α), V06.Box.mk b.val = b', 'fun _ => rfl'),
 ('V06.ulift_down', '(ULift.up.{3} (3 : Nat)).down = 3', 'rfl'),
 ('V06.twice_nat', 'V06.twice (21 : Nat) = 42', 'rfl'),
 ('V06.plift_ex', '∀ (p : Prop) (h : p), (PLift.up h).down = h', 'fun _ _ => rfl'),
 ('V06.sort_ex', '∀ (α : Sort 2) (a : α), V06.compose id id a = a', 'fun _ _ => rfl'),
])
BASES['hole'] = dict(prelude='', prelude_challenge=r'''
def V06.double : Nat → Nat := fun _ => sorry
''', prelude_solution=r'''
def V06.double : Nat → Nat := fun n => n + n
''', defs=['V06.double'], thms=[
 ('V06.double_two', 'V06.double 2 = 4', 'rfl'),
 ('V06.double_add', '∀ a b : Nat, V06.double (a + b) = V06.double a + V06.double b', 'by intro a b; simp only [V06.double]; omega'),
])

def write(out):
    for name, b in BASES.items():
        for side in ('challenge', 'solution'):
            d = os.path.join(out, name, side); os.makedirs(d, exist_ok=True)
            mod = 'Challenge' if side == 'challenge' else 'Solution'
            body = b['prelude'] + b.get('prelude_' + side, '') + '\n' + '\n'.join(
                f'theorem {n} : {s} :=\n  ' + ('sorry' if side == 'challenge' else p) + '\n' for n, s, p in b['thms'])
            open(os.path.join(d, mod + '.lean'), 'w').write(body)
            open(os.path.join(d, 'lean-toolchain'), 'w').write('leanprover/lean4:v4.33.1\n')
            open(os.path.join(d, 'lakefile.toml'), 'w').write(f'name = "v06{name}{side}"\ndefaultTargets = ["{mod}"]\n\n[[lean_lib]]\nname = "{mod}"\n')
            if side == 'challenge':
                json.dump({'challenge_module': 'Challenge', 'solution_module': 'Solution',
                           'theorem_names': [n for n, _, _ in b['thms']], 'definition_names': b.get('defs', []),
                           'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']},
                          open(os.path.join(d, 'comparator.json'), 'w'), indent=1)
if __name__ == '__main__':
    write(sys.argv[1])
