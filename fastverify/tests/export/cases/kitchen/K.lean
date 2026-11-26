-- "kitchen sink" of valid constructs whose export must be byte-identical between E1 and E0
universe u v w

def strs : List String :=
  ["tab\there", "nul\x00byte", "quote\"back\\slash", "unicode αβγ ∀∃ 🎉", "astral 𝔸 \u00e9", "crlf\r\n", "del\x7f",
   "ctl\x01\x02\x1b\x1f", "", "long" ++ String.ofList (List.replicate 300 'z'), "«guillemets»", "slash/and:colon"]

def «weird name with spaces» : Nat := 1
namespace «x.y»
def «a+b» : Nat := 2
end «x.y»
def «你好» : Nat := 3
def nats : List Nat := [0, 1, 2^32 - 1, 2^32, 2^63, 2^64, 2^64 + 1, 2^200, 10^100]

inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree

mutual
  inductive Ev : Nat → Prop where
    | zero : Ev 0
    | succ : Od n → Ev (n + 1)
  inductive Od : Nat → Prop where
    | succ : Ev n → Od (n + 1)
end

structure P3 (α : Type u) where
  a : α
  b : Nat
  c : List α

class Pointed (α : Type u) where
  pt : α

instance : Pointed Nat := ⟨42⟩

def imaxy (α : Sort u) (β : Sort v) : Sort (imax u v) := α → β
def maxy (α : Type u) (β : Type v) : Type (max u v) := α × β
def lets (n : Nat) : Nat := let x := n + 1; have y := x * 2; y + x
def projs (p : P3 Nat) : Nat := p.b + p.a + (p.c.length)
def quots : Quot (fun (a b : Nat) => a % 2 = b % 2) := Quot.mk _ 3
def qlift : Nat := Quot.lift (fun (n : Nat) => n % 2) (fun _ _ h => h) quots

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

opaque opq : Nat
partial def loopy (n : Nat) : Nat := if n = 0 then 0 else loopy (n - 1)
unsafe def uns : Nat := 7
noncomputable def choice' : Nat := Classical.choice ⟨0⟩

theorem thm1 : ∀ n : Nat, n + 0 = n := fun _ => rfl
theorem thm2 (α : Type u) (x : α) : x = x := by simp
theorem thm3 : Ev 2 := .succ (.succ .zero)
axiom myAx : ∀ (α : Sort w), α → α

def treeSize : Tree → Nat
  | .leaf _ => 1
  | .node ts => 1 + (ts.attach.map fun ⟨t, _⟩ => treeSize t).sum
