universe u v w

structure Point (α : Type u) where
  x : α
  y : α
deriving Repr, DecidableEq, BEq

inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def Tree.size {α : Type u} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

mutual
inductive Ev : Nat → Prop
  | zero : Ev 0
  | succ : Od n → Ev (n+1)
inductive Od : Nat → Prop
  | succ : Ev n → Od (n+1)
end

inductive Rose (α : Type u) where
  | node : α → List (Rose α) → Rose α

def Rose.label {α : Type u} : Rose α → α
  | .node a _ => a

structure Wrap (α : Sort u) : Sort (max 1 u) where
  val : α

class Shape (α : Type u) where
  area : α → Nat

instance : Shape (Point Nat) := ⟨fun p => p.x * p.y⟩

def idu {α : Sort u} (a : α) : α := a
opaque secret : Nat
private def priv (n : Nat) : Nat := n + 1
def quotNat : Type := Quot (fun (a b : Nat) => a % 2 = b % 2)
def quotMk (n : Nat) : quotNat := Quot.mk _ n
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
termination_by m n => (m, n)
def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

theorem point_eta (p : Point Nat) : Point.mk p.x p.y = p := rfl
theorem tree_size_leaf : (Tree.leaf : Tree Nat).size = 0 := rfl
theorem tree_size_node : (Tree.node .leaf 3 .leaf : Tree Nat).size = 1 := rfl
theorem ev_two : Ev 2 := .succ (.succ .zero)
theorem nat_big : (2^64 : Nat) = 18446744073709551616 := by decide
theorem nat_huge : (123456789123456789123456789 * 987654321987654321 : Nat) = 121932631356500531469135800347203169112635269 := by decide
theorem str_len : "héllo ∀ 🎉\n\t\"q\"".length = 14 := by decide
theorem char_lit : 'λ'.toNat = 955 := rfl
theorem let_test : (let x := 3; x + x) = 6 := rfl
theorem classical_em (p : Prop) : p ∨ ¬p := Classical.em p
theorem funext_test (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h
theorem quot_test : quotMk 0 = quotMk 2 := Quot.sound rfl
theorem proj_test (p : Nat × Nat) : (p.1, p.2) = p := rfl
theorem idu_eq {α : Sort (imax u v)} (a : α) : idu a = a := rfl
theorem wrap_eta {α : Sort (max u (w+1))} (x : Wrap α) : Wrap.mk x.val = x := rfl
theorem opaque_test : secret = secret := rfl
theorem priv_test : priv 1 = 2 := rfl
theorem area_test : Shape.area (Point.mk 3 4 : Point Nat) = 12 := rfl
theorem rose_test : (Rose.node 1 [Rose.node 2 []]).label = 1 := rfl
theorem ack_test : ack 0 5 = 6 := let x : (fun (_ : Nat) => Nat) sorry := (0 : Nat); (fun (_ : Nat) => by simp [ack]) x
theorem sumTo_test : sumTo = sumTo := rfl
theorem point_deq : (Point.mk 1 2 == Point.mk 1 2) = true := by decide
theorem prop_ext_use (a b : Prop) (h : a ↔ b) : a = b := propext h

theorem umb : ((@point_eta = @point_eta) ∧ (@tree_size_leaf = @tree_size_leaf) ∧ (@tree_size_node = @tree_size_node) ∧ (@ev_two = @ev_two) ∧ (@nat_big = @nat_big) ∧ (@nat_huge = @nat_huge) ∧ (@str_len = @str_len) ∧ (@char_lit = @char_lit) ∧ (@let_test = @let_test) ∧ (@classical_em = @classical_em) ∧ (@funext_test = @funext_test) ∧ (@quot_test = @quot_test) ∧ (@proj_test = @proj_test) ∧ (@idu_eq.{0,0} = @idu_eq.{0,0}) ∧ (@wrap_eta.{0,0} = @wrap_eta.{0,0}) ∧ (@opaque_test = @opaque_test) ∧ (@priv_test = @priv_test) ∧ (@area_test = @area_test) ∧ (@rose_test = @rose_test) ∧ (@ack_test = @ack_test) ∧ (@sumTo_test = @sumTo_test) ∧ (@point_deq = @point_deq) ∧ (@prop_ext_use = @prop_ext_use)) → True := fun _ => trivial
