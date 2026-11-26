namespace Tst

def sq (n : Nat) : Nat := n * n
def sq' (n : Nat) : Nat := n * n            -- identical definition under another name

structure P where
  a : Nat
  b : Nat
structure Q where                            -- identical structure under another name
  a : Nat
  b : Nat

def P.sum (p : P) : Nat := p.a + p.b
def Q.sum (q : Q) : Nat := q.a + q.b         -- identical modulo P ~ Q

theorem t1 (n : Nat) : sq n = n * n := rfl
theorem t2 (n : Nat) : sq n = n * n := by simp [sq]          -- same statement, other proof
theorem t3 (n : Nat) : sq' n = n * n := by unfold sq'; rfl   -- same statement modulo sq ~ sq'
theorem s1 (p : P) : p.sum = p.a + p.b := rfl
theorem s2 (q : Q) : q.sum = q.a + q.b := by simp [Q.sum]    -- same modulo P ~ Q

theorem u1 (n : Nat) : sq (n + 1) = (n + 1) * (n + 1) := t2 (n + 1)
theorem u2 (n : Nat) : sq' (n + 1) = (n + 1) * (n + 1) := t3 (n + 1)

end Tst

theorem main_thm : ∀ n : Nat, (n + 1) * (n + 1) = (n + 1) * (n + 1) := fun n =>
  ((Tst.u1 n).symm.trans (Tst.t1 (n + 1))).trans
    (((Tst.u2 n).symm.trans (Tst.t3 (n + 1))).symm.trans ((Tst.u2 n).symm.trans (Tst.t3 (n + 1))))

theorem main_thm2 : ∀ p : Tst.P, ∀ q : Tst.Q, p.sum + q.sum = (p.a + p.b) + (q.a + q.b) := fun p q => by
  rw [Tst.s1, Tst.s2]
