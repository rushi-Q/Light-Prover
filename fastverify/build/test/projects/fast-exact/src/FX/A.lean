-- fast-exact test module (build/test/run.sh): every form the plugin handles or declines
structure S where
  x : Nat
  y : Nat

def T := S
def U (n : Nat) := n + 0

-- inner fast path: kernel confirms S =?= T
def mkT (s : S) : T := by with_unfolding_all exact (s :)

-- outer + inner fast path: (n = 3) =?= (U n = 3) needs unfolding U and Nat.add
theorem tU (n : Nat) (h : n = 3) : U n = 3 := by
  exact (by with_unfolding_all exact (h :))

-- kernel says no (Nat vs Int) -> official tactic -> coercion inserted
def toInt (n : Nat) : Int := by with_unfolding_all exact (n :)

-- value with metavariables -> official tactic
theorem tmv (n : Nat) : U n = n := by with_unfolding_all exact (rfl :)

-- ascription with a type
def mkT2 (s : S) : T := by with_unfolding_all exact (s : S)

-- hygienic names created AFTER a fast decision in the same declaration (the matcher of the anonymous-constructor
-- lambda has macro-scoped binder names): the plugin must allocate exactly the official macro scopes, else these names
-- (and the .olean, and the export) differ (v12 did: 5 scopes fewer per fast decision)
def mkPair (s : S) : T × (Nat × Nat → Nat) := by
  refine (?_, ?_)
  · with_unfolding_all exact (s :)
  · exact fun ⟨a, b⟩ => a + b
