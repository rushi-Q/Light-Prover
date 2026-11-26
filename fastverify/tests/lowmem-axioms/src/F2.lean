theorem om (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
theorem om2 (x y : Int) (h1 : 2 * x + 3 * y = 7) (h2 : x - y = 1) : x = 2 := by omega
theorem simp1 (l : List Nat) : (l ++ []).length = l.length := by simp
theorem simp2 (l : List Nat) (f : Nat → Nat) : (l.map f).length = l.length := by simp
theorem bv1 : (5 : BitVec 8) + 3 = 8 := by decide
theorem int1 : (-3 : Int) * 4 = -12 := by decide
theorem fin1 : (3 : Fin 5) + 4 = 2 := by decide
theorem list1 : [3, 1, 2].reverse = [2, 1, 3] := by decide
theorem arr1 : #[1, 2, 3].size = 3 := by simp
theorem opt1 : (some 3).map (· + 1) = some 4 := rfl
theorem str1 : "abc" ++ "def" = "abcdef" := by decide
theorem char1 : 'a'.isLower = true := by decide
theorem uint1 : (255 : UInt8) + 1 = 0 := by decide
theorem nat_gcd : Nat.gcd 12 18 = 6 := by decide
theorem nat_log : Nat.log2 1024 = 10 := by decide
theorem exists1 : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩
theorem subtype1 : (⟨3, by decide⟩ : {n : Nat // n < 5}).val = 3 := rfl
theorem decide_and (p q : Prop) [Decidable p] [Decidable q] (hp : p) (hq : q) : decide (p ∧ q) = true := by simp [hp, hq]

theorem umb : ((@om = @om) ∧ (@om2 = @om2) ∧ (@simp1 = @simp1) ∧ (@simp2 = @simp2) ∧ (@bv1 = @bv1) ∧ (@int1 = @int1) ∧ (@fin1 = @fin1) ∧ (@list1 = @list1) ∧ (@arr1 = @arr1) ∧ (@opt1 = @opt1) ∧ (@str1 = @str1) ∧ (@char1 = @char1) ∧ (@uint1 = @uint1) ∧ (@nat_gcd = @nat_gcd) ∧ (@nat_log = @nat_log) ∧ (@exists1 = @exists1) ∧ (@subtype1 = @subtype1) ∧ (@decide_and = @decide_and)) → True := fun _ => trivial
