import Mathlib

namespace Imo1959P1
theorem imo1959_p1 : ∀ n : ℕ, Nat.Coprime (21 * n + 4) (14 * n + 3) := sorry
end Imo1959P1

namespace Imo1972P5
theorem imo1972_p5 (f g : ℝ → ℝ) (hf1 : ∀ x, ∀ y, f (x + y) + f (x - y) = 2 * f x * g y)
    (hf2 : BddAbove (Set.range fun x => ‖f x‖)) (hf3 : ∃ x, f x ≠ 0) (y : ℝ) : ‖g y‖ ≤ 1 := sorry
end Imo1972P5

namespace Imo2001P6
theorem imo2001_p6 {a b c d : ℤ} (hd : 0 < d) (hdc : d < c) (hcb : c < b) (hba : b < a)
    (h : a * c + b * d = (a + b - c + d) * (-a + b + c + d)) : ¬Prime (a * b + c * d) := sorry
end Imo2001P6

namespace Imo1966P4
theorem imo1966_p4 (n : ℕ) (x : ℝ)
    (hx : ∀ t : ℕ, ∀ k : ℤ, x ≠ k * Real.pi / 2^t) :
    ∑ i ∈ Finset.range n, 1 / Real.sin (2^(i + 1) * x) =
    Real.cot x - Real.cot (2^n * x) := sorry
end Imo1966P4

namespace Imo1963P5
open scoped Real
theorem imo1963_p5 :
    Real.cos (π/7) - Real.cos (2*π/7) + Real.cos (3*π/7) = 1/2 := sorry
end Imo1963P5

namespace Imo2013P1
theorem imo2013_p1 (n : ℕ+) (k : ℕ) :
    ∃ m : ℕ → ℕ+,
      (1 : ℚ) + (2 ^ k - 1) / n = ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := sorry
end Imo2013P1

namespace Imo2005P3
theorem imo2005_p3 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +
        (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥
      0 := sorry
end Imo2005P3

namespace Imo1969P1
open Int Nat
theorem imo1969_p1 : Set.Infinite {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)} := sorry
end Imo1969P1

namespace Imo2008P3
open Real
theorem imo2008_p3 : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt (2 * n) := sorry
end Imo2008P3

namespace Imo1964P2
theorem imo1964_p2
    (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (a b c : ℝ)
    (ha : a = dist (T.points 1) (T.points 2))
    (hb : b = dist (T.points 2) (T.points 0))
    (hc : c = dist (T.points 0) (T.points 1)) :
    a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤
    3 * a * b * c := sorry
end Imo1964P2
