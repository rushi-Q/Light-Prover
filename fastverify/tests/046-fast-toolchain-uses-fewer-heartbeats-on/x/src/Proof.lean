import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
-- an ordinary Mathlib-style proof (no metaprogramming); HB is substituted by repro.sh
set_option maxHeartbeats HB in
example (a b c : ℤ) : True := by
  have h1 : (a+b)^2 = a^2+2*a*b+b^2 := by ring
  have h2 : (a-b)^2 = a^2-2*a*b+b^2 := by ring
  have h3 : (a+b+c)^2 = a^2+b^2+c^2+2*a*b+2*b*c+2*a*c := by ring
  have h4 : (a+1)^3 = a^3+3*a^2+3*a+1 := by ring
  have h5 : a*b*c = c*b*a := by ring
  have h6 : (a+b)*(a-b) = a^2-b^2 := by ring
  have h7 : 0 ≤ a^2 + b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have h8 : a ≤ a + 1 := by linarith
  trivial
