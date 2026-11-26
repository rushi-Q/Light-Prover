import Definitions.DefA
import P2M.Util
import P2M.Sol.S_B
attribute [-instance] instFooBool P2MW.S_B.instFooUnit
attribute [-simp] dB P2MW.S_B.helperB
theorem B (n : Nat) : dA (n + 0) = n + 1 := by p2m_exact_reverting @_root_.P2MW.S_B.solution
