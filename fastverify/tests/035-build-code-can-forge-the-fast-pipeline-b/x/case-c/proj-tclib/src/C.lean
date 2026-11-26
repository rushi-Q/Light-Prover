import A
import Lean.Data.EditDistance
-- refers to a declaration that the real core module does not have
theorem uses_core : Lean.EditDistance.forged = true := rfl
