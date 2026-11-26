import Sol.A
import Lean.LibrarySuggestions.Default
theorem t (n : Nat) : secretFn n = 3 * n + 1 := by grind +suggestions
