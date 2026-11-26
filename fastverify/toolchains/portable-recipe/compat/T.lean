import Lean
open Lean Elab Command in
elab "#d21hello" : command => logInfo m!"hello {(2:Nat)^100}"
#d21hello
theorem d21_t : 2 + 2 = 4 := by decide
def d21_big : Nat := 3^200 % 1000000007
#eval d21_big
example : d21_big = 3^200 % 1000000007 := rfl
