import T.A
import T.B
set_option maxHeartbeats 100000 in
theorem T.c : T.a = 1 := T.a_eq
set_option linter.unusedVariables false
theorem T.c2 (x : Nat) : True := trivial
set_option maxHeartbeats 400000 in
theorem T.c3 : T.a + 0 = 1 := T.b
