-- The five challenge theorems, proved honestly.
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl

-- A harmless diagnostic print (e.g. a project that tests a parser's error messages), followed by a long report.
-- It is an INFO message; the file has no error and `lean` exits 0. (The report is long enough (> the stdio buffer) that
-- lean's output file shows the line while lean is still running, as any chatty module would.)
#eval IO.println ("expected parser output: Foo.lean:1:1: error: unexpected token\n" ++ String.ofList (List.replicate 100000 'x'))

-- Stand-in for the rest of a real module that keeps elaborating for a few seconds after the print.
#eval IO.sleep 5000
