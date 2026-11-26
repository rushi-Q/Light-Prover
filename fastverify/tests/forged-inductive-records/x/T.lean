inductive T : Type where
  | mk : T → T

theorem foo (x : T) : x = x := rfl
