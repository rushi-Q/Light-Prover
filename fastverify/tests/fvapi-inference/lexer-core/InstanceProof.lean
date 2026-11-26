instance inst : Subsingleton Unit where
  allEq := by intro a b; cases a; cases b; rfl
