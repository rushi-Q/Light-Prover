-- not imported by Main: a module that does not compile (the official `lake build` of the default targets fails,
-- the official `lake comparator` builds only the solution module and is not affected)
theorem dead : 1 = 2 := rfl
