-- Extra is a module of the default-target lib A (built by `lake build` even though Main does not import it) and also of lib C
-- (listed first, not a target). It does not compile.
def broken : Nat := "not a Nat"
