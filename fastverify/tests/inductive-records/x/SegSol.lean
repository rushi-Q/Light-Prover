inductive MyB where
  | t
  | f
def sel (b : MyB) (X Y : Type) : Type := MyB.rec X Y b
inductive U where
  | mk : sel MyB.t Nat Bool → U
theorem goal : True := trivial
