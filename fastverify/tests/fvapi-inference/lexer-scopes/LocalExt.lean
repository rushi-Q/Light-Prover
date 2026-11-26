structure P : Prop where
  x : True
@[local ext] theorem my_ext (a b : P) : a = b := rfl
