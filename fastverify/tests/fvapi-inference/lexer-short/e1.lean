structure P : Prop where
  x : True
@[ext] theorem my_ext (a b : P) : a = b := rfl
#print axioms my_ext_iff
#check @my_ext_iff
