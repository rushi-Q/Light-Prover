structure P : Prop where
  x : True
namespace N
@[scoped ext] theorem _root_.my_ext (a b : P) : a = b := rfl
end N
