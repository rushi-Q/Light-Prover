import Toy.A
namespace ToyNs.B
theorem f_ge (n : Nat) : n < ToyNs.f n := Nat.lt_succ_self n
end ToyNs.B
