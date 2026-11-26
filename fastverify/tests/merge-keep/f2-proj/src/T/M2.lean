import T.Base
namespace P
def other : Nat := 0
end P
namespace Q
def val : Nat := 2
end Q
open P Q
def w : Nat := val
