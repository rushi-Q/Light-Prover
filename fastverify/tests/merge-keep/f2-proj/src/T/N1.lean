import T.Base
namespace N
theorem n1 : Base.one = 1 := rfl
private def one' : Nat := Base.one
def two : Nat := one' + 1
end N
