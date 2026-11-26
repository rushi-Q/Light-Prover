import BigFn
-- f k : (x : Nat) → bigShared x k = 0 → Nat, whose binder type has 2^(k+1)-1 tree nodes but only k+1 distinct subterms.
-- `getFunInfo` (public Meta API, used by simp/congr/...) walks it as a tree in Lean 4.33.1 (FunInfo.collectDeps).
mk_big_fn f20 20
set_option maxHeartbeats 200000 in
fun_info f20
mk_big_fn f24 24
set_option maxHeartbeats 200000 in
fun_info f24
mk_big_fn f28 28
set_option maxHeartbeats 200000 in
fun_info f28
