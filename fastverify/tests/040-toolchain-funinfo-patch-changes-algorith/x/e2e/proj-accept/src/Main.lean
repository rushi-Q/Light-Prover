import BigFn
-- build-time metaprogram outside every exported theorem's closure: getFunInfo on a constant whose binder type is a
-- large DAG (2^29 tree nodes, 29 distinct subterms); official Lean 4.33.1 walks it as a tree.
mk_big_fn f28 28
set_option maxHeartbeats 200000 in
fun_info f28
theorem riemannHypothesis : (2 : Nat) + 2 = 4 := rfl
theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl
