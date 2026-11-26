# Small competition-style problems (statement, proof, style tag), written for the throughput benchmark.
# Lean 4.33.1 + Mathlib 0df444a. Every statement is elaborated after the common PREAMBLE in both challenge and solution.
PREAMBLE = "import Mathlib\n\nopen Real Nat Finset\n"

P = []
def p(name, style, stmt, proof):
    P.append(dict(name=name, style=style, stmt=stmt, proof=proof))

# --- norm_num arithmetic / number facts
p("amc_rem_2pow100_mod7", "norm_num", "(2 ^ 100) % 7 = 2", "by norm_num")
p("amc_sum_1_to_100", "decide", "∑ i ∈ range 101, i = 5050", "by decide")
p("nt_prime_1009", "norm_num", "Nat.Prime 1009", "by norm_num")
p("nt_prime_104729", "norm_num", "Nat.Prime 104729", "by norm_num")
p("nt_not_prime_91", "norm_num", "¬ Nat.Prime 91", "by norm_num")
p("nt_gcd_2024_1001", "norm_num", "Nat.gcd 2024 1001 = 11", "by norm_num")
p("nt_lcm_12_18", "norm_num", "Nat.lcm 12 18 = 36", "by norm_num")
p("arith_frac", "norm_num", "(1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1", "by norm_num")
p("arith_real_sqrt", "norm_num", "Real.sqrt 16 = 4", "by\n  rw [show (16:ℝ) = 4 ^ 2 by norm_num]\n  exact Real.sqrt_sq (by norm_num)")
p("arith_pow_mod", "norm_num", "(3 ^ 200) % 10 = 1", "by norm_num")
p("arith_big_mul", "norm_num", "(123456789 : ℤ) * 987654321 = 121932631112635269", "by norm_num")
p("arith_digits_sum", "norm_num", "(Nat.digits 10 2024).sum = 8", "by norm_num")
p("nt_divisors_card_60", "decide", "(Nat.divisors 60).card = 12", "by decide")
p("nt_totient_100", "decide", "Nat.totient 100 = 40", "by decide")
p("nt_factorial_10", "norm_num", "Nat.factorial 10 = 3628800", "by norm_num [Nat.factorial]")
p("nt_choose_10_3", "norm_num", "Nat.choose 10 3 = 120", "by norm_num [Nat.choose]")
p("nt_fib_20", "decide", "Nat.fib 20 = 6765", "by decide")
p("nt_mod_cube", "decide", "∀ n : Fin 9, ((n : ℕ) ^ 3) % 9 ∈ ({0, 1, 8} : Finset ℕ)", "by decide")

# --- omega: linear integer arithmetic
p("lia_two_consec", "omega", "∀ n : ℕ, n % 2 = 0 ∨ n % 2 = 1", "by intro n; omega")
p("lia_sum_odd", "omega", "∀ a b : ℤ, a % 2 = 1 → b % 2 = 1 → (a + b) % 2 = 0", "by intro a b ha hb; omega")
p("lia_system", "omega", "∀ x y : ℤ, x + y = 10 → x - y = 4 → x = 7 ∧ y = 3", "by intro x y h1 h2; omega")
p("lia_div3", "omega", "∀ n : ℕ, (n * 3 + 6) % 3 = 0", "by intro n; omega")
p("lia_bound", "omega", "∀ n : ℕ, 3 * n + 2 < 20 → n ≤ 5", "by intro n h; omega")
p("lia_chicken", "omega", "∀ c r : ℕ, c + r = 35 → 2 * c + 4 * r = 94 → c = 23 ∧ r = 12", "by intro c r h1 h2; omega")
p("lia_mod_comb", "omega", "∀ n : ℕ, n % 4 = 3 → n % 2 = 1", "by intro n h; omega")
p("lia_abs", "omega", "∀ x : ℤ, |x - 3| < 2 → 1 < x ∧ x < 5", "by intro x h; rw [abs_lt] at h; omega")
p("lia_floor_div", "omega", "∀ n : ℕ, n / 2 + (n + 1) / 2 = n", "by intro n; omega")
p("lia_ages", "omega", "∀ a b : ℕ, a = 3 * b → a + 10 = 2 * (b + 10) → a = 30", "by intro a b h1 h2; omega")

# --- nlinarith / positivity: real inequalities
p("ineq_amgm2", "nlinarith", "∀ a b : ℝ, 2 * a * b ≤ a ^ 2 + b ^ 2", "by intro a b; nlinarith [sq_nonneg (a - b)]")
p("ineq_sq_sum", "nlinarith", "∀ a b c : ℝ, a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2",
  "by intro a b c; nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]")
p("ineq_pos_frac", "positivity", "∀ x : ℝ, 0 < x → 0 < x / (x ^ 2 + 1)", "by intro x hx; positivity")
p("ineq_x_plus_inv", "nlinarith", "∀ x : ℝ, 0 < x → 2 ≤ x + 1 / x",
  "by\n  intro x hx\n  rw [show x + 1 / x = (x ^ 2 + 1) / x by field_simp]\n  rw [le_div_iff₀ hx]\n  nlinarith [sq_nonneg (x - 1)]")
p("ineq_cube", "nlinarith", "∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 3 + b ^ 3 ≥ a ^ 2 * b + a * b ^ 2",
  "by intro a b ha hb; nlinarith [sq_nonneg (a - b), mul_nonneg ha hb, mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]")
p("ineq_quad_min", "nlinarith", "∀ x : ℝ, x ^ 2 - 6 * x + 10 ≥ 1", "by intro x; nlinarith [sq_nonneg (x - 3)]")
p("ineq_four_var", "nlinarith", "∀ a b c d : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * (b + c + d) - b ^ 2 * 0",
  "by intro a b c d; nlinarith [sq_nonneg (a / 2 - b), sq_nonneg (a / 2 - c), sq_nonneg (a / 2 - d), sq_nonneg a]")
p("ineq_sqrt2", "nlinarith", "Real.sqrt 2 < 3 / 2",
  "by\n  rw [show (3:ℝ)/2 = Real.sqrt ((3/2)^2) by rw [Real.sqrt_sq]; norm_num]\n  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)")
p("ineq_exp_pos", "positivity", "∀ x : ℝ, 0 < Real.exp x + x ^ 2", "by intro x; positivity")
p("ineq_lin", "linarith", "∀ x y : ℝ, x < y → 2 * x + 1 < 2 * y + 1", "by intro x y h; linarith")
p("ineq_abs_tri", "term", "∀ a b : ℝ, |a + b| ≤ |a| + |b|", "fun a b => abs_add_le a b")
p("ineq_cauchy3", "nlinarith", "∀ a b c x y z : ℝ, (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)",
  "by intro a b c x y z; nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (b * z - c * y), sq_nonneg (a * z - c * x)]")

# --- ring / field_simp identities
p("alg_diff_squares", "ring", "∀ a b : ℝ, (a + b) * (a - b) = a ^ 2 - b ^ 2", "by intro a b; ring")
p("alg_cube_expand", "ring", "∀ x : ℤ, (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1", "by intro x; ring")
p("alg_sophie", "ring", "∀ a b : ℤ, a ^ 4 + 4 * b ^ 4 = (a ^ 2 + 2 * b ^ 2 + 2 * a * b) * (a ^ 2 + 2 * b ^ 2 - 2 * a * b)", "by intro a b; ring")
p("alg_frac_add", "field_simp", "∀ x : ℝ, x ≠ 0 → x ≠ -1 → 1 / x - 1 / (x + 1) = 1 / (x * (x + 1))",
  "by\n  intro x hx hx1\n  have h1 : x + 1 ≠ 0 := fun h => hx1 (by linarith)\n  field_simp\n  ring")
p("alg_solve_linear", "linarith", "∀ x : ℝ, 3 * x + 7 = 22 → x = 5", "by intro x h; linarith")
p("alg_quad_roots", "nlinarith", "∀ x : ℝ, x ^ 2 - 5 * x + 6 = 0 → x = 2 ∨ x = 3",
  "by\n  intro x h\n  have h' : (x - 2) * (x - 3) = 0 := by ring_nf; linarith\n  rcases mul_eq_zero.mp h' with h1 | h1\n  · left; linarith\n  · right; linarith")
p("alg_vieta", "ring", "∀ a b : ℂ, (fun x : ℂ => (x - a) * (x - b)) = (fun x => x ^ 2 - (a + b) * x + a * b)",
  "by intro a b; funext x; ring")
p("alg_complex_mul", "norm_num", "(1 + Complex.I) * (1 - Complex.I) = 2", "by ring_nf; simp [Complex.ext_iff]; norm_num")
p("alg_i_pow4", "simp", "Complex.I ^ 4 = 1", "by simp [pow_succ]")
p("alg_geom_sum", "ring", "∀ x : ℝ, (x - 1) * (x ^ 3 + x ^ 2 + x + 1) = x ^ 4 - 1", "by intro x; ring")
p("alg_func_eq", "simp", "∀ f : ℝ → ℝ, (∀ x, f x = 2 * x + 3) → f (f 1) = 13", "by intro f hf; rw [hf, hf]; norm_num")
p("alg_log_mul", "term", "∀ x y : ℝ, 0 < x → 0 < y → Real.log (x * y) = Real.log x + Real.log y",
  "fun x y hx hy => Real.log_mul (ne_of_gt hx) (ne_of_gt hy)")
p("alg_exp_add", "term", "∀ x y : ℝ, Real.exp (x + y) = Real.exp x * Real.exp y", "fun x y => Real.exp_add x y")

# --- induction / sums
p("ind_gauss", "induction", "∀ n : ℕ, 2 * (∑ i ∈ range (n + 1), i) = n * (n + 1)",
  "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring")
p("ind_sum_odd", "induction", "∀ n : ℕ, ∑ i ∈ range n, (2 * i + 1) = n ^ 2",
  "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ k ih => rw [Finset.sum_range_succ, ih]; ring")
p("ind_sum_sq", "induction", "∀ n : ℕ, 6 * (∑ i ∈ range (n + 1), i ^ 2) = n * (n + 1) * (2 * n + 1)",
  "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring")
p("ind_pow_ge", "induction", "∀ n : ℕ, n < 2 ^ n", "fun n => Nat.lt_two_pow_self")
p("ind_div_7", "induction", "∀ n : ℕ, 7 ∣ 8 ^ n - 1",
  "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    obtain ⟨m, hm⟩ := ih\n    refine ⟨8 * m + 1, ?_⟩\n    have : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)\n    rw [pow_succ]\n    omega")
p("ind_bernoulli", "induction", "∀ (x : ℝ) (n : ℕ), -1 ≤ x → 1 + n * x ≤ (1 + x) ^ n",
  "fun x n hx => one_add_mul_le_pow (by linarith) n")
p("ind_fact_ge", "induction", "∀ n : ℕ, 1 ≤ n ! ", "fun n => Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)")
p("ind_geom", "induction", "∀ n : ℕ, ∑ i ∈ range n, (2 : ℕ) ^ i = 2 ^ n - 1",
  "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    rw [Finset.sum_range_succ, ih, pow_succ]\n    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow\n    omega")

# --- decide / kernel computation
p("dec_list_sort", "decide", "List.insertionSort (fun a b : ℕ => a ≤ b) [5, 3, 9, 1, 4] = [1, 3, 4, 5, 9]", "by decide")
p("dec_bool_xor", "decide", "∀ a b : Bool, (a ^^ b) = (b ^^ a)", "by decide")
p("dec_fin_add", "decide", "∀ a b : Fin 5, a + b = b + a", "by decide")
p("dec_zmod", "decide", "∀ x : ZMod 7, x ^ 7 = x", "by decide")
p("dec_perfect_28", "decide", "∑ d ∈ Nat.properDivisors 28, d = 28", "by decide")
p("dec_pyth", "decide", "∃ a b c : Fin 20, (a:ℕ) ^ 2 + (b:ℕ) ^ 2 = (c:ℕ) ^ 2 ∧ 0 < (a:ℕ) ∧ (a:ℕ) < b", "by decide")
p("dec_nat_sqrt", "norm_num", "∃ k : ℕ, k * k ≤ 1000 ∧ 1000 < (k + 1) * (k + 1)", "⟨31, by norm_num⟩")
p("dec_prime_list", "decide", "(List.range 30).filter Nat.Prime = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]", "by decide")
p("rfl_big_pow", "rfl", "2 ^ 64 = 18446744073709551616", "by rfl")
p("rfl_nat_mul", "rfl", "(12345 : ℕ) * 6789 = 83810205", "rfl")
p("dec_kernel_gcd", "decide", "Nat.gcd 1071 462 = 21", "by decide")

# --- grind / aesop / simp / tauto (automation)
p("logic_tauto", "tauto", "∀ p q r : Prop, (p → q) → (q → r) → p → r", "by intro p q r hpq hqr hp; tauto")
p("logic_demorgan", "simp", "∀ p q : Prop, ¬(p ∨ q) ↔ ¬p ∧ ¬q", "fun p q => not_or")
p("set_inter_sub", "aesop", "∀ (α : Type) (A B : Set α), A ∩ B ⊆ A", "by intro α A B; aesop")
p("set_union_comm", "simp", "∀ (α : Type) (A B : Set α), A ∪ B = B ∪ A", "fun α A B => Set.union_comm A B")
p("grind_lin", "grind", "∀ a b c : ℕ, a = b → b = c → a + 1 = c + 1", "by intro a b c h1 h2; grind")
p("grind_list", "grind", "∀ (l : List ℕ), (l ++ []).length = l.length", "by intro l; grind")
p("simp_list_rev", "simp", "∀ (l : List ℕ), l.reverse.reverse = l", "by intro l; simp")
p("aesop_subset_trans", "tactic", "∀ (α : Type) (A B C : Set α), A ⊆ B → B ⊆ C → A ⊆ C", "by intro α A B C h1 h2 x hx; exact h2 (h1 hx)")
p("simp_finset_card", "simp", "(Finset.range 10).card = 10", "by simp")
p("exists_witness", "term", "∃ n : ℕ, n * n = 144", "⟨12, rfl⟩")

# --- number theory with Mathlib lemmas (term mode / short tactic)
p("nt_infinite_primes", "term", "∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p", "fun n => Nat.exists_infinite_primes n")
p("nt_sqrt2_irr", "term", "Irrational (Real.sqrt 2)", "irrational_sqrt_two")
p("nt_fermat_little", "term", "∀ (p : ℕ) [Fact p.Prime] (a : ZMod p), a ^ p = a", "fun p _ a => ZMod.pow_card a")
p("nt_even_sq", "tactic", "∀ n : ℤ, Even (n ^ 2) → Even n",
  "by\n  intro n h\n  rw [Int.even_pow] at h\n  exact h.1")
p("nt_dvd_trans", "term", "∀ a b c : ℕ, a ∣ b → b ∣ c → a ∣ c", "fun a b c => Nat.dvd_trans")
p("nt_coprime_consec", "tactic", "∀ n : ℕ, Nat.Coprime n (n + 1)", "by intro n; simp")
p("nt_prime_two_le", "term", "∀ p : ℕ, p.Prime → 2 ≤ p", "fun p hp => hp.two_le")
p("nt_sum_digits_9", "decide", "(Nat.digits 10 123456789).sum % 9 = 0", "by norm_num")
p("nt_mod_inv", "decide", "(3 : ZMod 11) * 4 = 1", "by decide")
p("nt_crt_ex", "decide", "∃ x : Fin 60, (x:ℕ) % 3 = 2 ∧ (x:ℕ) % 4 = 3 ∧ (x:ℕ) % 5 = 4", "by decide")
p("nt_wilson_7", "decide", "(Nat.factorial 6) % 7 = 6", "by decide")

# --- analysis / calculus-flavoured, using Mathlib
p("an_sin_sq", "term", "∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 = 1", "fun x => Real.sin_sq_add_cos_sq x")
p("an_cont_poly", "fun_prop", "Continuous (fun x : ℝ => x ^ 3 - 2 * x + 1)", "by fun_prop")
p("an_deriv_sq", "simp", "deriv (fun x : ℝ => x ^ 2) 3 = 6", "by simp; norm_num")
p("an_exp_ge", "term", "∀ x : ℝ, x + 1 ≤ Real.exp x", "fun x => Real.add_one_le_exp x")
p("an_pi_gt3", "term", "3 < Real.pi", "Real.pi_gt_three")
p("an_tendsto_inv", "term", "Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (nhds 0)",
  "tendsto_one_div_atTop_nhds_zero_nat")
p("an_log_one", "simp", "Real.log 1 = 0", "by simp")
p("an_abs_sub_lt", "linarith", "∀ x y : ℝ, |x - y| < 1 → y < x + 1", "by intro x y h; linarith [abs_lt.mp h]")
p("an_mono_exp", "term", "StrictMono Real.exp", "Real.exp_strictMono")

# --- combinatorics / finite
p("comb_pigeon_small", "decide", "∀ f : Fin 4 → Fin 3, ∃ i j, i ≠ j ∧ f i = f j", "by decide")
p("comb_card_pow", "simp", "∀ (s : Finset ℕ), s.powerset.card = 2 ^ s.card", "fun s => Finset.card_powerset s")
p("comb_choose_symm", "term", "∀ n k : ℕ, k ≤ n → Nat.choose n k = Nat.choose n (n - k)", "fun n k h => (Nat.choose_symm h).symm")
p("comb_sum_choose", "term", "∀ n : ℕ, ∑ i ∈ range (n + 1), Nat.choose n i = 2 ^ n", "fun n => Nat.sum_range_choose n")
p("comb_perm_card", "simp", "Fintype.card (Equiv.Perm (Fin 5)) = 120", "by simp [Fintype.card_perm, Nat.factorial]")
p("comb_handshake_4", "decide", "(((Finset.range 4) ×ˢ (Finset.range 4)).filter (fun p => p.1 < p.2)).card = 6", "by decide")
