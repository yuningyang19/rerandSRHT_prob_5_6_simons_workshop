import Problem56.Definitions

namespace Problem56

lemma cutoff_linear_le_pow (k : ℕ) (hk : 20 ≤ k) :
    4000 * (k + 1) + 49 ≤ 2 ^ (k - 3) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        4000 * (k + 1 + 1) + 49 ≤ 2 * (4000 * (k + 1) + 49) := by omega
        _ ≤ 2 * 2 ^ (k - 3) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1 - 3) := by
          have hexp : k + 1 - 3 = (k - 3) + 1 := by omega
          rw [hexp, pow_succ]
          omega

lemma cutoff_base_le_pow (q : ℕ) (hq : 20000 ≤ q) :
    4 * (q + 12) + 1 ≤ 2 ^ (q / 1000 - 3) := by
  have hk : 20 ≤ q / 1000 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hmod := Nat.mod_add_div q 1000
  have hmodlt := Nat.mod_lt q (by norm_num : 0 < 1000)
  calc
    4 * (q + 12) + 1 ≤ 4000 * (q / 1000 + 1) + 49 := by omega
    _ ≤ 2 ^ (q / 1000 - 3) := cutoff_linear_le_pow _ hk

lemma cutoff_polynomial_le_previous_power (q : ℕ) (hq : 20000 ≤ q) :
    2 * (4 * (q + 12) + 1) ^ 1000 ≤ 2 ^ (q - 1) := by
  have hbase := cutoff_base_le_pow q hq
  have hmod := Nat.mod_add_div q 1000
  have hmodlt := Nat.mod_lt q (by norm_num : 0 < 1000)
  have hk : 20 ≤ q / 1000 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hexp : (q / 1000 - 3) * 1000 + 1 ≤ q - 1 := by omega
  calc
    2 * (4 * (q + 12) + 1) ^ 1000 ≤
        2 * (2 ^ (q / 1000 - 3)) ^ 1000 :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase 1000)
    _ = 2 ^ ((q / 1000 - 3) * 1000 + 1) := by
      rw [← pow_mul, pow_succ]
      omega
    _ ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) hexp

lemma cutoff_clog_lower_bound (r : ℕ) (hr : R₀ ≤ r) :
    20000 ≤ Nat.clog 2 r := by
  have hrlarge : 2 ^ 20000 ≤ r := hr
  rw [show 20000 = Nat.clog 2 (2 ^ 20000) by
    symm
    exact Nat.clog_pow 2 20000 (by norm_num)]
  exact Nat.clog_mono_right 2 hrlarge

lemma cutoff_scaled_clog_bound (r : ℕ) :
    Nat.clog 2 (3000 * r) ≤ Nat.clog 2 r + 12 := by
  have hrpow : r ≤ 2 ^ Nat.clog 2 r := Nat.le_pow_clog (by norm_num) r
  apply Nat.clog_le_of_le_pow
  calc
    3000 * r ≤ 2 ^ 12 * 2 ^ Nat.clog 2 r :=
      Nat.mul_le_mul (by norm_num) hrpow
    _ = 2 ^ (Nat.clog 2 r + 12) := by
      rw [← pow_add]
      congr 1
      omega

set_option maxRecDepth 10000 in
lemma large_rank_cutoff_nat (r : ℕ) (hr : R₀ ≤ r) :
    2 * (4 * Nat.clog 2 (3000 * r) + 1) ^ 1000 ≤ r := by
  have hrlarge : 2 ^ 20000 ≤ r := hr
  have hrpos : 1 < r :=
    (Nat.one_lt_pow (by norm_num) (by norm_num)).trans_le hrlarge
  have hq : 20000 ≤ Nat.clog 2 r := cutoff_clog_lower_bound r hr
  have hp : Nat.clog 2 (3000 * r) ≤ Nat.clog 2 r + 12 :=
    cutoff_scaled_clog_bound r
  have hpbase :
      4 * Nat.clog 2 (3000 * r) + 1 ≤ 4 * (Nat.clog 2 r + 12) + 1 := by
    omega
  have hfirst :
      2 * (4 * Nat.clog 2 (3000 * r) + 1) ^ 1000 ≤
        2 * (4 * (Nat.clog 2 r + 12) + 1) ^ 1000 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpbase 1000)
  have hsecond :
      2 * (4 * (Nat.clog 2 r + 12) + 1) ^ 1000 ≤
        2 ^ (Nat.clog 2 r - 1) :=
    cutoff_polynomial_le_previous_power (Nat.clog 2 r) hq
  have hthird : 2 ^ (Nat.clog 2 r - 1) < r := by
    simpa only [Nat.pred_eq_sub_one] using
      (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hrpos)
  exact (hfirst.trans hsecond).trans hthird.le

theorem large_rank_cutoff_arithmetic (r : ℕ) (hr : R₀ ≤ r) :
    let p := Nat.ceil (Real.logb 2 (3000 * r : ℝ))
    2 * (4 * p + 1) ^ 1000 ≤ r := by
  dsimp only
  have hceil : Nat.ceil (Real.logb 2 (3000 * r : ℝ)) =
      Nat.clog 2 (3000 * r) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      (Real.natCeil_logb_natCast 2 (3000 * r))
  rw [hceil]
  exact large_rank_cutoff_nat r hr

#print axioms large_rank_cutoff_arithmetic

end Problem56
