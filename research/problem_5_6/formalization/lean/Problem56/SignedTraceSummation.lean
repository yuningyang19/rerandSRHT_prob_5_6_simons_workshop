import Problem56.TraceGeometric

/-!
# Final signed-trace summation

This file isolates the final numerical step of the signed-trace proposition.
The preceding finite trace/selector/entry-partition expansion is responsible
for producing `hmaster`; the theorem below converts exactly that master bound
to the public `K₀` bound using the already checked geometric estimates.
-/

namespace Problem56

open scoped BigOperators

theorem signedTrace_bound_of_master_geometric_bound
    (p r : ℕ) (x base : ℝ)
    (hp : 2 ≤ p) (hr : 2 * (4 * p + 1) ^ 1000 ≤ r)
    (hbase : 0 ≤ base)
    (hmaster :
      |x| ≤ 16 * (p : ℝ) * (4 * p + 1) * (9 * K₂ : ℝ) ^ p * base *
        (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ,
          ((((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r) ^ (s + d + h)))) :
    |x| ≤ (K₀ : ℝ) ^ p * base := by
  obtain ⟨_, _, _, _, _, htriple, hprefactor, hconstant⟩ :=
    trace_geometric_summation p r hp hr
  have hfactor_nonneg :
      0 ≤ 16 * (p : ℝ) * (4 * p + 1) * (9 * K₂ : ℝ) ^ p * base := by
    positivity
  have hpower_nonneg : 0 ≤ (9 * K₂ : ℝ) ^ p := by positivity
  have hprefactor_real :
      (128 : ℝ) * p * (4 * p + 1) ≤ (64 : ℝ) ^ p := by
    exact_mod_cast hprefactor
  have hconstant_real : (64 : ℝ) * 9 * K₂ = K₀ := by
    exact_mod_cast hconstant
  calc
    |x| ≤ 16 * (p : ℝ) * (4 * p + 1) * (9 * K₂ : ℝ) ^ p * base *
        (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ,
          ((((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r) ^ (s + d + h))) := hmaster
    _ ≤ 16 * (p : ℝ) * (4 * p + 1) * (9 * K₂ : ℝ) ^ p * base * 8 := by
      exact mul_le_mul_of_nonneg_left htriple hfactor_nonneg
    _ = (128 * (p : ℝ) * (4 * p + 1)) * (9 * K₂ : ℝ) ^ p * base := by
      ring
    _ ≤ (64 : ℝ) ^ p * (9 * K₂ : ℝ) ^ p * base := by
      have hprefactor_power :=
        mul_le_mul_of_nonneg_right hprefactor_real hpower_nonneg
      exact mul_le_mul_of_nonneg_right hprefactor_power hbase
    _ = ((64 : ℝ) * (9 * K₂)) ^ p * base := by
      congr 1
      exact (mul_pow (64 : ℝ) (9 * K₂ : ℝ) p).symm
    _ = (K₀ : ℝ) ^ p * base := by rw [show (64 : ℝ) * (9 * K₂) = K₀ by
      linarith only [hconstant_real]]

#print axioms signedTrace_bound_of_master_geometric_bound

end Problem56
