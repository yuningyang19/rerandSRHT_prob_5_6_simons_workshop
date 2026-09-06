import Problem56.Definitions

/-!
Finite and infinite geometric estimates used in the trace summation interface.
-/

open scoped BigOperators

namespace Problem56

private lemma finite_fast_geometric_bound (A : ℝ) (hA : 2 ≤ A) (N : ℕ) :
    (∑ t ∈ Finset.range (N + 1), A ^ (76 * t)) ≤
      2 * A ^ (76 * N) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hAone : 1 ≤ A := hA.trans' (by norm_num)
      have hA76 : 2 ≤ A ^ 76 :=
        hA.trans (by simpa using (pow_le_pow_right₀ hAone (by omega : 1 ≤ 76)))
      have hpow_nonneg : 0 ≤ A ^ (76 * N) := by positivity
      have hstep : 2 * A ^ (76 * N) ≤ A ^ (76 * (N + 1)) := by
        rw [show 76 * (N + 1) = 76 * N + 76 by omega, pow_add]
        nlinarith
      calc
        (∑ t ∈ Finset.range (N + 1), A ^ (76 * t)) +
            A ^ (76 * (N + 1)) ≤
            2 * A ^ (76 * N) + A ^ (76 * (N + 1)) :=
          by simpa [add_comm] using add_le_add_right ih (A ^ (76 * (N + 1)))
        _ ≤ 2 * A ^ (76 * (N + 1)) := by linarith

private lemma trace_prefactor_bound (p : ℕ) (hp : 2 ≤ p) :
    128 * p * (4 * p + 1) ≤ 64 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hp₁ : p + 1 ≤ 2 * p := by omega
      have hp₂ : 4 * (p + 1) + 1 ≤ 2 * (4 * p + 1) := by omega
      have hgrowth :
          128 * (p + 1) * (4 * (p + 1) + 1) ≤
            4 * (128 * p * (4 * p + 1)) := by
        calc
          128 * (p + 1) * (4 * (p + 1) + 1) ≤
              128 * (2 * p) * (2 * (4 * p + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 128 hp₁) hp₂
          _ = 4 * (128 * p * (4 * p + 1)) := by ring
      calc
        128 * (p + 1) * (4 * (p + 1) + 1) ≤
            64 * (128 * p * (4 * p + 1)) :=
          hgrowth.trans (Nat.mul_le_mul_right _ (by omega : 4 ≤ 64))
        _ ≤ 64 * 64 ^ p := Nat.mul_le_mul_left 64 ih
        _ = 64 ^ (p + 1) := by rw [pow_succ]; ring

theorem trace_geometric_summation (p r : ℕ)
    (hp : 2 ≤ p) (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    let ρ : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r
    0 ≤ ρ ∧ ρ ≤ 1 / 2 ∧
    (∑' j : ℕ, ρ ^ j) ≤ 2 ∧
    (∑' j : ℕ, ρ ^ j) ^ 3 ≤ 8 ∧
    (∀ d h : ℕ,
      (∑ t ∈ Finset.range (12 * d + 4 * h + 1),
        (((4 * p + 1 : ℕ) : ℝ) ^ (76 * t))) ≤
          2 * ((4 * p + 1 : ℕ) : ℝ) ^ (912 * d + 304 * h)) ∧
    (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) ≤ 8 ∧
    128 * p * (4 * p + 1) ≤ 64 ^ p ∧
    64 * 9 * K₂ = K₀ := by
  dsimp only
  let A : ℝ := ((4 * p + 1 : ℕ) : ℝ)
  let ρ : ℝ := A ^ 1000 / (r : ℝ)
  have hA : 2 ≤ A := by
    dsimp [A]
    exact_mod_cast (show 2 ≤ 4 * p + 1 by omega)
  have hrpos : 0 < (r : ℝ) := by
    have : 0 < r := by
      have : 0 < 2 * (4 * p + 1) ^ 1000 := by positivity
      omega
    exact_mod_cast this
  have hρnonneg : 0 ≤ ρ := by positivity
  have hρhalf : ρ ≤ 1 / 2 := by
    have hcast : (2 : ℝ) * A ^ 1000 ≤ r := by
      dsimp [A]
      exact_mod_cast hr
    dsimp [ρ]
    rw [div_le_iff₀ hrpos]
    nlinarith
  have hρlt : ρ < 1 := hρhalf.trans_lt (by norm_num)
  let S : ℝ := ∑' j : ℕ, ρ ^ j
  have hSformula : S = (1 - ρ)⁻¹ := by
    dsimp [S]
    exact tsum_geometric_of_lt_one hρnonneg hρlt
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun j ↦ pow_nonneg hρnonneg j)
  have hSle : S ≤ 2 := by
    rw [hSformula]
    have hden : (1 / 2 : ℝ) ≤ 1 - ρ := by linarith
    calc
      (1 - ρ)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hden
      _ = 2 := by norm_num
  have hScube : S ^ 3 ≤ 8 := by
    have h := pow_le_pow_left₀ hSnonneg hSle 3
    norm_num at h
    exact h
  have hfinite : ∀ d h : ℕ,
      (∑ t ∈ Finset.range (12 * d + 4 * h + 1), A ^ (76 * t)) ≤
        2 * A ^ (912 * d + 304 * h) := by
    intro d h
    simpa only [show 912 * d + 304 * h = 76 * (12 * d + 4 * h) by omega]
      using finite_fast_geometric_bound A hA (12 * d + 4 * h)
  have hinner : ∀ s d : ℕ,
      (∑' h : ℕ, ρ ^ (s + d + h)) = ρ ^ (s + d) * S := by
    intro s d
    calc
      (∑' h : ℕ, ρ ^ (s + d + h)) =
          ∑' h : ℕ, ρ ^ (s + d) * ρ ^ h := by
        apply tsum_congr
        intro h
        rw [← pow_add]
      _ = ρ ^ (s + d) * S := by rw [tsum_mul_left]
  have hmiddle : ∀ s : ℕ,
      (∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) = ρ ^ s * S * S := by
    intro s
    calc
      (∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) =
          ∑' d : ℕ, ρ ^ (s + d) * S := by
        apply tsum_congr
        exact hinner s
      _ = (∑' d : ℕ, ρ ^ (s + d)) * S := by rw [tsum_mul_right]
      _ = (∑' d : ℕ, ρ ^ s * ρ ^ d) * S := by
        rw [show (fun d : ℕ ↦ ρ ^ (s + d)) =
            (fun d : ℕ ↦ ρ ^ s * ρ ^ d) by
          funext d
          rw [← pow_add]]
      _ = ρ ^ s * S * S := by rw [tsum_mul_left]
  have htriple :
      (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) = S ^ 3 := by
    calc
      (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) =
          ∑' s : ℕ, ρ ^ s * S * S := by
        apply tsum_congr
        exact hmiddle
      _ = (∑' s : ℕ, ρ ^ s) * S * S := by
        rw [← tsum_mul_right, tsum_mul_right]
      _ = S ^ 3 := by ring
  change 0 ≤ ρ ∧ ρ ≤ 1 / 2 ∧ S ≤ 2 ∧ S ^ 3 ≤ 8 ∧
    (∀ d h : ℕ,
      (∑ t ∈ Finset.range (12 * d + 4 * h + 1), A ^ (76 * t)) ≤
        2 * A ^ (912 * d + 304 * h)) ∧
    (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) ≤ 8 ∧
    128 * p * (4 * p + 1) ≤ 64 ^ p ∧ 64 * 9 * K₂ = K₀
  exact ⟨hρnonneg, hρhalf, hSle, hScube, hfinite,
    htriple.le.trans hScube, trace_prefactor_bound p hp, by norm_num [K₂, K₀]⟩

#print axioms trace_geometric_summation

end Problem56
