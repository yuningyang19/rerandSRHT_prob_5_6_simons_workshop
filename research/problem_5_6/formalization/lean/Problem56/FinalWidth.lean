import Problem56.LargeRankCutoff

/-!
Deterministic real/natural arithmetic for the frozen I42 width-selection
interface.  This module contains no probability statement.
-/

namespace Problem56

open scoped BigOperators

private theorem exp_neg_42_lt_one_div_250 :
    Real.exp (-42) < (1 : ℝ) / 250 := by
  have hseries := Real.sum_le_exp_of_nonneg (x := (42 : ℝ)) (by norm_num) 3
  have h925 : (925 : ℝ) ≤ Real.exp 42 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hseries
    exact hseries
  have h250 : (250 : ℝ) < Real.exp 42 := (by norm_num : (250 : ℝ) < 925).trans_le h925
  have hexp : 0 < Real.exp 42 := Real.exp_pos 42
  rw [Real.exp_neg, div_eq_mul_inv]
  apply (inv_lt_iff_one_lt_mul₀' hexp).2
  norm_num
  nlinarith

private theorem exponential_remainder_lt (x : ℝ) (hx : 42 < x) :
    (2 : ℝ) / 1000 + 2 * Real.exp (-x) < 1 / 100 := by
  have hmono : Real.exp (-x) ≤ Real.exp (-42) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsmall : Real.exp (-x) < (1 : ℝ) / 250 :=
    hmono.trans_lt exp_neg_42_lt_one_div_250
  linarith

private theorem rank_le_scaled_ceil (c r : ℕ) (ε : ℝ)
    (hc : 1 ≤ c) (hr : 1 ≤ r) (hε : 0 < ε ∧ ε < 1) :
    r ≤ Nat.ceil ((c : ℝ) * r / ε ^ 2) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hεsq_le : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε - 1)]
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hrR : (0 : ℝ) ≤ r := by positivity
  have hscale : (r : ℝ) ≤ (c : ℝ) * r / ε ^ 2 := by
    apply (le_div_iff₀ hεsq).2
    nlinarith
  have hceil := Nat.le_ceil ((c : ℝ) * r / ε ^ 2)
  exact_mod_cast hscale.trans hceil

private theorem four_large_width_ceil_le (r : ℕ) (ε : ℝ)
    (hr : 1 ≤ r) (hε : 0 < ε ∧ ε < 1) :
    4 * Nat.ceil ((2048 * K₀ : ℝ) * r / ε ^ 2) ≤
      Nat.ceil ((8196 * K₀ : ℝ) * r / ε ^ 2) := by
  let A : ℝ := (2048 * K₀ : ℝ) * r / ε ^ 2
  let B : ℝ := (8196 * K₀ : ℝ) * r / ε ^ 2
  let T : ℝ := (K₀ : ℝ) * r / ε ^ 2
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hεsq_le : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε - 1)]
  have hK : (1 : ℝ) ≤ K₀ := by norm_num [K₀, K₂]
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hunit : (1 : ℝ) ≤ (K₀ : ℝ) * r / ε ^ 2 := by
    apply (le_div_iff₀ hεsq).2
    nlinarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hceilA : (Nat.ceil A : ℝ) < A + 1 := Nat.ceil_lt_add_one hA
  have hAB : A = 2048 * T := by dsimp [A, T]; ring
  have hBB : B = 8196 * T := by dsimp [B, T]; ring
  have hfour : ((4 * Nat.ceil A : ℕ) : ℝ) ≤ B := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hT : 1 ≤ T := by simpa [T] using hunit
    rw [hAB] at hceilA ⊢
    rw [hBB]
    nlinarith
  have hceilB := Nat.le_ceil B
  have hnat : 4 * Nat.ceil A ≤ Nat.ceil B := by
    exact_mod_cast hfour.trans hceilB
  simpa [A, B, Nat.cast_mul] using hnat

private theorem scaled_ceil_mono {c d r : ℕ} {ε : ℝ}
    (hcd : c ≤ d) (hε : 0 < ε) :
    Nat.ceil ((c : ℝ) * r / ε ^ 2) ≤
      Nat.ceil ((d : ℝ) * r / ε ^ 2) := by
  apply Nat.ceil_mono
  have hεsq : 0 ≤ ε ^ 2 := sq_nonneg ε
  gcongr

private theorem rank_le_small_width (r : ℕ) (ε : ℝ)
    (hr : 1 ≤ r) (hε : 0 < ε ∧ ε < 1) :
    r ≤ Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2) := by
  refine (rank_le_scaled_ceil 200 r ε (by norm_num) hr hε).trans ?_
  apply Nat.ceil_mono
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hεsq : 0 ≤ ε ^ 2 := sq_nonneg ε
  apply div_le_div_of_nonneg_right _ hεsq
  norm_num only [Nat.cast_pow]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith [mul_nonneg (sub_nonneg.mpr hrR) hr0]

private theorem small_width_ceil_le_final (r : ℕ) (ε : ℝ)
    (hr : r < R₀) (hε : 0 < ε) :
    Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2) ≤
      Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2) := by
  apply Nat.ceil_mono
  have hεsq : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hrR : (r : ℝ) ≤ (R₀ : ℝ) := Nat.cast_le.mpr (Nat.le_of_lt hr)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hC : (200 : ℝ) * (R₀ : ℝ) ≤
      (explicitUniversalConstant : ℝ) := by
    rw [explicitUniversalConstant]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  apply div_le_div_of_nonneg_right _ hεsq
  have h200 : (200 : ℝ) * r ≤ 200 * R₀ :=
    mul_le_mul_of_nonneg_left hrR (by norm_num)
  calc
    (200 : ℝ) * r ^ 2 = (200 * r) * r := by ring
    _ ≤ (200 * R₀) * r := mul_le_mul_of_nonneg_right h200 hr0
    _ ≤ explicitUniversalConstant * r :=
      mul_le_mul_of_nonneg_right hC hr0

private theorem large_width_ceil_le_final (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Nat.ceil ((2048 * K₀ : ℝ) * r / ε ^ 2) ≤
      Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2) := by
  have hcoeff : 2048 * K₀ ≤ explicitUniversalConstant := by
    rw [explicitUniversalConstant]
    exact (Nat.mul_le_mul_right K₀ (by omega : 2048 ≤ 8196)).trans
      (Nat.le_add_left _ _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (scaled_ceil_mono (r := r) (ε := ε) hcoeff hε)

private theorem larger_width_ceil_le_final (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Nat.ceil ((8196 * K₀ : ℝ) * r / ε ^ 2) ≤
      Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2) := by
  have hcoeff : 8196 * K₀ ≤ explicitUniversalConstant := by
    rw [explicitUniversalConstant]
    exact Nat.le_add_left _ _
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (scaled_ceil_mono (r := r) (ε := ε) hcoeff hε)

theorem final_width_constant_assembly :
    explicitUniversalConstant = 200 * R₀ + 8196 * K₀ ∧
    ∀ (m r : ℕ) (ε : ℝ),
      1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
      ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
        k ≤ Nat.min (walshCard m)
          (Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2)) ∧
        ((r < R₀ ∧
            k = Nat.min (walshCard m)
              (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))) ∨
          (R₀ ≤ r ∧
            let k₀ := Nat.ceil ((2048 * K₀ : ℝ) * r / ε ^ 2)
            (walshCard m ≤ 4 * k₀ →
              k = walshCard m ∧
              k ≤ Nat.ceil ((8196 * K₀ : ℝ) * r / ε ^ 2)) ∧
            (4 * k₀ < walshCard m →
              k = k₀ ∧
              (1 + ε / 4) * k₀ / walshCard m ≤ 5 / 16 ∧
              (3 : ℝ) / 4 * k₀ ≥
                (1536 * K₀ : ℝ) * r / ε ^ 2 ∧
              2 / 1000 + 2 * Real.exp (-(ε ^ 2 * k₀ / 48)) < 1 / 100))) := by
  constructor
  · rfl
  intro m r ε hr hrn hε0 hε1
  have hε : 0 < ε ∧ ε < 1 := ⟨hε0, hε1⟩
  by_cases hsmall : r < R₀
  · let k := Nat.min (walshCard m)
      (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))
    refine ⟨k, ?_, Nat.min_le_left _ _, ?_, Or.inl ⟨hsmall, rfl⟩⟩
    · exact le_min hrn (rank_le_small_width r ε hr hε)
    · apply le_min (Nat.min_le_left _ _)
      exact (Nat.min_le_right _ _).trans
        (small_width_ceil_le_final r ε hsmall hε0)
  · have hlarge : R₀ ≤ r := Nat.le_of_not_gt hsmall
    let k₀ := Nat.ceil ((2048 * K₀ : ℝ) * r / ε ^ 2)
    by_cases hfull : walshCard m ≤ 4 * k₀
    · refine ⟨walshCard m, hrn, le_rfl, ?_, Or.inr ⟨hlarge, ?_⟩⟩
      clear hlarge hsmall
      · apply le_min le_rfl
        exact hfull.trans ((four_large_width_ceil_le r ε hr hε).trans
          (larger_width_ceil_le_final r ε hε0))
      · dsimp only
        constructor
        · intro _
          exact ⟨rfl, hfull.trans (four_large_width_ceil_le r ε hr hε)⟩
        · intro hnot
          omega
    · have hcut : 4 * k₀ < walshCard m := Nat.lt_of_not_ge hfull
      have hk₀r : r ≤ k₀ := by
        simpa only [k₀, Nat.cast_mul, Nat.cast_ofNat] using
          rank_le_scaled_ceil (2048 * K₀) r ε (by
          simp only [K₀, K₂]
          norm_num) hr hε
      have hk₀n : k₀ ≤ walshCard m := by omega
      refine ⟨k₀, hk₀r, hk₀n, ?_, Or.inr ⟨hlarge, ?_⟩⟩
      clear hlarge hsmall
      · apply le_min hk₀n
        exact large_width_ceil_le_final r ε hε0
      · dsimp only
        clear hlarge hsmall
        constructor
        · intro hcontra
          omega
        · intro _
          refine ⟨rfl, ?_, ?_, ?_⟩
          · have hnR : (0 : ℝ) < walshCard m := by
              exact_mod_cast (lt_of_lt_of_le (by omega : 0 < r) hrn)
            apply (div_le_iff₀ hnR).2
            have hcutR : (4 : ℝ) * k₀ < walshCard m := by
              exact_mod_cast hcut
            have hk₀R : (0 : ℝ) ≤ k₀ := by positivity
            have hepsmul : ε * k₀ ≤ k₀ := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hε1.le) hk₀R]
            nlinarith
          · have hceil :
                (2048 * K₀ : ℝ) * r / ε ^ 2 ≤ (k₀ : ℝ) := by
              simpa only [k₀] using
                (Nat.le_ceil ((2048 * K₀ : ℝ) * r / ε ^ 2))
            calc
              (1536 * K₀ : ℝ) * r / ε ^ 2 =
                  (3 : ℝ) / 4 *
                    ((2048 * K₀ : ℝ) * r / ε ^ 2) := by ring
              _ ≤ (3 : ℝ) / 4 * k₀ :=
                mul_le_mul_of_nonneg_left hceil (by norm_num)
          · apply exponential_remainder_lt
            have hceil :
                (2048 * K₀ : ℝ) * r / ε ^ 2 ≤ (k₀ : ℝ) := by
              simpa only [k₀] using
                (Nat.le_ceil ((2048 * K₀ : ℝ) * r / ε ^ 2))
            have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε0
            have hKR : (1 : ℝ) ≤ (K₀ : ℝ) * r := by
              have hK : (1 : ℝ) ≤ K₀ := by norm_num [K₀, K₂]
              have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
              calc
                (1 : ℝ) = 1 * 1 := by ring
                _ ≤ (K₀ : ℝ) * r :=
                  mul_le_mul hK hrR (by norm_num) (by norm_num)
            have hscaled := mul_le_mul_of_nonneg_left hceil hεsq.le
            have hcancel : ε ^ 2 *
                ((2048 * K₀ : ℝ) * r / ε ^ 2) =
                (2048 : ℝ) * ((K₀ : ℝ) * r) := by
              field_simp
            rw [hcancel] at hscaled
            have hbase : (2048 : ℝ) ≤ ε ^ 2 * k₀ := by
              calc
                (2048 : ℝ) = 2048 * 1 := by ring
                _ ≤ 2048 * ((K₀ : ℝ) * r) := by gcongr
                _ ≤ ε ^ 2 * k₀ := hscaled
            nlinarith

#print axioms exponential_remainder_lt
#print axioms final_width_constant_assembly

end Problem56
