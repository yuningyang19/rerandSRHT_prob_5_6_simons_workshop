import Problem56.Definitions

/-!
The quadratic-root estimate used by the spectral-transfer branch.  This module
is intentionally definitions-only: it does not import the admitted statement
layer.
-/

namespace Problem56

open scoped ComplexConjugate

theorem quadratic_root_even_power_bound
    (a t : ℝ) (p : ℕ) (ha : 0 ≤ a) :
    ∀ z₁ z₂ : ℂ,
      z₁ + z₂ = t ∧ z₁ * z₂ = a ^ 2 →
      -2 * a ^ (2 * p) ≤ (z₁ ^ (2 * p) + z₂ ^ (2 * p)).re := by
  intro z₁ z₂ hroots
  rcases hroots with ⟨hsum, hprod⟩
  by_cases him₁ : z₁.im = 0
  · have him₂ : z₂.im = 0 := by
      have h := congrArg Complex.im hsum
      simpa [him₁] using h
    have hz₁ : z₁ = (z₁.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him₁
    have hz₂ : z₂ = (z₂.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him₂
    rw [hz₁, hz₂]
    rw [Complex.add_re, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
    simp only [Complex.ofReal_re]
    have haPow : 0 ≤ a ^ (2 * p) := by positivity
    have hz₁Pow : 0 ≤ z₁.re ^ (2 * p) := by
      rw [pow_mul]
      positivity
    have hz₂Pow : 0 ≤ z₂.re ^ (2 * p) := by
      rw [pow_mul]
      positivity
    linarith
  · have hsumRe : z₁.re + z₂.re = t := by
      have h := congrArg Complex.re hsum
      simpa using h
    have hsumIm : z₁.im + z₂.im = 0 := by
      have h := congrArg Complex.im hsum
      simpa using h
    have hprodIm : z₁.re * z₂.im + z₁.im * z₂.re = 0 := by
      have h := congrArg Complex.im hprod
      simpa [Complex.mul_im, pow_two] using h
    have him₂eq : z₂.im = -z₁.im := by linarith
    have hfactor : z₁.im * (z₂.re - z₁.re) = 0 := by
      calc
        z₁.im * (z₂.re - z₁.re) =
            z₁.re * z₂.im + z₁.im * z₂.re := by
          rw [him₂eq]
          ring
        _ = 0 := hprodIm
    have hre : z₂.re = z₁.re := by
      rcases mul_eq_zero.mp hfactor with hzero | hzero
      · exact (him₁ hzero).elim
      · linarith
    have hz₂conj : z₂ = conj z₁ := by
      apply Complex.ext
      · simp [hre]
      · simp only [Complex.conj_im]
        linarith
    have hnormSqComplex :
        (Complex.normSq z₁ : ℂ) = ((a ^ 2 : ℝ) : ℂ) := by
      calc
        (Complex.normSq z₁ : ℂ) = conj z₁ * z₁ :=
          Complex.normSq_eq_conj_mul_self
        _ = z₁ * conj z₁ := mul_comm _ _
        _ = z₁ * z₂ := by rw [hz₂conj]
        _ = (a : ℂ) ^ 2 := hprod
        _ = ((a ^ 2 : ℝ) : ℂ) := by norm_cast
    have hnormSq : Complex.normSq z₁ = a ^ 2 := by
      exact_mod_cast hnormSqComplex
    have hnormPow : ‖z₁ ^ (2 * p)‖ = a ^ (2 * p) := by
      rw [norm_pow]
      calc
        ‖z₁‖ ^ (2 * p) = (‖z₁‖ ^ 2) ^ p := by rw [← pow_mul]
        _ = (Complex.normSq z₁) ^ p := by rw [Complex.sq_norm]
        _ = (a ^ 2) ^ p := by rw [hnormSq]
        _ = a ^ (2 * p) := by rw [← pow_mul]
    have hrealLower : -a ^ (2 * p) ≤ (z₁ ^ (2 * p)).re := by
      have h := (abs_le.mp (Complex.abs_re_le_norm (z₁ ^ (2 * p)))).1
      rwa [hnormPow] at h
    have hsumPower :
        (z₁ ^ (2 * p) + z₂ ^ (2 * p)).re =
          2 * (z₁ ^ (2 * p)).re := by
      rw [hz₂conj]
      rw [← map_pow (starRingEnd ℂ) z₁ (2 * p)]
      simp only [Complex.add_re, Complex.conj_re]
      ring
    rw [hsumPower]
    linarith

theorem bad_spectral_edge_large_root
    (lam δ θ η : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hδ : 0 < δ)
    (hθ : 0 < θ ∧ θ ≤ 1 / 2) (hη : 0 < η ∧ η < 1)
    (hsmall : δ ≤ θ * η ^ 2 / 64)
    (hbad : |lam - θ| > θ * η) :
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    let t := lam - δ - θ + 2 * δ * θ
    |t| > 63 * (θ * η) / 64 ∧
    (lam = 0 → (1 - δ) * θ > θ * η / 2) ∧
    (lam = 1 → (1 - δ) * (1 - θ) > θ * η / 2) ∧
    (0 < lam → lam < 1 →
      ∃ z₁ z₂ : ℝ, z₁ + z₂ = t ∧ z₁ * z₂ = a2 ∧
        max |z₁| |z₂| > θ * η / 2) := by
  dsimp only
  let q : ℝ := θ * η
  let A : ℝ := δ * (1 - δ) * θ * (1 - θ)
  let T : ℝ := lam - δ - θ + 2 * δ * θ
  change |T| > 63 * q / 64 ∧
    (lam = 0 → (1 - δ) * θ > q / 2) ∧
    (lam = 1 → (1 - δ) * (1 - θ) > q / 2) ∧
    (0 < lam → lam < 1 →
      ∃ z₁ z₂ : ℝ, z₁ + z₂ = T ∧ z₁ * z₂ = A ∧
        max |z₁| |z₂| > q / 2)
  have hq : q = θ * η := rfl
  have hqpos : 0 < q := by
    rw [hq]
    exact mul_pos hθ.1 hη.1
  have hηsq_lt : η ^ 2 < η := by
    nlinarith [mul_pos hη.1 (sub_pos.mpr hη.2)]
  have hδq : δ < q / 64 := by
    have hmul : θ * η ^ 2 < θ * η :=
      mul_lt_mul_of_pos_left hηsq_lt hθ.1
    rw [hq]
    nlinarith
  have hqhalf : q < 1 / 2 := by
    rw [hq]
    calc
      θ * η < θ * 1 := mul_lt_mul_of_pos_left hη.2 hθ.1
      _ ≤ 1 / 2 := by simpa using hθ.2
  have hδhalf : δ < 1 / 2 := by nlinarith
  have hδone : δ < 1 := hδhalf.trans (by norm_num)
  have hTdecomp : lam - θ = T + δ * (1 - 2 * θ) := by
    simp only [T]
    ring
  have hy0 : 0 ≤ δ * (1 - 2 * θ) := by
    exact mul_nonneg hδ.le (by linarith)
  have hy_le : δ * (1 - 2 * θ) ≤ δ := by
    nlinarith [mul_pos hδ hθ.1]
  have hTtri : |lam - θ| ≤ |T| + δ * (1 - 2 * θ) := by
    calc
      |lam - θ| = |T + δ * (1 - 2 * θ)| := congrArg abs hTdecomp
      _ ≤ |T| + |δ * (1 - 2 * θ)| := abs_add_le _ _
      _ = |T| + δ * (1 - 2 * θ) := by rw [abs_of_nonneg hy0]
  have hTlarge : |T| > 63 * q / 64 := by nlinarith
  have hleftBase : η / 2 < 1 - δ := by nlinarith
  have hendpointZero : (1 - δ) * θ > q / 2 := by
    have h := mul_lt_mul_of_pos_right hleftBase hθ.1
    rw [hq]
    nlinarith
  have hthetaBase : 1 / 2 ≤ 1 - θ := by linarith
  have hquarterLower : 1 / 4 < (1 - δ) * (1 - θ) := by
    have hfirst : (1 / 2 : ℝ) * (1 / 2) < (1 - δ) * (1 / 2) := by
      exact mul_lt_mul_of_pos_right (by linarith : (1 / 2 : ℝ) < 1 - δ) (by norm_num)
    have hsecond : (1 - δ) * (1 / 2) ≤ (1 - δ) * (1 - θ) := by
      exact mul_le_mul_of_nonneg_left hthetaBase (by linarith)
    nlinarith
  have hqquarter : q / 2 < 1 / 4 := by nlinarith
  have hendpointOne : (1 - δ) * (1 - θ) > q / 2 := by linarith
  refine ⟨hTlarge, ?_, ?_, ?_⟩
  · intro _
    exact hendpointZero
  · intro _
    exact hendpointOne
  · intro hlam0 hlam1
    have hA0 : 0 ≤ A := by
      simp only [A]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hδ.le (by linarith)) hθ.1.le) (by linarith)
    have hA_le_delta_theta : A ≤ δ * θ := by
      simp only [A]
      have hδfactor : δ * (1 - δ) ≤ δ := by
        nlinarith [mul_pos hδ (sub_pos.mpr hδone)]
      have hθfactor : θ * (1 - θ) ≤ θ := by
        nlinarith [mul_pos hθ.1 (by linarith : 0 < 1 - θ)]
      calc
        δ * (1 - δ) * θ * (1 - θ) =
            (δ * (1 - δ)) * (θ * (1 - θ)) := by ring
        _ ≤ δ * θ :=
          mul_le_mul hδfactor hθfactor (mul_nonneg hθ.1.le (by linarith)) hδ.le
    have hdeltaTheta : δ * θ ≤ q ^ 2 / 64 := by
      calc
        δ * θ ≤ (θ * η ^ 2 / 64) * θ :=
          mul_le_mul_of_nonneg_right hsmall hθ.1.le
        _ = q ^ 2 / 64 := by simp only [q]; ring
    have hAq : A ≤ q ^ 2 / 64 := hA_le_delta_theta.trans hdeltaTheta
    let D : ℝ := T ^ 2 - 4 * A
    have hc0 : 0 ≤ 63 * q / 64 := by positivity
    have hTsq : (63 * q / 64) ^ 2 < T ^ 2 := by
      have hs := (sq_lt_sq₀ hc0 (abs_nonneg T)).2 hTlarge
      simpa only [sq_abs] using hs
    have hDlower : (q / 64) ^ 2 < D := by
      simp only [D]
      nlinarith [sq_nonneg q]
    have hD0 : 0 ≤ D := le_of_lt (lt_of_le_of_lt (sq_nonneg (q / 64)) hDlower)
    have hsqrtSq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD0
    have hsqrtLarge : q / 64 < Real.sqrt D := by
      exact (Real.lt_sqrt (by positivity)).2 hDlower
    let zplus : ℝ := (T + Real.sqrt D) / 2
    let zminus : ℝ := (T - Real.sqrt D) / 2
    refine ⟨zplus, zminus, ?_, ?_, ?_⟩
    · simp only [zplus, zminus]
      ring
    · simp only [zplus, zminus]
      calc
        (T + Real.sqrt D) / 2 * ((T - Real.sqrt D) / 2) =
            (T ^ 2 - (Real.sqrt D) ^ 2) / 4 := by ring
        _ = (T ^ 2 - D) / 4 := by rw [hsqrtSq]
        _ = A := by simp only [D]; ring
    · by_cases hT0 : 0 ≤ T
      · have habsT : |T| = T := abs_of_nonneg hT0
        have hzplusPos : 0 < zplus := by
          simp only [zplus]
          have hq64pos : 0 < q / 64 := div_pos hqpos (by norm_num)
          have hsqrtPos : 0 < Real.sqrt D := hq64pos.trans hsqrtLarge
          exact div_pos (add_pos_of_nonneg_of_pos hT0 hsqrtPos) (by norm_num)
        have hzplusLarge : q / 2 < |zplus| := by
          rw [abs_of_pos hzplusPos]
          simp only [zplus]
          rw [habsT] at hTlarge
          have hsum : q < T + Real.sqrt D := by
            calc
              q = 63 * q / 64 + q / 64 := by ring
              _ < T + Real.sqrt D := add_lt_add hTlarge hsqrtLarge
          exact (div_lt_div_iff_of_pos_right (by norm_num)).2 hsum
        exact lt_of_lt_of_le hzplusLarge (le_max_left _ _)
      · have hTneg : T < 0 := lt_of_not_ge hT0
        have habsT : |T| = -T := abs_of_neg hTneg
        have hzminusNeg : zminus < 0 := by
          simp only [zminus]
          have hnum : T - Real.sqrt D < 0 :=
            sub_neg.mpr (hTneg.trans_le (Real.sqrt_nonneg D))
          exact div_neg_of_neg_of_pos hnum (by norm_num)
        have hzminusLarge : q / 2 < |zminus| := by
          rw [abs_of_neg hzminusNeg]
          simp only [zminus]
          rw [habsT] at hTlarge
          have hsum : q < -T + Real.sqrt D := by
            calc
              q = 63 * q / 64 + q / 64 := by ring
              _ < -T + Real.sqrt D := add_lt_add hTlarge hsqrtLarge
          calc
            q / 2 < (-T + Real.sqrt D) / 2 :=
              (div_lt_div_iff_of_pos_right (by norm_num)).2 hsum
            _ = -((T - Real.sqrt D) / 2) := by ring
        exact lt_of_lt_of_le hzminusLarge (le_max_right _ _)

#print axioms quadratic_root_even_power_bound
#print axioms bad_spectral_edge_large_root

end Problem56
