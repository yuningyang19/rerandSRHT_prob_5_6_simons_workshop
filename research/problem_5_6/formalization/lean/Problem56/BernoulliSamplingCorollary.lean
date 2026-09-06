import Problem56.TwoProjectionTransfer
import Problem56.SmallRankSecondMoment
import Problem56.BinomialTail

/-!
The Bernoulli coordinate-sampling corollary, conditional only on the exact
signed-trace estimate.  The statement layer can discharge that hypothesis
with `signed_trace_proposition` without introducing an import cycle.
-/

open scoped BigOperators Matrix

namespace Problem56

private theorem bernoulliProjection_isOrthogonalProjection
    {α : Type*} [Fintype α] [DecidableEq α] (e : SignLayer α) :
    IsOrthogonalProjection (bernoulliProjection e) := by
  constructor
  · simp only [bernoulliProjection, Matrix.diagonal_transpose]
  · ext i j
    simp [bernoulliProjection, Matrix.mul_apply, Matrix.diagonal_apply]
    aesop

private theorem bernoulliWeight_sum_eq_one
    {α : Type*} [Fintype α] [DecidableEq α] (θ : ℝ) :
    (∑ e : SignLayer α, bernoulliWeight θ e) = 1 := by
  have h := bernoulli_exp_count_sum (α := α) θ 0
  simpa using h

private theorem signPairExpectation_mono
    {α : Type*} [Fintype α] [DecidableEq α]
    (F G : SignLayer α → SignLayer α → ℝ)
    (hFG : ∀ d₁ d₂, F d₁ d₂ ≤ G d₁ d₂) :
    signPairExpectation F ≤ signPairExpectation G := by
  unfold signPairExpectation uniformExpectation
  apply div_le_div_of_nonneg_right
  · have hsum := Finset.sum_le_sum fun d₁ (_ : d₁ ∈ Finset.univ) ↦
        Finset.sum_le_sum fun d₂ (_ : d₂ ∈ Finset.univ) ↦ hFG d₁ d₂
    simpa only [Fintype.sum_prod_type] using hsum
  · positivity

private theorem signPairExpectation_mul_const
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : SignLayer α → SignLayer α → ℝ) (c : ℝ) :
    signPairExpectation (fun d₁ d₂ ↦ F d₁ d₂ * c) =
      signPairExpectation F * c := by
  calc
    signPairExpectation (fun d₁ d₂ ↦ F d₁ d₂ * c) =
        signPairExpectation (fun d₁ d₂ ↦ c * F d₁ d₂) := by
      congr 1
      funext d₁ d₂
      ring
    _ = c * signPairExpectation F := signPairExpectation_const_mul c F
    _ = _ := by ring

private theorem signPairExpectation_add_const
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : SignLayer α → SignLayer α → ℝ) (c : ℝ) :
    signPairExpectation (fun d₁ d₂ ↦ F d₁ d₂ + c) =
      signPairExpectation F + c := by
  change uniformExpectation
      (fun d : SignLayer α × SignLayer α ↦ F d.1 d.2 + c) =
    uniformExpectation (fun d : SignLayer α × SignLayer α ↦ F d.1 d.2) + c
  simpa only [sub_neg_eq_add, neg_neg] using
    uniformExpectation_sub_const
      (fun d : SignLayer α × SignLayer α ↦ F d.1 d.2) (-c)

private theorem bernoulli_failure_arithmetic (p r : ℕ)
    (hp : Nat.ceil (Real.logb 2 (3000 * r : ℝ)) ≤ p) :
    (3 : ℝ) * r * 2 ^ (-(p : ℤ)) ≤ 1 / 1000 := by
  by_cases hr : r = 0
  · subst r
    norm_num
  have hrpos : 0 < (3000 : ℝ) * r := by positivity
  have hceil : Real.logb 2 (3000 * r : ℝ) ≤
      (Nat.ceil (Real.logb 2 (3000 * r : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hpc : (Nat.ceil (Real.logb 2 (3000 * r : ℝ)) : ℝ) ≤ p := by
    exact_mod_cast hp
  have hlog : Real.logb 2 (3000 * r : ℝ) ≤ (p : ℝ) := hceil.trans hpc
  have hpow : (3000 : ℝ) * r ≤ (2 : ℝ) ^ p := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (b := 2) (y := (p : ℝ))
      (by norm_num) hrpos).mp hlog
  have hpowpos : 0 < (2 : ℝ) ^ p := by positivity
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply (div_le_iff₀ hpowpos).2
  calc
    (3 : ℝ) * r = (1 / 1000) * (3000 * r) := by ring
    _ ≤ (1 / 1000) * 2 ^ p :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem bernoulli_coordinate_sampling_corollary_of_trace {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (p : ℕ) (hp : p = Nat.ceil (Real.logb 2 (3000 * r : ℝ)))
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r)
    (η θ : ℝ) (hη : 0 < η ∧ η < 1) (hθ : 0 < θ ∧ θ ≤ 1 / 2)
    (hκ : 64 * K₀ * r / η ^ 2 ≤ (walshCard m : ℝ) * θ)
    (htrace :
      |signBernoulliExpectation θ (fun d₁ d₂ e ↦
        Matrix.trace (((randomProjection d₁ d₂ V -
            ((r : ℝ) / walshCard m) • 1) *
          (bernoulliProjection e - θ • 1)) ^ (2 * p)))| ≤
        (K₀ : ℝ) ^ p * (((r : ℝ) / walshCard m) * θ) ^ p) :
    signPairExpectation (fun d₁ d₂ ↦
      bernoulliProbability θ (fun e ↦
        euclideanOperatorNorm
          (bernoulliGram θ (transformedFrame d₁ d₂ V) e - 1) > η)) ≤
      1 / 1000 := by
  classical
  have hr2 : 2 ≤ r := by
    have hbasepos : 0 < (4 * p + 1) ^ 1000 :=
      pow_pos (by omega) 1000
    have hbase : 1 ≤ (4 * p + 1) ^ 1000 := hbasepos
    omega
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hlog : (2 : ℝ) ≤ Real.logb 2 (3000 * r : ℝ) := by
      apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).2
      rw [Real.rpow_two]
      norm_num
      exact_mod_cast (show 4 ≤ 3000 * r by omega)
    have hceil := hlog.trans (Nat.le_ceil (Real.logb 2 (3000 * r : ℝ)))
    exact_mod_cast hceil
  have hnpos : (0 : ℝ) < walshCard m := by
    simp [walshCard]
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hr2)
  have hηsqpos : 0 < η ^ 2 := sq_pos_of_pos hη.1
  have hK : (1 : ℝ) ≤ K₀ := by norm_num [K₀, K₂]
  have hκ' : (64 : ℝ) * K₀ * r ≤
      ((walshCard m : ℝ) * θ) * η ^ 2 := by
    exact (div_le_iff₀ hηsqpos).mp (by simpa using hκ)
  have hsmall : (r : ℝ) / walshCard m ≤ θ * η ^ 2 / 64 := by
    apply (div_le_iff₀ hnpos).2
    have hleft : (64 : ℝ) * r ≤ 64 * K₀ * r := by nlinarith
    have hmain : (64 : ℝ) * r ≤ (walshCard m : ℝ) * θ * η ^ 2 :=
      hleft.trans hκ'
    nlinarith
  have hδpos : 0 < (r : ℝ) / walshCard m := div_pos hrpos hnpos
  have hδhalf : (r : ℝ) / walshCard m ≤ 1 / 2 := by
    calc
      (r : ℝ) / walshCard m ≤ θ * η ^ 2 / 64 := hsmall
      _ ≤ 1 / 2 := by
        have hηsq : η ^ 2 ≤ 1 := by nlinarith [sq_nonneg η]
        nlinarith [mul_nonneg hθ.1.le hηsqpos.le]
  let δ : ℝ := (r : ℝ) / walshCard m
  let a2 : ℝ := δ * (1 - δ) * θ * (1 - θ)
  let bad : SignLayer (WalshIndex m) → SignLayer (WalshIndex m) →
      SignLayer (WalshIndex m) → Prop := fun d₁ d₂ e ↦
    euclideanOperatorNorm
      (bernoulliGram θ (transformedFrame d₁ d₂ V) e - 1) > η
  let traceTerm : SignLayer (WalshIndex m) → SignLayer (WalshIndex m) →
      SignLayer (WalshIndex m) → ℝ := fun d₁ d₂ e ↦
    Matrix.trace (((randomProjection d₁ d₂ V - δ • 1) *
      (bernoulliProjection e - θ • 1)) ^ (2 * p))
  let edge : ℝ := (θ * η / 2) ^ (2 * p)
  let compensation : ℝ := 2 * (r : ℝ) * a2 ^ p
  have hpoint (d₁ d₂ e : SignLayer (WalshIndex m)) :
      (if bad d₁ d₂ e then edge else 0) ≤
        traceTerm d₁ d₂ e + compensation := by
    have htransfer := (two_projection_spectral_transfer_proof
      (transformedFrame d₁ d₂ V) (bernoulliProjection e)
      (transformedFrame_orthonormal V hV d₁ d₂)
      (bernoulliProjection_isOrthogonalProjection e)
      δ θ (le_trans (by norm_num) hp2) ⟨by simpa [δ] using hδpos,
        by simpa [δ] using hδhalf⟩ hθ).2 η hη.1 hη.2 (by
          simpa [δ] using hsmall)
    by_cases hbad : bad d₁ d₂ e
    · rw [if_pos hbad]
      have hb : euclideanOperatorNorm
          (θ⁻¹ • ((transformedFrame d₁ d₂ V).transpose *
            bernoulliProjection e * transformedFrame d₁ d₂ V) - 1) > η := by
        simpa only [bad, bernoulliGram] using hbad
      rw [if_pos hb] at htransfer
      simpa only [edge, traceTerm, compensation, a2, randomProjection] using
        htransfer
    · rw [if_neg hbad]
      have hb : ¬euclideanOperatorNorm
          (θ⁻¹ • ((transformedFrame d₁ d₂ V).transpose *
            bernoulliProjection e * transformedFrame d₁ d₂ V) - 1) > η := by
        simpa only [bad, bernoulliGram] using hbad
      rw [if_neg hb] at htransfer
      simpa only [traceTerm, compensation, a2, randomProjection] using htransfer
  have hbernoulli (d₁ d₂ : SignLayer (WalshIndex m)) :
      bernoulliProbability θ (bad d₁ d₂) * edge ≤
        bernoulliExpectation θ (traceTerm d₁ d₂) + compensation := by
    have hθunit : 0 ≤ θ ∧ θ ≤ 1 :=
      ⟨hθ.1.le, hθ.2.trans (by norm_num)⟩
    calc
      bernoulliProbability θ (bad d₁ d₂) * edge =
          ∑ e, bernoulliWeight θ e *
            (if bad d₁ d₂ e then edge else 0) := by
        unfold bernoulliProbability
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : bad d₁ d₂ e <;> simp [he]
      _ ≤ ∑ e, bernoulliWeight θ e *
          (traceTerm d₁ d₂ e + compensation) := by
        apply Finset.sum_le_sum
        intro e _
        exact mul_le_mul_of_nonneg_left (hpoint d₁ d₂ e)
          (bernoulliWeight_nonneg θ hθunit e)
      _ = bernoulliExpectation θ (traceTerm d₁ d₂) + compensation := by
        unfold bernoulliExpectation
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, bernoulliWeight_sum_eq_one]
        ring
  have havg :
      signPairExpectation (fun d₁ d₂ ↦
          bernoulliProbability θ (bad d₁ d₂)) * edge ≤
        signBernoulliExpectation θ traceTerm + compensation := by
    calc
      signPairExpectation (fun d₁ d₂ ↦
          bernoulliProbability θ (bad d₁ d₂)) * edge =
          signPairExpectation (fun d₁ d₂ ↦
            bernoulliProbability θ (bad d₁ d₂) * edge) := by
        rw [signPairExpectation_mul_const]
      _ ≤ signPairExpectation (fun d₁ d₂ ↦
          bernoulliExpectation θ (traceTerm d₁ d₂) + compensation) := by
        exact signPairExpectation_mono _ _ hbernoulli
      _ = signBernoulliExpectation θ traceTerm + compensation := by
        rw [signPairExpectation_add_const]
        rfl
  have htrace' : |signBernoulliExpectation θ traceTerm| ≤
      (K₀ : ℝ) ^ p * (δ * θ) ^ p := by
    simpa only [traceTerm, δ] using htrace
  have hraw :
      signPairExpectation (fun d₁ d₂ ↦
          bernoulliProbability θ (bad d₁ d₂)) * edge ≤
        (K₀ : ℝ) ^ p * (δ * θ) ^ p + compensation := by
    apply havg.trans
    gcongr
    exact le_trans (le_abs_self _) htrace'
  have hKdelta : (K₀ : ℝ) * δ ≤ θ * η ^ 2 / 64 := by
    dsimp [δ]
    rw [show (K₀ : ℝ) * ((r : ℝ) / walshCard m) =
      ((K₀ : ℝ) * r) / walshCard m by ring]
    apply (div_le_iff₀ hnpos).2
    nlinarith [hκ']
  let base : ℝ := θ ^ 2 * η ^ 2 / 8
  have hbasepos : 0 < base := by
    dsimp [base]
    exact div_pos (mul_pos (sq_pos_of_pos hθ.1) hηsqpos) (by norm_num)
  have htraceBase : (K₀ : ℝ) * (δ * θ) ≤ base := by
    calc
      (K₀ : ℝ) * (δ * θ) = ((K₀ : ℝ) * δ) * θ := by ring
      _ ≤ (θ * η ^ 2 / 64) * θ :=
        mul_le_mul_of_nonneg_right hKdelta hθ.1.le
      _ ≤ base := by
        dsimp [base]
        nlinarith [mul_pos (sq_pos_of_pos hθ.1) hηsqpos]
  have ha2nonneg : 0 ≤ a2 := by
    dsimp [a2]
    have hδnonneg : 0 ≤ δ := by simpa [δ] using hδpos.le
    have hδone : δ ≤ 1 := (by simpa [δ] using hδhalf.trans (by norm_num))
    have hθone : θ ≤ 1 := hθ.2.trans (by norm_num)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hδnonneg (sub_nonneg.mpr hδone)) hθ.1.le)
      (sub_nonneg.mpr hθone)
  have ha2_le_delta_theta : a2 ≤ δ * θ := by
    dsimp [a2]
    have hδnonneg : 0 ≤ δ := by simpa [δ] using hδpos.le
    have hδone : δ ≤ 1 := by simpa [δ] using hδhalf.trans (by norm_num)
    have hθone : θ ≤ 1 := hθ.2.trans (by norm_num)
    have hδfactor0 : 0 ≤ 1 - δ := sub_nonneg.mpr hδone
    have hδfactor1 : 1 - δ ≤ 1 := by linarith
    have hθfactor0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθone
    have hθfactor1 : 1 - θ ≤ 1 := by linarith
    have hfactors : (1 - δ) * (1 - θ) ≤ 1 := by
      calc
        (1 - δ) * (1 - θ) ≤ 1 * (1 - θ) :=
          mul_le_mul_of_nonneg_right hδfactor1 hθfactor0
        _ ≤ 1 := by simpa using hθfactor1
    calc
      δ * (1 - δ) * θ * (1 - θ) =
          (δ * θ) * ((1 - δ) * (1 - θ)) := by ring
      _ ≤ (δ * θ) * 1 :=
        mul_le_mul_of_nonneg_left hfactors (mul_nonneg hδnonneg hθ.1.le)
      _ = δ * θ := by ring
  have hdeltaThetaBase : δ * θ ≤ base := by
    calc
      δ * θ ≤ (θ * η ^ 2 / 64) * θ :=
        mul_le_mul_of_nonneg_right hsmall hθ.1.le
      _ ≤ base := by
        dsimp [base]
        nlinarith [mul_pos (sq_pos_of_pos hθ.1) hηsqpos]
  have htracePow : (K₀ : ℝ) ^ p * (δ * θ) ^ p ≤ base ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity)
      (mul_nonneg (by simpa [δ] using hδpos.le) hθ.1.le)) htraceBase p
  have ha2Pow : a2 ^ p ≤ base ^ p :=
    pow_le_pow_left₀ ha2nonneg (ha2_le_delta_theta.trans hdeltaThetaBase) p
  have hbound :
      (K₀ : ℝ) ^ p * (δ * θ) ^ p + compensation ≤
        3 * (r : ℝ) * base ^ p := by
    have hrone : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hbasePow : 0 ≤ base ^ p := pow_nonneg hbasepos.le p
    dsimp only [compensation]
    nlinarith
  have hbaseEdge : base ^ p = (2 : ℝ) ^ (-(p : ℤ)) * edge := by
    have hbaseIdentity : (θ ^ 2 * η ^ 2 / 8) ^ p =
        (2 : ℝ) ^ (-(p : ℤ)) * (θ * η / 2) ^ (2 * p) := by
      have hbaseScalar : (θ ^ 2 * η ^ 2 / 8) =
          (2 : ℝ)⁻¹ * (θ * η / 2) ^ 2 := by
        field_simp
        ring
      calc
        _ = ((2 : ℝ)⁻¹ * (θ * η / 2) ^ 2) ^ p := by
          rw [hbaseScalar]
        _ = ((2 : ℝ)⁻¹) ^ p * ((θ * η / 2) ^ 2) ^ p :=
          mul_pow _ _ _
        _ = ((2 : ℝ) ^ p)⁻¹ * (θ * η / 2) ^ (2 * p) := by
          rw [inv_pow, pow_mul]
        _ = _ := by rw [zpow_neg, zpow_natCast]
    simpa only [base, edge] using hbaseIdentity
  have hedgepos : 0 < edge := by
    dsimp [edge]
    exact pow_pos (div_pos (mul_pos hθ.1 hη.1) (by norm_num)) _
  have hprob : signPairExpectation (fun d₁ d₂ ↦
      bernoulliProbability θ (bad d₁ d₂)) ≤
      (3 : ℝ) * r * 2 ^ (-(p : ℤ)) := by
    apply (mul_le_mul_iff_of_pos_right hedgepos).mp
    calc
      signPairExpectation (fun d₁ d₂ ↦
          bernoulliProbability θ (bad d₁ d₂)) * edge ≤
          (K₀ : ℝ) ^ p * (δ * θ) ^ p + compensation := hraw
      _ ≤ 3 * (r : ℝ) * base ^ p := hbound
      _ = ((3 : ℝ) * r * 2 ^ (-(p : ℤ))) * edge := by
        rw [hbaseEdge]
        ring
  have harithmetic : (3 : ℝ) * r * 2 ^ (-(p : ℤ)) ≤ 1 / 1000 :=
    bernoulli_failure_arithmetic p r (by omega)
  simpa only [bad] using hprob.trans harithmetic

#print axioms bernoulli_coordinate_sampling_corollary_of_trace

end Problem56
