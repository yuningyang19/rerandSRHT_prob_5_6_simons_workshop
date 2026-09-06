import Problem56.Definitions

/-!
Scalar arithmetic used by the repaired fixed-size sampling sandwich.  Keeping
these facts separate prevents the matrix-order proof from hiding endpoint or
constant changes.
-/

namespace Problem56

open scoped Matrix.Norms.L2Operator

theorem sampling_euclideanNorm_eq_norm_toLp
    {α : Type*} [Fintype α] (x : α → ℝ) :
    euclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sampling_euclideanOperatorNorm_eq_l2_opNorm
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α β ℝ) :
    euclideanOperatorNorm A = ‖A‖ := by
  let T : EuclideanSpace ℝ β →L[ℝ] EuclideanSpace ℝ α :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := α) (n := β)).trans
      LinearMap.toContinuousLinearMap A
  rw [euclideanOperatorNorm, Matrix.l2_opNorm_def]
  change sSup {z : ℝ | ∃ x : β → ℝ, euclideanNorm x = 1 ∧
    z = euclideanNorm (A.mulVec x)} = ‖T‖
  rw [← T.sSup_sphere_eq_norm]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · simpa [Metric.mem_sphere, sampling_euclideanNorm_eq_norm_toLp] using hx
    · simp [T, sampling_euclideanNorm_eq_norm_toLp]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · simpa [Metric.mem_sphere, sampling_euclideanNorm_eq_norm_toLp] using hx
    · rw [sampling_euclideanNorm_eq_norm_toLp]
      change ‖(Matrix.toEuclideanLin A) x‖ =
        ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖
      exact congrArg norm (Matrix.toLpLin_apply 2 2 A x)

theorem sampling_quadraticForm_eq_reApplyInnerSelf
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (x : α → ℝ) :
    quadraticForm A x =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).reApplyInnerSelf
        (WithLp.toLp 2 x) := by
  rw [quadraticForm]
  change x ⬝ᵥ A.mulVec x = _
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [RCLike.re_to_real]
  rw [real_inner_comm]
  exact (Matrix.inner_toEuclideanCLM A
    (WithLp.toLp 2 x) (WithLp.toLp 2 x)).symm

/-- For a real symmetric matrix, a homogeneous absolute quadratic-form bound
controls the Euclidean operator norm with the same constant. -/
theorem sampling_euclideanOperatorNorm_le_of_quadraticForm_abs_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : A.IsHermitian) (η : ℝ) (hη : 0 ≤ η)
    (hquad : ∀ x : α → ℝ,
      |quadraticForm A x| ≤ η * ∑ i, (x i) ^ 2) :
    euclideanOperatorNorm A ≤ η := by
  rw [sampling_euclideanOperatorNorm_eq_l2_opNorm, Matrix.cstar_norm_def]
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  change ‖T‖ ≤ η
  have hsym : T.IsSymmetric := by
    change (Matrix.toEuclideanLin A).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [T.norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hη
  rw [ContinuousLinearMap.rayleighQuotient, abs_div,
    abs_of_nonneg (sq_nonneg ‖x‖)]
  apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).2
  rw [← sampling_quadraticForm_eq_reApplyInnerSelf A (WithLp.ofLp x)]
  simpa only [EuclideanSpace.real_norm_sq_eq] using hquad (WithLp.ofLp x)

theorem sampling_abs_quadraticForm_le_operatorNorm_mul_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (x : α → ℝ) :
    |quadraticForm A x| ≤
      euclideanOperatorNorm A * ∑ i, (x i) ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [quadraticForm, euclideanInner]
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hxLp : WithLp.toLp 2 x ≠ 0 := by
    intro hzero
    apply hx
    exact congrArg WithLp.ofLp hzero
  have h := T.rayleighQuotient_le_norm (WithLp.toLp 2 x)
  rw [ContinuousLinearMap.rayleighQuotient, abs_div,
    abs_of_nonneg (sq_nonneg ‖WithLp.toLp 2 x‖)] at h
  have hsquare : 0 < ‖WithLp.toLp 2 x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hxLp)
  have hmul := (div_le_iff₀ hsquare).mp h
  rw [← sampling_quadraticForm_eq_reApplyInnerSelf A x,
    Matrix.l2_opNorm_toEuclideanCLM,
    ← sampling_euclideanOperatorNorm_eq_l2_opNorm,
    EuclideanSpace.real_norm_sq_eq] at hmul
  exact hmul

theorem quadraticForm_sub
    {α : Type*} [Fintype α] (A B : Matrix α α ℝ) (x : α → ℝ) :
    quadraticForm (A - B) x = quadraticForm A x - quadraticForm B x := by
  classical
  unfold quadraticForm
  change x ⬝ᵥ (A - B).mulVec x =
    x ⬝ᵥ A.mulVec x - x ⬝ᵥ B.mulVec x
  rw [Matrix.sub_mulVec, dotProduct_sub]

theorem quadraticForm_one
    {α : Type*} [Fintype α] [DecidableEq α] (x : α → ℝ) :
    quadraticForm (1 : Matrix α α ℝ) x = ∑ i, (x i) ^ 2 := by
  classical
  simp [quadraticForm, euclideanInner, pow_two]

theorem fixedSampleGram_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k) :
    (fixedSampleGram X J).IsHermitian := by
  unfold fixedSampleGram
  have hprojection : (coordinateProjection J).IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have hcore :
      (X.transpose * coordinateProjection J * X).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul X hprojection
  exact hcore.smul (IsSelfAdjoint.all _)

theorem bernoulliGram_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (θ : ℝ) (X : Matrix α (Fin r) ℝ) (e : SignLayer α) :
    (bernoulliGram θ X e).IsHermitian := by
  unfold bernoulliGram
  have hprojection : (bernoulliProjection e).IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have hcore :
      (X.transpose * bernoulliProjection e * X).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul X hprojection
  exact hcore.smul (IsSelfAdjoint.all _)

theorem quadraticForm_transpose_diagonal_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (X : Matrix α β ℝ) (w : α → ℝ) (x : β → ℝ) :
    quadraticForm (X.transpose * Matrix.diagonal w * X) x =
      ∑ i, w i * (X.mulVec x i) ^ 2 := by
  classical
  unfold quadraticForm
  change x ⬝ᵥ (X.transpose * Matrix.diagonal w * X).mulVec x = _
  rw [Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec x X.transpose (Matrix.diagonal w * X),
    ← Matrix.mulVec_mulVec x (Matrix.diagonal w) X,
    Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticForm_smul
    {α : Type*} [Fintype α] (c : ℝ) (A : Matrix α α ℝ)
    (x : α → ℝ) :
    quadraticForm (c • A) x = c * quadraticForm A x := by
  classical
  simp [quadraticForm, euclideanInner, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_comm, mul_left_comm]

theorem quadraticForm_fixedSampleGram_eq
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k) (x : Fin r → ℝ) :
    quadraticForm (fixedSampleGram X J) x =
      ((Fintype.card α : ℝ) / (k : ℝ)) *
        ∑ i, if i ∈ J.1 then (X.mulVec x i) ^ 2 else 0 := by
  rw [fixedSampleGram, quadraticForm_smul, coordinateProjection,
    quadraticForm_transpose_diagonal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ J.1 <;> simp [hi]

theorem quadraticForm_bernoulliGram_eq
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (θ : ℝ) (X : Matrix α (Fin r) ℝ) (e : SignLayer α)
    (x : Fin r → ℝ) :
    quadraticForm (bernoulliGram θ X e) x =
      θ⁻¹ * ∑ i, if e i = true then (X.mulVec x i) ^ 2 else 0 := by
  rw [bernoulliGram, quadraticForm_smul, bernoulliProjection,
    quadraticForm_transpose_diagonal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : e i = true <;> simp [hi]

theorem sum_indicator_le_of_imp
    {α : Type*} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (f : α → ℝ)
    (hpq : ∀ i, p i → q i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, if p i then f i else 0) ≤ ∑ i, if q i then f i else 0 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hpi : p i
  · simp [hpi, hpq i hpi]
  · by_cases hqi : q i <;> simp [hpi, hqi, hf i]

/-- The coordinate inclusions in the nested sampling coupling give the exact
quadratic-form sandwich, with the Bernoulli normalizations cancelling against
the factors `1 ± ε / 4`. -/
theorem sampling_quadratic_form_sandwich
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k)
    (bminus bplus : SignLayer α) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hminus : ∀ i, bminus i = true → i ∈ J.1)
    (hplus : ∀ i, i ∈ J.1 → bplus i = true) :
    let α₀ := ε / 4
    let θminus := (1 - α₀) * k / Fintype.card α
    let θplus := (1 + α₀) * k / Fintype.card α
    ∀ x, (1 - α₀) * quadraticForm (bernoulliGram θminus X bminus) x ≤
        quadraticForm (fixedSampleGram X J) x ∧
      quadraticForm (fixedSampleGram X J) x ≤
        (1 + α₀) * quadraticForm (bernoulliGram θplus X bplus) x := by
  classical
  dsimp only
  intro x
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk.1
  have hcardNat : 0 < Fintype.card α := lt_of_lt_of_le hk.1 hk.2
  have hcard : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hcardNat
  have hminusFactor : 0 < 1 - ε / 4 := by linarith
  have hplusFactor : 0 < 1 + ε / 4 := by linarith
  have hcoefMinus :
      (1 - ε / 4) * (((1 - ε / 4) * (k : ℝ) /
        (Fintype.card α : ℝ))⁻¹) =
        (Fintype.card α : ℝ) / (k : ℝ) := by
    field_simp
    apply div_self
    linarith
  have hcoefPlus :
      (1 + ε / 4) * (((1 + ε / 4) * (k : ℝ) /
        (Fintype.card α : ℝ))⁻¹) =
        (Fintype.card α : ℝ) / (k : ℝ) := by
    field_simp
    apply div_self
    linarith
  have hscale : 0 ≤ (Fintype.card α : ℝ) / (k : ℝ) := by positivity
  let y : α → ℝ := X.mulVec x
  have hsumMinus :
      (∑ i, if bminus i = true then y i ^ 2 else 0) ≤
        ∑ i, if i ∈ J.1 then y i ^ 2 else 0 :=
    sum_indicator_le_of_imp
      (fun i ↦ bminus i = true) (fun i ↦ i ∈ J.1)
      (fun i ↦ y i ^ 2) hminus (fun i ↦ sq_nonneg (y i))
  have hsumPlus :
      (∑ i, if i ∈ J.1 then y i ^ 2 else 0) ≤
        ∑ i, if bplus i = true then y i ^ 2 else 0 :=
    sum_indicator_le_of_imp
      (fun i ↦ i ∈ J.1) (fun i ↦ bplus i = true)
      (fun i ↦ y i ^ 2) hplus (fun i ↦ sq_nonneg (y i))
  rw [quadraticForm_bernoulliGram_eq,
    quadraticForm_fixedSampleGram_eq,
    quadraticForm_bernoulliGram_eq]
  change
    (1 - ε / 4) *
        (((1 - ε / 4) * (k : ℝ) / (Fintype.card α : ℝ))⁻¹ *
          (∑ i, if bminus i = true then y i ^ 2 else 0)) ≤
      (Fintype.card α : ℝ) / (k : ℝ) *
          (∑ i, if i ∈ J.1 then y i ^ 2 else 0) ∧
    (Fintype.card α : ℝ) / (k : ℝ) *
          (∑ i, if i ∈ J.1 then y i ^ 2 else 0) ≤
      (1 + ε / 4) *
        (((1 + ε / 4) * (k : ℝ) / (Fintype.card α : ℝ))⁻¹ *
          (∑ i, if bplus i = true then y i ^ 2 else 0))
  constructor
  · rw [← mul_assoc, hcoefMinus]
    exact mul_le_mul_of_nonneg_left hsumMinus hscale
  · rw [← mul_assoc, hcoefPlus]
    exact mul_le_mul_of_nonneg_left hsumPlus hscale

/-- The two Bernoulli spectral events convert the quadratic sandwich into the
fixed-sample spectral event without loss beyond the frozen `ε / 4` constants. -/
theorem sampling_sandwich_operatorNorm_conversion
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k)
    (bminus bplus : SignLayer α) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hminus : ∀ i, bminus i = true → i ∈ J.1)
    (hplus : ∀ i, i ∈ J.1 → bplus i = true) :
    let α₀ := ε / 4
    let θminus := (1 - α₀) * k / Fintype.card α
    let θplus := (1 + α₀) * k / Fintype.card α
    euclideanOperatorNorm (bernoulliGram θminus X bminus - 1) ≤ α₀ →
      euclideanOperatorNorm (bernoulliGram θplus X bplus - 1) ≤ α₀ →
      euclideanOperatorNorm (fixedSampleGram X J - 1) ≤ ε := by
  classical
  dsimp only
  intro hnormMinus hnormPlus
  have hα₀ : 0 ≤ ε / 4 := by linarith
  have hminusFactor : 0 ≤ 1 - ε / 4 := by linarith
  have hplusFactor : 0 ≤ 1 + ε / 4 := by linarith
  have hsquare :
      1 - ε ≤ (1 - ε / 4) ^ 2 ∧
        (1 + ε / 4) ^ 2 ≤ 1 + ε := by
    constructor <;> nlinarith [sq_nonneg ε]
  have hsandwich := sampling_quadratic_form_sandwich
    X J bminus bplus ε hε hk hminus hplus
  apply sampling_euclideanOperatorNorm_le_of_quadraticForm_abs_le
    (fixedSampleGram X J - 1)
    ((fixedSampleGram_isHermitian X J).sub Matrix.isHermitian_one)
    ε hε.1.le
  intro x
  let sx : ℝ := ∑ i, (x i) ^ 2
  have hsx : 0 ≤ sx := Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)
  have habsMinus :
      |quadraticForm (bernoulliGram
          ((1 - ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bminus) x - sx| ≤
        (ε / 4) * sx := by
    calc
      _ = |quadraticForm
          (bernoulliGram
            ((1 - ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bminus - 1) x| := by
        rw [quadraticForm_sub, quadraticForm_one]
      _ ≤ euclideanOperatorNorm
          (bernoulliGram
            ((1 - ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bminus - 1) * sx :=
        sampling_abs_quadraticForm_le_operatorNorm_mul_sq _ x
      _ ≤ (ε / 4) * sx :=
        mul_le_mul_of_nonneg_right hnormMinus hsx
  have habsPlus :
      |quadraticForm (bernoulliGram
          ((1 + ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bplus) x - sx| ≤
        (ε / 4) * sx := by
    calc
      _ = |quadraticForm
          (bernoulliGram
            ((1 + ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bplus - 1) x| := by
        rw [quadraticForm_sub, quadraticForm_one]
      _ ≤ euclideanOperatorNorm
          (bernoulliGram
            ((1 + ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bplus - 1) * sx :=
        sampling_abs_quadraticForm_le_operatorNorm_mul_sq _ x
      _ ≤ (ε / 4) * sx :=
        mul_le_mul_of_nonneg_right hnormPlus hsx
  have hgramMinus :
      (1 - ε / 4) * sx ≤
        quadraticForm (bernoulliGram
          ((1 - ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bminus) x := by
    have hnegative := (abs_le.mp habsMinus).1
    linarith
  have hgramPlus :
      quadraticForm (bernoulliGram
          ((1 + ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bplus) x ≤
        (1 + ε / 4) * sx := by
    have hpositive := (abs_le.mp habsPlus).2
    linarith
  have hfixedLower :
      (1 - ε) * sx ≤ quadraticForm (fixedSampleGram X J) x := by
    calc
      (1 - ε) * sx ≤ (1 - ε / 4) ^ 2 * sx :=
        mul_le_mul_of_nonneg_right hsquare.1 hsx
      _ = (1 - ε / 4) * ((1 - ε / 4) * sx) := by ring
      _ ≤ (1 - ε / 4) *
          quadraticForm (bernoulliGram
            ((1 - ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bminus) x :=
        mul_le_mul_of_nonneg_left hgramMinus hminusFactor
      _ ≤ quadraticForm (fixedSampleGram X J) x :=
        (hsandwich x).1
  have hfixedUpper :
      quadraticForm (fixedSampleGram X J) x ≤ (1 + ε) * sx := by
    calc
      quadraticForm (fixedSampleGram X J) x ≤
          (1 + ε / 4) *
            quadraticForm (bernoulliGram
              ((1 + ε / 4) * (k : ℝ) / (Fintype.card α : ℝ)) X bplus) x :=
        (hsandwich x).2
      _ ≤ (1 + ε / 4) * ((1 + ε / 4) * sx) :=
        mul_le_mul_of_nonneg_left hgramPlus hplusFactor
      _ = (1 + ε / 4) ^ 2 * sx := by ring
      _ ≤ (1 + ε) * sx :=
        mul_le_mul_of_nonneg_right hsquare.2 hsx
  rw [quadraticForm_sub, quadraticForm_one]
  change |quadraticForm (fixedSampleGram X J) x - sx| ≤ ε * sx
  apply abs_le.mpr
  constructor <;> linarith

theorem sampling_square_bounds (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    1 - ε ≤ (1 - ε / 4) ^ 2 ∧ (1 + ε / 4) ^ 2 ≤ 1 + ε := by
  constructor <;> nlinarith [sq_nonneg ε]

/-- Exact kernel package matching the frozen `I36` conclusion. -/
theorem sampling_sandwich_spectral_conversion
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k)
    (bminus bplus : SignLayer α) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hminus : ∀ i, bminus i = true → i ∈ J.1)
    (hplus : ∀ i, i ∈ J.1 → bplus i = true) :
    let α₀ := ε / 4
    let θminus := (1 - α₀) * k / Fintype.card α
    let θplus := (1 + α₀) * k / Fintype.card α
    (∀ x, (1 - α₀) * quadraticForm (bernoulliGram θminus X bminus) x ≤
        quadraticForm (fixedSampleGram X J) x ∧
      quadraticForm (fixedSampleGram X J) x ≤
        (1 + α₀) * quadraticForm (bernoulliGram θplus X bplus) x) ∧
    (euclideanOperatorNorm (bernoulliGram θminus X bminus - 1) ≤ α₀ →
      euclideanOperatorNorm (bernoulliGram θplus X bplus - 1) ≤ α₀ →
      euclideanOperatorNorm (fixedSampleGram X J - 1) ≤ ε) ∧
    1 - ε ≤ (1 - α₀) ^ 2 ∧ (1 + α₀) ^ 2 ≤ 1 + ε := by
  dsimp only
  refine ⟨?_, ?_, sampling_square_bounds ε hε⟩
  · simpa only using
      sampling_quadratic_form_sandwich
        X J bminus bplus ε hε hk hminus hplus
  · simpa only using
      sampling_sandwich_operatorNorm_conversion
        X J bminus bplus ε hε hk hminus hplus

theorem sampling_density_order
    (n k : ℕ) (α : ℝ) (hα : 0 ≤ α) (hk : k ≤ n) :
    (1 - α) * (k : ℝ) / n ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ (1 + α) * (k : ℝ) / n := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  by_cases hn : n = 0
  · subst n
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    norm_num
  · have hn0 : 0 < (n : ℝ) := by positivity
    constructor
    · apply (div_le_div_iff_of_pos_right hn0).2
      nlinarith
    · apply (div_le_div_iff_of_pos_right hn0).2
      nlinarith

#print axioms sampling_square_bounds
#print axioms sampling_density_order
#print axioms sampling_sandwich_spectral_conversion

end Problem56
