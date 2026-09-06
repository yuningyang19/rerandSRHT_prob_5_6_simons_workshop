import Problem56.FinitePopulationMoment
import Problem56.RademacherFourthMoment
import Problem56.ProbabilityFrobenius

/-!
The source-faithful small-rank branch: finite-population second moments,
Rademacher fourth moments, and the finite uniform Markov bound.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

private theorem smallRank_normalizedWalsh_transpose (m : ℕ) :
    (normalizedWalsh m).transpose = normalizedWalsh m := by
  ext a b
  simp only [Matrix.transpose_apply, normalizedWalsh, walshCharacter_comm' b a]

private theorem smallRank_normalizedWalsh_mul_self (m : ℕ) :
    normalizedWalsh m * normalizedWalsh m = 1 := by
  classical
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  ext a b
  simp only [Matrix.mul_apply, normalizedWalsh, Matrix.one_apply]
  calc
    (∑ x, walshCharacter a x / Real.sqrt (walshCard m : ℝ) *
        (walshCharacter x b / Real.sqrt (walshCard m : ℝ))) =
        (∑ x, walshCharacter a x * walshCharacter b x) /
          (walshCard m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [walshCharacter_comm' x b]
      field_simp
      rw [Real.sq_sqrt hcard.le]
      ring
    _ = if a = b then 1 else 0 := by
      rw [sum_walshCharacter_pair]
      split_ifs
      · exact div_self hcard.ne'
      · exact zero_div _

private theorem smallRank_signDiagonal_mul_self
    {α : Type*} [Fintype α] [DecidableEq α] (d : SignLayer α) :
    signDiagonal d * signDiagonal d = (1 : Matrix α α ℝ) := by
  simp only [signDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact signValue_mul_self d i

theorem transformedFrame_orthonormal
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (d₁ d₂ : SignLayer (WalshIndex m)) :
    OrthonormalFrame (transformedFrame d₁ d₂ V) := by
  have hD₁ : Matrix.diagonal (signValue d₁) *
      Matrix.diagonal (signValue d₁) = 1 :=
    smallRank_signDiagonal_mul_self d₁
  have hD₂ : Matrix.diagonal (signValue d₂) *
      Matrix.diagonal (signValue d₂) = 1 :=
    smallRank_signDiagonal_mul_self d₂
  simp only [OrthonormalFrame, transformedFrame, Matrix.transpose_mul,
    signDiagonal, Matrix.diagonal_transpose, smallRank_normalizedWalsh_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (normalizedWalsh m) (normalizedWalsh m),
    smallRank_normalizedWalsh_mul_self]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal (signValue d₂)), hD₂]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (normalizedWalsh m),
    smallRank_normalizedWalsh_mul_self]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal (signValue d₁)), hD₁]
  simpa [OrthonormalFrame] using hV

private theorem singleWalshSignFrame_orthonormal
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (d : SignLayer (WalshIndex m)) :
    OrthonormalFrame (normalizedWalsh m * signDiagonal d * V) := by
  have hD : Matrix.diagonal (signValue d) *
      Matrix.diagonal (signValue d) = 1 :=
    smallRank_signDiagonal_mul_self d
  simp only [OrthonormalFrame, Matrix.transpose_mul, signDiagonal,
    Matrix.diagonal_transpose, smallRank_normalizedWalsh_transpose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (normalizedWalsh m) (normalizedWalsh m),
    smallRank_normalizedWalsh_mul_self]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal (signValue d)), hD]
  simpa [OrthonormalFrame] using hV

private theorem uniformExpectation_modulate
    {m : ℕ} (i : WalshIndex m) (F : SignLayer (WalshIndex m) → ℝ) :
    uniformExpectation (fun d ↦ F (modulateSign i d)) = uniformExpectation F := by
  classical
  let e : Equiv.Perm (SignLayer (WalshIndex m)) :=
    (modulateSign_involutive i).toPerm (modulateSign i)
  simp only [uniformExpectation]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

private theorem transformedFrame_row_eq_rademacher
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (i : WalshIndex m) (a : Fin r) :
    transformedFrame d₁ d₂ V i a =
      (1 / Real.sqrt (walshCard m : ℝ)) *
        ∑ j, signValue (modulateSign i d₂) j *
          (normalizedWalsh m * signDiagonal d₁ * V) j a := by
  classical
  rw [show transformedFrame d₁ d₂ V =
      normalizedWalsh m * (signDiagonal d₂ *
        (normalizedWalsh m * signDiagonal d₁ * V)) by
    simp only [transformedFrame, Matrix.mul_assoc]]
  rw [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hdiag :
      (signDiagonal d₂ *
          (normalizedWalsh m * signDiagonal d₁ * V)) j a =
        signValue d₂ j *
          (normalizedWalsh m * signDiagonal d₁ * V) j a := by
    simp [signDiagonal, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [hdiag, normalizedWalsh, signValue_modulate]
  ring

private theorem euclideanNorm_pow_four_eq_sum_sq
    {α : Type*} [Fintype α] (z : α → ℝ) :
    euclideanNorm z ^ 4 = (∑ a, (z a) ^ 2) ^ 2 := by
  have hsum : 0 ≤ ∑ a, (z a) ^ 2 :=
    Finset.sum_nonneg (fun a _ ↦ sq_nonneg (z a))
  rw [euclideanNorm, show 4 = 2 * 2 by norm_num, pow_mul,
    Real.sq_sqrt hsum]

private theorem transformedFrame_row_energy_sq
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (i : WalshIndex m) :
    (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2 =
      (1 / (walshCard m : ℝ) ^ 2) *
        (euclideanNorm (fun a ↦ ∑ j,
          signValue (modulateSign i d₂) j *
            (normalizedWalsh m * signDiagonal d₁ * V) j a)) ^ 4 := by
  classical
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  let z : Fin r → ℝ := fun a ↦ ∑ j,
    signValue (modulateSign i d₂) j *
      (normalizedWalsh m * signDiagonal d₁ * V) j a
  have hrow (a : Fin r) :
      transformedFrame d₁ d₂ V i a =
        (1 / Real.sqrt (walshCard m : ℝ)) * z a :=
    transformedFrame_row_eq_rademacher V d₁ d₂ i a
  have hsum :
      (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) =
        (1 / Real.sqrt (walshCard m : ℝ)) ^ 2 *
          ∑ a, (z a) ^ 2 := by
    simp_rw [hrow, mul_pow]
    rw [Finset.mul_sum]
  rw [hsum, mul_pow, euclideanNorm_pow_four_eq_sum_sq]
  change
    ((1 / Real.sqrt (walshCard m : ℝ)) ^ 2) ^ 2 *
        (∑ a, (z a) ^ 2) ^ 2 =
      1 / (walshCard m : ℝ) ^ 2 * (∑ a, (z a) ^ 2) ^ 2
  congr 1
  rw [div_pow, one_pow, Real.sq_sqrt hcard.le]
  ring

theorem transformedFrame_row_fourth_moment_bound
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (d₁ : SignLayer (WalshIndex m))
    (i : WalshIndex m) :
    uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
      (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2) ≤
      ((r : ℝ) ^ 2 + 2 * r) / (walshCard m : ℝ) ^ 2 := by
  let U := normalizedWalsh m * signDiagonal d₁ * V
  have hU : OrthonormalFrame U := singleWalshSignFrame_orthonormal V hV d₁
  have hfactor : 0 ≤ 1 / (walshCard m : ℝ) ^ 2 := by positivity
  calc
    uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
        (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2) =
        (1 / (walshCard m : ℝ) ^ 2) *
          uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
            (euclideanNorm (fun a ↦ ∑ j,
              signValue (modulateSign i d₂) j * U j a)) ^ 4) := by
      simp_rw [transformedFrame_row_energy_sq V]
      exact uniformExpectation_const_mul _ _
    _ = (1 / (walshCard m : ℝ) ^ 2) *
          uniformExpectation (fun ξ : SignLayer (WalshIndex m) ↦
            (euclideanNorm (fun a ↦ ∑ j,
              signValue ξ j * U j a)) ^ 4) := by
      congr 1
      simpa only using uniformExpectation_modulate i
        (fun ξ : SignLayer (WalshIndex m) ↦
          (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4)
    _ ≤ (1 / (walshCard m : ℝ) ^ 2) *
          ((r : ℝ) ^ 2 + 2 * r) :=
      mul_le_mul_of_nonneg_left (rademacher_vector_fourth_moment U hU).2 hfactor
    _ = ((r : ℝ) ^ 2 + 2 * r) / (walshCard m : ℝ) ^ 2 := by ring

private theorem uniformExpectation_prod_iterated
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] (F : Ω₁ → Ω₂ → ℝ) :
    uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1 z.2) =
      uniformExpectation (fun x ↦ uniformExpectation (F x)) := by
  classical
  have hcard₁ : (Fintype.card Ω₁ : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω₁ ≠ 0)
  have hcard₂ : (Fintype.card Ω₂ : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω₂ ≠ 0)
  simp only [uniformExpectation, Fintype.sum_prod_type, Fintype.card_prod]
  push_cast
  rw [← Finset.sum_div]
  field_simp

private theorem uniformExpectation_mono
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] {F G : Ω → ℝ}
    (h : ∀ ω, F ω ≤ G ω) : uniformExpectation F ≤ uniformExpectation G := by
  have hcard : 0 ≤ (Fintype.card Ω : ℝ) := by positivity
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun ω _ ↦ h ω)) hcard

private theorem uniformExpectation_const_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformExpectation (fun _ : Ω ↦ c) = c := by
  classical
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  simp [uniformExpectation, hcard]

theorem transformedFrame_average_leverage_sq_bound
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) :
    signPairExpectation (fun d₁ d₂ ↦
      ∑ i, (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2) ≤
      ((r : ℝ) ^ 2 + 2 * r) / walshCard m := by
  let C : ℝ := ((r : ℝ) ^ 2 + 2 * r) / (walshCard m : ℝ) ^ 2
  let B : ℝ := ((r : ℝ) ^ 2 + 2 * r) / (walshCard m : ℝ)
  have hinner (d₁ : SignLayer (WalshIndex m)) :
      uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
        ∑ i, (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2) ≤ B := by
    rw [uniformExpectation_sum]
    calc
      (∑ i, uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
          (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2)) ≤
          ∑ _i : WalshIndex m, C := by
        apply Finset.sum_le_sum
        intro i _
        exact transformedFrame_row_fourth_moment_bound V hV d₁ i
      _ = B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp only [B, C]
        have hcard : (walshCard m : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero : walshCard m ≠ 0)
        field_simp
        change (walshCard m : ℝ) * (r : ℝ) =
          (r : ℝ) * (walshCard m : ℝ)
        ring
  rw [signPairExpectation,
    uniformExpectation_prod_iterated
      (fun d₁ d₂ ↦ ∑ i,
        (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2)]
  calc
    uniformExpectation (fun d₁ : SignLayer (WalshIndex m) ↦
        uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
          ∑ i, (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2)) ≤
        uniformExpectation (fun _ : SignLayer (WalshIndex m) ↦ B) :=
      uniformExpectation_mono hinner
    _ = B := uniformExpectation_const_eq B
    _ = _ := rfl

private theorem uniformExpectation_triple_iterated
    {Ω₁ Ω₂ Ω₃ : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype Ω₃]
    [Nonempty Ω₁] [Nonempty Ω₂] [Nonempty Ω₃]
    (F : Ω₁ → Ω₂ → Ω₃ → ℝ) :
    uniformExpectation (fun z : Ω₁ × Ω₂ × Ω₃ ↦ F z.1 z.2.1 z.2.2) =
      uniformExpectation (fun x ↦
        uniformExpectation (fun y ↦ uniformExpectation (F x y))) := by
  calc
    uniformExpectation (fun z : Ω₁ × Ω₂ × Ω₃ ↦ F z.1 z.2.1 z.2.2) =
        uniformExpectation (fun x : Ω₁ ↦
          uniformExpectation (fun yz : Ω₂ × Ω₃ ↦ F x yz.1 yz.2)) :=
      uniformExpectation_prod_iterated (Ω₁ := Ω₁) (Ω₂ := Ω₂ × Ω₃)
        (fun x yz ↦ F x yz.1 yz.2)
    _ = uniformExpectation (fun x : Ω₁ ↦
          uniformExpectation (fun y : Ω₂ ↦ uniformExpectation (F x y))) := by
      congr 1
      funext x
      exact uniformExpectation_prod_iterated
        (Ω₁ := Ω₂) (Ω₂ := Ω₃) (F x)

theorem fixedSampleGram_full_eq_one
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {r : ℕ} (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X)
    (J : FixedSubset α (Fintype.card α)) :
    fixedSampleGram X J = 1 := by
  classical
  have hJ : J.1 = Finset.univ := by
    apply (Finset.card_eq_iff_eq_univ J.1).mp
    exact J.2
  have hP : coordinateProjection J = (1 : Matrix α α ℝ) := by
    ext i j
    simp [coordinateProjection, Matrix.diagonal_apply, Matrix.one_apply, hJ]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  rw [fixedSampleGram, hP, div_self hcard, one_smul, Matrix.mul_one, hX]

theorem small_rank_frobenius_expectation_bound
    {m r k : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (hk : 1 ≤ k ∧ k ≤ walshCard m) :
    uniformExpectation
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k)
      (fun sample ↦ frobeniusNormSq
        (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) ≤
      (r : ℝ) * (r + 1) / k := by
  classical
  by_cases hone : walshCard m = 1
  · have hkone : k = walshCard m := by omega
    subst k
    have hzero : (fun sample :
          SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
            FixedSubset (WalshIndex m) (walshCard m) ↦
          frobeniusNormSq
            (fixedSampleGram
              (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) =
        fun _ ↦ 0 := by
      funext sample
      have hfull := fixedSampleGram_full_eq_one
        (transformedFrame sample.1 sample.2.1 V)
        (transformedFrame_orthonormal V hV sample.1 sample.2.1) sample.2.2
      have hdiff : fixedSampleGram
            (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1 = 0 :=
        sub_eq_zero.mpr hfull
      calc
        frobeniusNormSq
            (fixedSampleGram
              (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1) =
            frobeniusNormSq (0 : Matrix (Fin r) (Fin r) ℝ) :=
          congrArg frobeniusNormSq hdiff
        _ = 0 := by simp [frobeniusNormSq]
    rw [hzero]
    simp [uniformExpectation]
    positivity
  · have hnNat : 1 < walshCard m := by
      have hpos : 0 < walshCard m := Fintype.card_pos
      omega
    let factor : ℝ := ((walshCard m - k : ℕ) : ℝ) /
      ((k : ℝ) * (walshCard m - 1 : ℕ))
    let S : SignLayer (WalshIndex m) → SignLayer (WalshIndex m) → ℝ :=
      fun d₁ d₂ ↦
        ∑ i, (∑ a, (transformedFrame d₁ d₂ V i a) ^ 2) ^ 2
    have hpoint (d₁ d₂ : SignLayer (WalshIndex m)) :
        uniformExpectation (Ω := FixedSubset (WalshIndex m) k) (fun J ↦
          frobeniusNormSq (fixedSampleGram (transformedFrame d₁ d₂ V) J - 1)) =
        factor * ((walshCard m : ℝ) * S d₁ d₂ - r) := by
      exact finite_population_second_moment_identity
        (transformedFrame d₁ d₂ V)
        (transformedFrame_orthonormal V hV d₁ d₂) hnNat hk.1 hk.2
    have hkcard : k ≤ Fintype.card (WalshIndex m) := hk.2
    have hkuniv : k ≤ (Finset.univ : Finset (WalshIndex m)).card := by
      simpa only [Finset.card_univ] using hkcard
    obtain ⟨J₀, _, hJ₀⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (WalshIndex m)))
        hkuniv
    letI : Nonempty (FixedSubset (WalshIndex m) k) := ⟨⟨J₀, hJ₀⟩⟩
    have htotal :
        uniformExpectation
          (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
            FixedSubset (WalshIndex m) k)
          (fun sample ↦ frobeniusNormSq
            (fixedSampleGram
              (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) =
        factor * ((walshCard m : ℝ) * signPairExpectation S - r) := by
      calc
        uniformExpectation
            (fun sample : SignLayer (WalshIndex m) ×
                SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) k ↦
              frobeniusNormSq
                (fixedSampleGram
                  (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) =
            uniformExpectation (fun d₁ : SignLayer (WalshIndex m) ↦
              uniformExpectation (fun d₂ : SignLayer (WalshIndex m) ↦
                uniformExpectation (fun J : FixedSubset (WalshIndex m) k ↦
                  frobeniusNormSq
                    (fixedSampleGram (transformedFrame d₁ d₂ V) J - 1)))) :=
          uniformExpectation_triple_iterated
            (Ω₁ := SignLayer (WalshIndex m))
            (Ω₂ := SignLayer (WalshIndex m))
            (Ω₃ := FixedSubset (WalshIndex m) k)
            (fun d₁ d₂ J ↦ frobeniusNormSq
              (fixedSampleGram (transformedFrame d₁ d₂ V) J - 1))
        _ = signPairExpectation
            (fun d₁ d₂ ↦ factor * ((walshCard m : ℝ) * S d₁ d₂ - r)) := by
          simp_rw [hpoint]
          unfold signPairExpectation
          exact (uniformExpectation_prod_iterated _).symm
        _ = factor * ((walshCard m : ℝ) * signPairExpectation S - r) := by
          rw [signPairExpectation_const_mul, signPairExpectation_sub_const,
            signPairExpectation_const_mul]
    rw [htotal]
    have hnR : (1 : ℝ) < walshCard m := by
      simpa only [Nat.cast_one] using
        (Nat.cast_lt.mpr hnNat : ((1 : ℕ) : ℝ) < (walshCard m : ℝ))
    have hkR : (1 : ℝ) ≤ k := by
      simpa only [Nat.cast_one] using
        (Nat.cast_le.mpr hk.1 : ((1 : ℕ) : ℝ) ≤ (k : ℝ))
    have hknR : (k : ℝ) ≤ walshCard m := Nat.cast_le.mpr hk.2
    have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hkR
    have hnsub : (0 : ℝ) < (walshCard m - 1 : ℕ) := by
      exact Nat.cast_pos.mpr (by omega : 0 < walshCard m - 1)
    have hfactor0 : 0 ≤ factor := by
      dsimp only [factor]
      positivity
    have hfactor_le : factor ≤ 1 / (k : ℝ) := by
      dsimp only [factor]
      have hratio :
          ((walshCard m - k : ℕ) : ℝ) /
              ((walshCard m - 1 : ℕ) : ℝ) ≤ 1 := by
        apply (div_le_one hnsub).2
        exact_mod_cast (by omega : walshCard m - k ≤ walshCard m - 1)
      calc
        ((walshCard m - k : ℕ) : ℝ) /
              ((k : ℝ) * (walshCard m - 1 : ℕ)) =
            (1 / (k : ℝ)) *
              (((walshCard m - k : ℕ) : ℝ) /
                ((walshCard m - 1 : ℕ) : ℝ)) := by ring
        _ ≤ (1 / (k : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 1 / (k : ℝ) := by ring
    have hS := transformedFrame_average_leverage_sq_bound V hV
    have hscaledS :
        (walshCard m : ℝ) * signPairExpectation S ≤
          (r : ℝ) ^ 2 + 2 * r := by
      have hh := (le_div_iff₀ (show (0 : ℝ) < walshCard m by linarith)).mp hS
      simpa only [S, mul_comm] using hh
    have hinner :
        (walshCard m : ℝ) * signPairExpectation S - r ≤
          (r : ℝ) ^ 2 + r := by linarith
    calc
      factor * ((walshCard m : ℝ) * signPairExpectation S - r) ≤
          factor * ((r : ℝ) ^ 2 + r) :=
        mul_le_mul_of_nonneg_left hinner hfactor0
      _ ≤ (1 / (k : ℝ)) * ((r : ℝ) ^ 2 + r) :=
        mul_le_mul_of_nonneg_right hfactor_le (by positivity)
      _ = (r : ℝ) * (r + 1) / k := by ring

private theorem small_rank_le_width
    (r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε ∧ ε < 1) :
    r ≤ Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hεsq_le : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε - 1)]
  have hrR : (1 : ℝ) ≤ r := by
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr hr : ((1 : ℕ) : ℝ) ≤ (r : ℝ))
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hscale : (r : ℝ) ≤ (200 : ℝ) * r ^ 2 / ε ^ 2 := by
    apply (le_div_iff₀ hεsq).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) hr0]
  exact_mod_cast hscale.trans (Nat.le_ceil _)

theorem small_rank_failure_bound_of_gram_reduction
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V)
    (ε : ℝ)
    (hgram : ∀ (d₁ d₂ : SignLayer (WalshIndex m))
      (J : FixedSubset (WalshIndex m)
        (Nat.min (walshCard m)
          (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2)))),
      compressedGram V d₁ d₂ J =
        fixedSampleGram (transformedFrame d₁ d₂ V) J)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr : 1 ≤ r) (hrn : r ≤ walshCard m) :
    let k₀ := Nat.min (walshCard m)
      (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))
    frameFailureProbability (k := k₀) ε V ≤ 1 / 100 := by
  dsimp only
  let w := Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2)
  let k₀ := Nat.min (walshCard m) w
  change frameFailureProbability (k := k₀) ε V ≤ 1 / 100
  have hε : 0 < ε ∧ ε < 1 := ⟨hε0, hε1⟩
  have hrw : r ≤ w := by
    simpa only [w] using small_rank_le_width r ε hr hε
  have hk₀r : r ≤ k₀ := le_min hrn hrw
  have hk₀one : 1 ≤ k₀ := hr.trans hk₀r
  have hk₀n : k₀ ≤ walshCard m := Nat.min_le_left _ _
  have hkcard : k₀ ≤ Fintype.card (WalshIndex m) := hk₀n
  have hkuniv : k₀ ≤ (Finset.univ : Finset (WalshIndex m)).card := by
    simpa only [Finset.card_univ] using hkcard
  obtain ⟨J₀, _, hJ₀⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (WalshIndex m)))
      hkuniv
  letI : Nonempty (FixedSubset (WalshIndex m) k₀) := ⟨⟨J₀, hJ₀⟩⟩
  have hprob : frameFailureProbability (k := k₀) ε V =
      uniformProbability
        (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
          FixedSubset (WalshIndex m) k₀)
        (fun sample ↦ euclideanOperatorNorm
          (fixedSampleGram
            (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1) > ε) := by
    unfold frameFailureProbability
    congr 1
    funext sample
    have hg := hgram sample.1 sample.2.1 sample.2.2
    rw [hg]
  rw [hprob]
  by_cases hfull : walshCard m ≤ w
  · have hkfull : k₀ = walshCard m := Nat.min_eq_left hfull
    rw [hkfull]
    have hevent : (fun sample : SignLayer (WalshIndex m) ×
          SignLayer (WalshIndex m) ×
            FixedSubset (WalshIndex m) (walshCard m) ↦
        euclideanOperatorNorm
          (fixedSampleGram
            (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1) > ε) =
        fun _ ↦ False := by
      funext sample
      apply propext
      have hfixed := fixedSampleGram_full_eq_one
        (transformedFrame sample.1 sample.2.1 V)
        (transformedFrame_orthonormal V hV sample.1 sample.2.1) sample.2.2
      have hdiff : fixedSampleGram
            (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1 = 0 :=
        sub_eq_zero.mpr hfixed
      rw [hdiff, euclideanOperatorNorm_eq_l2_opNorm, norm_zero]
      exact iff_false_intro (not_lt_of_ge hε0.le)
    calc
      uniformProbability
          (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
              FixedSubset (WalshIndex m) (walshCard m) ↦
            euclideanOperatorNorm
              (fixedSampleGram
                (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1) > ε) =
          uniformProbability (fun _ : SignLayer (WalshIndex m) ×
              SignLayer (WalshIndex m) ×
              FixedSubset (WalshIndex m) (walshCard m) ↦ False) :=
        congrArg uniformProbability hevent
      _ = 0 := by simp [uniformProbability]
      _ ≤ 1 / 100 := by norm_num
  · have hwlt : w < walshCard m := Nat.lt_of_not_ge hfull
    have hkwidth : k₀ = w := Nat.min_eq_right hwlt.le
    have hmean := small_rank_frobenius_expectation_bound V hV
      ⟨hk₀one, hk₀n⟩
    have hmarkov :=
      uniformProbability_operatorNorm_gt_le_frobeniusExpectation
        (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
            FixedSubset (WalshIndex m) k₀ ↦
          fixedSampleGram
            (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)
        ε ((r : ℝ) * (r + 1) / k₀) hε0 hmean
    refine hmarkov.trans ?_
    have hkpos : (0 : ℝ) < k₀ := by
      exact Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < r) hk₀r)
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε0
    have hceil : (200 : ℝ) * r ^ 2 / ε ^ 2 ≤ (w : ℝ) := by
      simpa only [w] using
        (Nat.le_ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))
    have hwidthR : (w : ℝ) = k₀ := by exact_mod_cast hkwidth.symm
    rw [hwidthR] at hceil
    have hscaled := mul_le_mul_of_nonneg_left hceil hεsq.le
    have hcancel : ε ^ 2 * ((200 : ℝ) * r ^ 2 / ε ^ 2) =
        (200 : ℝ) * r ^ 2 := by field_simp
    rw [hcancel] at hscaled
    rw [div_le_iff₀ hεsq, div_le_iff₀ hkpos]
    have hrR : (1 : ℝ) ≤ r := by
      simpa only [Nat.cast_one] using
        (Nat.cast_le.mpr hr : ((1 : ℕ) : ℝ) ≤ (r : ℝ))
    nlinarith

theorem small_rank_second_moment_of_gram_reduction
    {m r k : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (hk : 1 ≤ k ∧ k ≤ walshCard m)
    (hgram : ∀ (ε : ℝ), 0 < ε → ε < 1 → 1 ≤ r → r ≤ walshCard m →
      ∀ (d₁ d₂ : SignLayer (WalshIndex m))
        (J : FixedSubset (WalshIndex m)
          (Nat.min (walshCard m)
            (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2)))),
        compressedGram V d₁ d₂ J =
          fixedSampleGram (transformedFrame d₁ d₂ V) J) :
    uniformExpectation
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k)
      (fun sample ↦ frobeniusNormSq
        (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) ≤
      (r : ℝ) * (r + 1) / k ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → 1 ≤ r → r ≤ walshCard m →
      let k₀ := Nat.min (walshCard m)
        (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))
      frameFailureProbability (k := k₀) ε V ≤ 1 / 100) := by
  refine ⟨small_rank_frobenius_expectation_bound V hV hk, ?_⟩
  intro ε hε0 hε1 hr hrn
  exact small_rank_failure_bound_of_gram_reduction V hV ε
    (hgram ε hε0 hε1 hr hrn) hε0 hε1 hr hrn

#print axioms transformedFrame_orthonormal
#print axioms small_rank_second_moment_of_gram_reduction

end Problem56
