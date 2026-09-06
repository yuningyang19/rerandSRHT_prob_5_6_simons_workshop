import Problem56.GraphOperatorL2

/-!
Finite Frobenius/operator-norm and uniform-probability infrastructure used by
the small-rank branch.  The probability statements here are elementary finite
sum inequalities; no measure-theoretic representatives are involved.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

theorem euclideanOperatorNorm_sq_le_frobeniusNormSq
    {α : Type*} [Fintype α] (A : Matrix α α ℝ) :
    euclideanOperatorNorm A ^ 2 ≤ frobeniusNormSq A := by
  classical
  rw [euclideanOperatorNorm_eq_l2_opNorm, Matrix.l2_opNorm_def]
  let T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := α) (n := α)).trans
      LinearMap.toContinuousLinearMap A
  have hF : 0 ≤ frobeniusNormSq A := by
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (A i j)
  have hnorm : ‖T‖ ≤ Real.sqrt (frobeniusNormSq A) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
      mul_pow, Real.sq_sqrt hF, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    have hrows :
        (∑ i, (∑ j, A i j * WithLp.ofLp x j) ^ 2) ≤
          (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, (WithLp.ofLp x j) ^ 2 := by
      calc
        (∑ i, (∑ j, A i j * WithLp.ofLp x j) ^ 2) ≤
            ∑ i, (∑ j, (A i j) ^ 2) * ∑ j, (WithLp.ofLp x j) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (WithLp.ofLp x)
        _ = (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, (WithLp.ofLp x j) ^ 2 := by
          rw [Finset.sum_mul]
    simpa [T, Matrix.mulVec, dotProduct, frobeniusNormSq] using hrows
  have hsqrt := Real.sq_sqrt hF
  have hop : 0 ≤ ‖T‖ := norm_nonneg _
  nlinarith

theorem uniformProbability_operatorNorm_gt_le_frobeniusExpectation
    {Ω α : Type*} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (A : Ω → Matrix α α ℝ) (ε M : ℝ) (hε : 0 < ε)
    (hmean : uniformExpectation (fun ω ↦ frobeniusNormSq (A ω)) ≤ M) :
    uniformProbability (fun ω ↦ euclideanOperatorNorm (A ω) > ε) ≤
      M / ε ^ 2 := by
  classical
  let bad : Finset Ω := Finset.univ.filter fun ω ↦
    euclideanOperatorNorm (A ω) > ε
  have hbad :
      (bad.card : ℝ) * ε ^ 2 ≤ (∑ ω ∈ bad, frobeniusNormSq (A ω)) := by
    calc
      (bad.card : ℝ) * ε ^ 2 = ∑ ω ∈ bad, ε ^ 2 := by simp
      _ ≤ ∑ ω ∈ bad, frobeniusNormSq (A ω) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hlarge : ε < euclideanOperatorNorm (A ω) := by
          simpa [bad] using hω
        have hnorm_nonneg : 0 ≤ euclideanOperatorNorm (A ω) :=
          euclideanOperatorNorm_nonneg (A ω)
        have hsquare : ε ^ 2 ≤ euclideanOperatorNorm (A ω) ^ 2 := by
          nlinarith
        exact hsquare.trans (euclideanOperatorNorm_sq_le_frobeniusNormSq (A ω))
  have hsum :
      (∑ ω ∈ bad, frobeniusNormSq (A ω)) ≤
        ∑ ω, frobeniusNormSq (A ω) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
    intro ω _ _
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (A ω i j)
  have hcard : 0 < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have heps_sq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have htotal :
      (∑ ω, frobeniusNormSq (A ω)) ≤ M * (Fintype.card Ω : ℝ) := by
    rw [uniformExpectation] at hmean
    exact (div_le_iff₀ hcard).mp hmean
  rw [uniformProbability]
  change (bad.card : ℝ) / (Fintype.card Ω : ℝ) ≤ M / ε ^ 2
  rw [div_le_div_iff₀ hcard heps_sq]
  exact hbad.trans (hsum.trans htotal)

end Problem56
