import Problem56.PaperV6.FormalLogPowers

/-! The formal logarithm and exponential coefficients obtained by multiplication. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

theorem formalLog_factorial_coefficient (j : ℕ) (hj : j ≠ 0) :
    ((-1 : ℝ) ^ (j - 1) / (j : ℝ)) * (Nat.factorial j : ℝ) =
      (-1 : ℝ) ^ (j - 1) * (Nat.factorial (j - 1) : ℝ) := by
  rw [← Nat.mul_factorial_pred hj, Nat.cast_mul]
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  field_simp

theorem squarefreeLog_partition
    {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (hm : m ∅ = 1)
    (S : Finset ι) (hS : S.Nonempty) :
    squarefreeLog m S =
      ∑ P : Finpartition S,
        ((-1 : ℝ) ^ (P.parts.card - 1) * (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ∏ B ∈ P.parts, m B := by
  classical
  let f : Finset ι → ℝ := fun T ↦ m T - squarefreeUnit T
  have hf : f ∅ = 0 := by simp [f, squarefreeUnit, hm]
  have hprod (P : Finpartition S) : (∏ B ∈ P.parts, f B) = ∏ B ∈ P.parts, m B := by
    apply Finset.prod_congr rfl
    intro B hB
    simp [f, squarefreeUnit, P.ne_empty hB]
  have hPzero (P : Finpartition S) : P.parts.card ≠ 0 :=
    Finset.card_ne_zero.mpr (P.parts_nonempty hS.ne_empty)
  rw [squarefreeLog]
  change (∑ j ∈ Finset.range (S.card + 1),
    if j = 0 then 0 else ((-1 : ℝ) ^ (j - 1) / (j : ℝ)) * squarefreePow f j S) = _
  calc
    _ = ∑ j ∈ Finset.range (S.card + 1), ∑ P : Finpartition S,
        if P.parts.card = j then
          (((-1 : ℝ) ^ (j - 1) / (j : ℝ)) * (Nat.factorial j : ℝ)) *
            ∏ B ∈ P.parts, m B else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · simp [hj, hPzero]
      · rw [if_neg hj, squarefreePow_partition f hf]
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P _
        rw [hprod]
        by_cases hP : P.parts.card = j <;> simp [hP]
    _ = ∑ P : Finpartition S, ∑ j ∈ Finset.range (S.card + 1),
        if P.parts.card = j then
          (((-1 : ℝ) ^ (j - 1) / (j : ℝ)) * (Nat.factorial j : ℝ)) *
            ∏ B ∈ P.parts, m B else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      rw [Finset.sum_eq_single P.parts.card]
      · simp only [if_true, formalLog_factorial_coefficient _ (hPzero P)]
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_of_le P.card_parts_le_card)))

theorem squarefreeExp_partition
    {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) (hf : f ∅ = 0)
    (S : Finset ι) :
    squarefreeExp f S = ∑ P : Finpartition S, ∏ B ∈ P.parts, f B := by
  classical
  rw [squarefreeExp]
  simp_rw [squarefreePow_partition f hf]
  calc
    _ = ∑ j ∈ Finset.range (S.card + 1), ∑ P : Finpartition S,
        if P.parts.card = j then ∏ B ∈ P.parts, f B else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
      field_simp
    _ = ∑ P : Finpartition S, ∑ j ∈ Finset.range (S.card + 1),
        if P.parts.card = j then ∏ B ∈ P.parts, f B else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      rw [Finset.sum_eq_single P.parts.card]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_of_le P.card_parts_le_card)))

noncomputable def formalLogFinpartitionEquiv
    {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Finpartition (Finset.univ : Finset S) ≃ Finpartition S where
  toFun := liftBlockPartition S
  invFun := lowerBlockPartition S
  left_inv := lowerBlockPartition_liftBlockPartition S
  right_inv := liftBlockPartition_lowerBlockPartition S

theorem formalLog_cumulant_ambient_partition
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (S : Finset ι) :
    measureJointCumulant μ (fun j : S ↦ Y j.1) =
      ∑ P : Finpartition S,
        ((-1 : ℝ) ^ (P.parts.card - 1) * (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ∏ B ∈ P.parts, squarefreeMoment μ Y B := by
  classical
  rw [measureJointCumulant]
  apply Fintype.sum_equiv (formalLogFinpartitionEquiv S)
  intro Q
  change _ = ((-1 : ℝ) ^ ((liftBlockPartition S Q).parts.card - 1) *
    (Nat.factorial ((liftBlockPartition S Q).parts.card - 1) : ℝ)) * _
  rw [card_liftBlockPartition_parts]
  congr 1
  exact measure_blockMomentProduct_liftBlockPartition μ Y S Q

theorem formalLogMomentCoefficient : FormalLogMomentCoefficientExpected := by
  intro Ω ι _ _ _ μ _ Y _ S hS
  rw [squarefreeLog_partition _ (squarefreeMoment_empty μ Y) S hS]
  exact (formalLog_cumulant_ambient_partition μ Y S).symm

end Problem56.PaperV6
