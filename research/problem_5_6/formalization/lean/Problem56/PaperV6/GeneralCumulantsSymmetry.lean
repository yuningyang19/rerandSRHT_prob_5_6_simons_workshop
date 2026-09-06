import Problem56.PaperV6.GeneralCumulantsExpected

/-! Scalar homogeneity and symmetry on arbitrary real probability spaces. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

theorem measure_integral_const_family_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (c : ι → ℝ) (Y : ι → Ω → ℝ) (B : Finset ι) :
    (∫ ω, (∏ j ∈ B, c j * Y j ω) ∂μ) =
      (∏ j ∈ B, c j) * ∫ ω, (∏ j ∈ B, Y j ω) ∂μ := by
  simp_rw [Finset.prod_mul_distrib]
  exact integral_const_mul _ _

theorem measure_jointCumulant_const_family_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (c : ι → ℝ) (Y : ι → Ω → ℝ) :
    measureJointCumulant μ (fun j ω ↦ c j * Y j ω) =
      (∏ j, c j) * measureJointCumulant μ Y := by
  classical
  unfold measureJointCumulant
  calc
    (∑ P : Finpartition (Finset.univ : Finset ι),
        ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ∏ B ∈ P.parts,
            (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ B, c j * Y j ω)) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ((∏ j, c j) *
            ∏ B ∈ P.parts,
              (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ B, Y j ω)) := by
        apply Finset.sum_congr rfl
        intro P _
        congr 1
        rw [Finset.prod_congr rfl (fun B hB ↦
          measure_integral_const_family_mul μ c Y B)]
        rw [Finset.prod_mul_distrib]
        have hpartition :
            ∏ B ∈ P.parts, ∏ j ∈ B, c j = ∏ j, c j := by
          calc
            ∏ B ∈ P.parts, ∏ j ∈ B, c j =
                ∏ j ∈ P.parts.biUnion id, c j :=
              (Finset.prod_biUnion P.disjoint).symm
            _ = ∏ j, c j := by rw [P.biUnion_parts]
        rw [hpartition]
    _ = (∏ j, c j) *
        ∑ P : Finpartition (Finset.univ : Finset ι),
          ((-1 : ℝ) ^ (P.parts.card - 1) *
            (Nat.factorial (P.parts.card - 1) : ℝ)) *
            ∏ B ∈ P.parts,
              (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ B, Y j ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      ring


theorem measure_jointCumulant_identDistrib_repeat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℝ} (h : IdentDistrib Z W μ μ) (q : ℕ) :
    measureJointCumulant μ (fun _ : Fin q ↦ Z) =
      measureJointCumulant μ (fun _ : Fin q ↦ W) := by
  classical
  unfold measureJointCumulant
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  simpa only [Finset.prod_const] using (h.pow (n := B.card)).integral_eq

theorem generalOddSymmetry : GeneralOddSymmetryExpected := by
  intro Ω _ μ _ Z q hq _ hsym
  have heq := measure_jointCumulant_identDistrib_repeat μ hsym q
  have hscale := measure_jointCumulant_const_family_mul μ
    (fun _ : Fin q ↦ (-1 : ℝ)) (fun _ : Fin q ↦ Z)
  have hsign : (∏ _ : Fin q, (-1 : ℝ)) = -1 := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      hq.neg_one_pow
  simp only [neg_one_mul, hsign] at hscale
  rw [hscale] at heq
  linarith

end Problem56.PaperV6
