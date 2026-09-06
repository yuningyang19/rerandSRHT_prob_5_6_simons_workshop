import Problem56.PaperV6.GeneralCumulantsExpected

/-! Linearity in one occurrence under precisely the requisite finite moments. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

theorem measure_blockProduct_update_of_mem
    {Ω ι : Type*} [DecidableEq ι] (Y : ι → Ω → ℝ)
    (i : ι) (U : Ω → ℝ) (B : Finset ι) (hi : i ∈ B) (ω : Ω) :
    (∏ j ∈ B, Function.update Y i U j ω) =
      U ω * ∏ j ∈ B.erase i, Y j ω := by
  rw [← Finset.mul_prod_erase B (fun j ↦ Function.update Y i U j ω) hi]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem measure_blockProduct_update_of_notMem
    {Ω ι : Type*} [DecidableEq ι] (Y : ι → Ω → ℝ)
    (i : ι) (U : Ω → ℝ) (B : Finset ι) (hi : i ∉ B) (ω : Ω) :
    (∏ j ∈ B, Function.update Y i U j ω) = ∏ j ∈ B, Y j ω := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

theorem measure_blockMoment_linear_update
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (i : ι)
    (U V : Ω → ℝ) (a b : ℝ) (B : Finset ι) (hi : i ∈ B)
    (hU : FiniteJointMoments μ (Function.update Y i U))
    (hV : FiniteJointMoments μ (Function.update Y i V)) :
    (∫ ω, (∏ j ∈ B, Function.update Y i (fun ω ↦ a * U ω + b * V ω) j ω) ∂μ) =
      a * (∫ ω, (∏ j ∈ B, Function.update Y i U j ω) ∂μ) +
      b * (∫ ω, (∏ j ∈ B, Function.update Y i V j ω) ∂μ) := by
  have hpoint (ω : Ω) :
      (∏ j ∈ B, Function.update Y i (fun ω ↦ a * U ω + b * V ω) j ω) =
        a * (∏ j ∈ B, Function.update Y i U j ω) +
        b * (∏ j ∈ B, Function.update Y i V j ω) := by
    rw [measure_blockProduct_update_of_mem Y i _ B hi,
      measure_blockProduct_update_of_mem Y i U B hi,
      measure_blockProduct_update_of_mem Y i V B hi]
    ring
  simp_rw [hpoint]
  rw [integral_add ((hU B).const_mul a) ((hV B).const_mul b),
    integral_const_mul, integral_const_mul]

theorem measure_partitionMoment_linear_update
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (i : ι)
    (U V : Ω → ℝ) (a b : ℝ)
    (P : Finpartition (Finset.univ : Finset ι))
    (hU : FiniteJointMoments μ (Function.update Y i U))
    (hV : FiniteJointMoments μ (Function.update Y i V)) :
    (∏ B ∈ P.parts, ∫ ω,
      (∏ j ∈ B, Function.update Y i (fun ω ↦ a * U ω + b * V ω) j ω) ∂μ) =
      a * (∏ B ∈ P.parts, ∫ ω, (∏ j ∈ B, Function.update Y i U j ω) ∂μ) +
      b * (∏ B ∈ P.parts, ∫ ω, (∏ j ∈ B, Function.update Y i V j ω) ∂μ) := by
  classical
  let C := P.part i
  have hC : C ∈ P.parts := P.part_mem.mpr (Finset.mem_univ i)
  have hiC : i ∈ C := P.mem_part (Finset.mem_univ i)
  have hrest (W : Ω → ℝ) :
      (∏ B ∈ P.parts.erase C, ∫ ω, (∏ j ∈ B, Function.update Y i W j ω) ∂μ) =
        ∏ B ∈ P.parts.erase C, ∫ ω, (∏ j ∈ B, Y j ω) ∂μ := by
    apply Finset.prod_congr rfl
    intro B hB
    have hiB : i ∉ B := by
      intro hi
      exact (Finset.mem_erase.mp hB).1
        (P.eq_of_mem_parts (Finset.mem_erase.mp hB).2 hC hi hiC)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (measure_blockProduct_update_of_notMem Y i W B hiB)
  have hsplit (W : Ω → ℝ) :
      (∏ B ∈ P.parts, ∫ ω, (∏ j ∈ B, Function.update Y i W j ω) ∂μ) =
        (∫ ω, (∏ j ∈ C, Function.update Y i W j ω) ∂μ) *
          ∏ B ∈ P.parts.erase C, ∫ ω, (∏ j ∈ B, Y j ω) ∂μ := by
    rw [← Finset.mul_prod_erase P.parts
      (fun B ↦ ∫ ω, (∏ j ∈ B, Function.update Y i W j ω) ∂μ) hC, hrest]
  rw [hsplit, hsplit, hsplit,
    measure_blockMoment_linear_update μ Y i U V a b C hiC hU hV]
  ring

theorem generalMultilinearity : GeneralMultilinearityExpected := by
  intro Ω ι _ _ _ _ μ _ Y i U V a b hU hV
  classical
  unfold measureJointCumulant
  simp_rw [measure_partitionMoment_linear_update μ Y i U V a b _ hU hV]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  ring

end Problem56.PaperV6
