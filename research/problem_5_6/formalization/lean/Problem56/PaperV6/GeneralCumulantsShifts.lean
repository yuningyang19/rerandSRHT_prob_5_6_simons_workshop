import Problem56.PaperV6.GeneralCumulantsMixed
import Problem56.PaperV6.GeneralCumulantsMultilinear

/-! Deterministic shifts at every order at least two. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

theorem finiteJointMoments_update_constant
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (hY : FiniteJointMoments μ Y)
    (i : ι) (c : ℝ) :
    FiniteJointMoments μ (Function.update Y i (fun _ ↦ c)) := by
  intro B
  by_cases hi : i ∈ B
  · have hpoint := measure_blockProduct_update_of_mem Y i (fun _ ↦ c) B hi
    simpa only [hpoint] using (hY (B.erase i)).const_mul c
  · have hpoint := measure_blockProduct_update_of_notMem Y i (fun _ ↦ c) B hi
    simpa only [hpoint] using hY B

theorem finiteJointMoments_update_add_constant
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (hY : FiniteJointMoments μ Y)
    (i : ι) (c : ℝ) :
    FiniteJointMoments μ (Function.update Y i (fun ω ↦ Y i ω + c)) := by
  intro B
  by_cases hi : i ∈ B
  · have hpoint (ω : Ω) :
        (∏ j ∈ B, Function.update Y i (fun ω ↦ Y i ω + c) j ω) =
          (∏ j ∈ B, Y j ω) + c * ∏ j ∈ B.erase i, Y j ω := by
      rw [measure_blockProduct_update_of_mem Y i _ B hi,
        ← Finset.mul_prod_erase B (fun j ↦ Y j ω) hi]
      ring
    simp_rw [hpoint]
    exact (hY B).fun_add ((hY (B.erase i)).const_mul c)
  · have hpoint := measure_blockProduct_update_of_notMem Y i
      (fun ω ↦ Y i ω + c) B hi
    simpa only [hpoint] using hY B

theorem measure_jointCumulant_constant_argument_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (hY : FiniteJointMoments μ Y)
    (hsize : 2 ≤ Fintype.card ι) (i : ι) (c : ℝ) :
    measureJointCumulant μ (Function.update Y i (fun _ ↦ c)) = 0 := by
  classical
  let Z := Function.update Y i (fun _ ↦ c)
  let A : Finset ι := {i}
  let B := (Finset.univ : Finset ι).erase i
  have hA : A.Nonempty := Finset.singleton_nonempty i
  have hB : B.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [B]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  have hdisjoint : Disjoint A B := by simp [A, B]
  have hcover : A ∪ B = Finset.univ := by simp [A, B]
  have hconst : (fun ω ↦ fun j : A ↦ Z j.1 ω) =
      (fun _ : Ω ↦ fun _ : A ↦ c) := by
    funext ω j
    have hj : j.1 = i := Finset.mem_singleton.mp j.2
    simp [Z, hj]
  have hIndep : IndepFun (fun ω ↦ fun j : A ↦ Z j.1 ω)
      (fun ω ↦ fun j : B ↦ Z j.1 ω) μ := by
    rw [hconst]
    exact indepFun_const_left _ _
  exact measure_independent_families_mixed_cumulant_vanish μ Z
    (finiteJointMoments_update_constant μ Y hY i c)
    A B hcover hdisjoint hIndep hA hB

theorem measure_jointCumulant_add_constant_one
    {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (hY : FiniteJointMoments μ Y)
    (hsize : 2 ≤ Fintype.card ι) (i : ι) (c : ℝ) :
    measureJointCumulant μ (Function.update Y i (fun ω ↦ Y i ω + c)) =
      measureJointCumulant μ Y := by
  letI : Nonempty ι := ⟨i⟩
  have hlinear := generalMultilinearity Ω ι μ Y i (Y i) (fun _ ↦ c) 1 1
    (by simpa only [Function.update_eq_self] using hY)
    (finiteJointMoments_update_constant μ Y hY i c)
  have hzero := measure_jointCumulant_constant_argument_zero μ Y hY hsize i c
  simpa only [one_mul, Function.update_eq_self, hzero, add_zero] using hlinear

theorem measure_jointCumulant_shift_finite_set
    {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (hY : FiniteJointMoments μ Y)
    (c : ι → ℝ) (hsize : 2 ≤ Fintype.card ι) (S : Finset ι) :
    FiniteJointMoments μ (fun j ω ↦ if j ∈ S then Y j ω + c j else Y j ω) ∧
    measureJointCumulant μ (fun j ω ↦ if j ∈ S then Y j ω + c j else Y j ω) =
      measureJointCumulant μ Y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · simpa only [Finset.notMem_empty, if_false] using hY
      · simp only [Finset.notMem_empty, if_false]
  | @insert i S hi ih =>
      let Z : ι → Ω → ℝ := fun j ω ↦ if j ∈ S then Y j ω + c j else Y j ω
      have heq : Function.update Z i (fun ω ↦ Z i ω + c i) =
          (fun j ω ↦ if j ∈ insert i S then Y j ω + c j else Y j ω) := by
        funext j ω
        by_cases hji : j = i
        · subst j
          simp [Z, hi]
        · simp [Function.update_of_ne hji, Z, hji]
      constructor
      · rw [← heq]
        exact finiteJointMoments_update_add_constant μ Z ih.1 i (c i)
      · rw [← heq, measure_jointCumulant_add_constant_one μ Z ih.1 hsize i (c i)]
        exact ih.2

theorem generalShiftInvariance : GeneralShiftInvarianceExpected := by
  intro Ω ι _ _ _ μ _ Y c hsize hY
  simpa only [Finset.mem_univ, if_true] using
    (measure_jointCumulant_shift_finite_set μ Y hY c hsize Finset.univ).2

end Problem56.PaperV6
