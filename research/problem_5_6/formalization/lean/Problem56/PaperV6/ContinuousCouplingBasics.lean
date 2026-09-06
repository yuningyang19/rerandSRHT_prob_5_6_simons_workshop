import Problem56.PaperV6.ContinuousCouplingExpected
import Mathlib.MeasureTheory.Measure.Real

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

instance continuousUnitUniform_probability : IsProbabilityMeasure continuousUnitUniform := by
  constructor
  simp [continuousUnitUniform, Real.volume_Icc]

instance continuousKeyLaw_probability (α : Type) [Fintype α] :
    IsProbabilityMeasure (continuousKeyLaw α) := by
  unfold continuousKeyLaw
  infer_instance

theorem continuousKey_eval_law {α : Type} [Fintype α] (i : α) :
    (continuousKeyLaw α).map (fun u ↦ u i) = continuousUnitUniform :=
  (measurePreserving_eval (fun _ : α ↦ continuousUnitUniform) i).map_eq

theorem continuousKey_independent {α : Type} [Fintype α] :
    iIndepFun (fun (i : α) (u : α → ℝ) ↦ u i) (continuousKeyLaw α) :=
  iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

theorem continuousUnitUniform_Iic (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    continuousUnitUniform (Set.Iic θ) = ENNReal.ofReal θ := by
  rw [continuousUnitUniform, Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic θ ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 θ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h, hx0, _⟩
      exact ⟨hx0, h⟩
    · rintro ⟨hx0, h⟩
      exact ⟨h, hx0, h.trans hθ1⟩
  rw [hset, Real.volume_Icc]
  simp

theorem continuousUnitUniform_Ioi (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    continuousUnitUniform (Set.Ioi θ) = ENNReal.ofReal (1 - θ) := by
  rw [continuousUnitUniform, Measure.restrict_apply measurableSet_Ioi]
  have hset : Set.Ioi θ ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc θ 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h, _, hx1⟩
      exact ⟨h, hx1⟩
    · rintro ⟨h, hx1⟩
      exact ⟨h, hθ0.trans h.le, hx1⟩
  rw [hset, Real.volume_Ioc]

theorem continuousThreshold_fiber {α : Type} (θ : ℝ) (e : SignLayer α) :
    {u : α → ℝ | continuousThreshold θ u = e} =
      Set.univ.pi (fun i ↦ if e i then Set.Iic θ else Set.Ioi θ) := by
  classical
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, continuousThreshold, funext_iff]
  apply forall_congr'
  intro i
  cases he : e i <;> simp [he, not_le]

theorem continuousThreshold_measurable {α : Type} [Fintype α]
    [MeasurableSpace (SignLayer α)] (θ : ℝ) :
    Measurable (continuousThreshold (α := α) θ) := by
  classical
  apply measurable_to_countable'
  intro e
  change MeasurableSet {u : α → ℝ | continuousThreshold θ u = e}
  rw [continuousThreshold_fiber]
  apply MeasurableSet.univ_pi
  intro i
  cases e i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact measurableSet_Ioi
  · exact measurableSet_Iic

theorem continuousThreshold_law {α : Type} [Fintype α] [DecidableEq α]
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (e : SignLayer α) :
    (continuousKeyLaw α).real {u | continuousThreshold θ u = e} =
      bernoulliWeight θ e := by
  classical
  rw [measureReal_def, continuousThreshold_fiber, continuousKeyLaw, Measure.pi_pi,
    ENNReal.toReal_prod]
  unfold bernoulliWeight
  apply Finset.prod_congr rfl
  intro i _
  cases he : e i
  · simp [he, continuousUnitUniform_Ioi θ hθ0 hθ1, ENNReal.toReal_ofReal,
      sub_nonneg.mpr hθ1]
  · simp [he, continuousUnitUniform_Iic θ hθ0 hθ1, ENNReal.toReal_ofReal, hθ0]

theorem continuousKey_frame_marginal {Ω α : Type} [MeasurableSpace Ω] [Fintype α]
    (μ : Measure Ω) :
    (μ.prod (continuousKeyLaw α)).map Prod.fst = μ := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem continuousKey_frame_independent {Ω α β : Type} [MeasurableSpace Ω]
    [Fintype α] [MeasurableSpace β] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (X : Ω → Matrix α (Fin r) ℝ) (T : (α → ℝ) → β)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j)) (hT : Measurable T) :
    IndepFun (fun p : Ω × (α → ℝ) ↦ fun i j ↦ X p.1 i j)
      (fun p ↦ T p.2) (μ.prod (continuousKeyLaw α)) :=
  indepFun_prod hX hT

end Problem56.PaperV6
