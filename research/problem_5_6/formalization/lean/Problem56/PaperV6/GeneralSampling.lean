import Problem56.PaperV6.SamplingPointwise
import Problem56.PaperV6.FixedFrame

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

theorem continuous_operatorNorm_coordinates {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Continuous (fun A : α → β → ℝ ↦ euclideanOperatorNorm A) := by
  change Continuous (fun A : Matrix α β ℝ ↦ euclideanOperatorNorm A)
  simp_rw [euclideanOperatorNorm_eq_l2_opNorm]
  exact continuous_norm

theorem measurable_fixed_failure {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Ω → Matrix α (Fin r) ℝ)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j))
    (J : FixedSubset α k) (ε : ℝ) :
    MeasurableSet {ω | euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε} := by
  have hc : ∀ i j, Measurable (fun ω ↦ X ω i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)
  have hm : Measurable (fun ω ↦ fun i j ↦ (fixedSampleGram (X ω) J - 1) i j) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [fixedSampleGram, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  exact measurableSet_lt measurable_const (continuous_operatorNorm_coordinates.measurable.comp hm)

theorem measurable_bernoulli_failure {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Ω → Matrix α (Fin r) ℝ)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j))
    (e : SignLayer α) (θ ε : ℝ) :
    MeasurableSet {ω | euclideanOperatorNorm (bernoulliGram θ (X ω) e - 1) > ε} := by
  have hc : ∀ i j, Measurable (fun ω ↦ X ω i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)
  have hm : Measurable (fun ω ↦ fun i j ↦ (bernoulliGram θ (X ω) e - 1) i j) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [bernoulliGram, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  exact measurableSet_lt measurable_const (continuous_operatorNorm_coordinates.measurable.comp hm)

theorem integrable_finite_event_sum {Ω β : Type*} [MeasurableSpace Ω]
    [Fintype β] (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : β → ℝ) (E : β → Ω → Prop) [∀ b, DecidablePred (E b)]
    (hE : ∀ b, MeasurableSet {ω | E b ω}) :
    Integrable (fun ω ↦ ∑ b, if E b ω then q b else 0) μ := by
  apply integrable_finsetSum
  intro b _
  have hi := (integrable_const (q b) : Integrable (fun _ : Ω ↦ q b) μ).indicator (hE b)
  apply hi.congr
  filter_upwards [] with ω
  by_cases h : E b ω <;> simp [Set.indicator, h]

theorem integrable_fixed_failure {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {r k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Matrix α (Fin r) ℝ)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j)) (ε : ℝ) :
    Integrable (fun ω ↦ uniformProbability (fun J : FixedSubset α k ↦
      euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε)) μ := by
  classical
  simp only [uniformProbability, Finset.natCast_card_filter]
  apply Integrable.div_const
  exact integrable_finite_event_sum μ (fun _ ↦ 1) _
    (fun J ↦ measurable_fixed_failure X hX J ε)

theorem integrable_bernoulli_failure {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {r : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Matrix α (Fin r) ℝ)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j)) (θ ε : ℝ) :
    Integrable (fun ω ↦ bernoulliProbability θ (fun e ↦
      euclideanOperatorNorm (bernoulliGram θ (X ω) e - 1) > ε)) μ := by
  classical
  unfold bernoulliProbability
  exact integrable_finite_event_sum μ (bernoulliWeight θ) _
    (fun e ↦ measurable_bernoulli_failure X hX e θ ε)

theorem general_sampling : GeneralSamplingExpected := by
  intro Ω α _ _ _ μ _ r k X hX _horth ε γ hε0 hε1 hk0 hkn htminus htplus hminus hplus
  let θminus : ℝ := (1 - ε / 4) * k / Fintype.card α
  let θplus : ℝ := (1 + ε / 4) * k / Fintype.card α
  let F : Ω → ℝ := fun ω ↦ uniformProbability (fun J : FixedSubset α k ↦
    euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε)
  let Bminus : Ω → ℝ := fun ω ↦ bernoulliProbability θminus (fun e ↦
    euclideanOperatorNorm (bernoulliGram θminus (X ω) e - 1) > ε / 4)
  let Bplus : Ω → ℝ := fun ω ↦ bernoulliProbability θplus (fun e ↦
    euclideanOperatorNorm (bernoulliGram θplus (X ω) e - 1) > ε / 4)
  let c : ℝ := 2 * Real.exp (-(ε ^ 2 * k / 48))
  have hF : Integrable F μ := integrable_fixed_failure μ X hX ε
  have hBm : Integrable Bminus μ := integrable_bernoulli_failure μ X hX θminus (ε / 4)
  have hBp : Integrable Bplus μ := integrable_bernoulli_failure μ X hX θplus (ε / 4)
  have hbound : ∫ ω, F ω ∂μ ≤ ∫ ω, (Bminus ω + Bplus ω + c) ∂μ := by
    apply integral_mono_ae hF ((hBm.add hBp).add (integrable_const c))
    exact Filter.Eventually.of_forall (sampling_pointwise X ε ⟨hε0,hε1⟩
      ⟨hk0,hkn⟩ htminus htplus)
  have heq : (∫ ω, (Bminus ω + Bplus ω + c) ∂μ) =
      (∫ ω, Bminus ω ∂μ) + (∫ ω, Bplus ω ∂μ) + c := by
    rw [integral_add (hBm.fun_add hBp) (integrable_const c), integral_add hBm hBp]
    simp
  rw [heq] at hbound
  change (∫ ω, Bminus ω ∂μ) ≤ γ at hminus
  change (∫ ω, Bplus ω ∂μ) ≤ γ at hplus
  change (∫ ω, F ω ∂μ) ≤ 2 * γ + c
  linarith

end Problem56.PaperV6
