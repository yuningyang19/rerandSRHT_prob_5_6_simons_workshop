import Problem56.PaperV6.GeneralSampling
import Problem56.PaperV6.FiniteNoiseLaw
import Problem56.PaperV6.GeneralSamplingJointExpected

open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

theorem uniform_event_weight_formula {β : Type*} [Fintype β]
    (E : β → Prop) [DecidablePred E] :
    (∑ b, if E b then (1 : ℝ) / Fintype.card β else 0) = uniformProbability E := by
  classical
  simp only [uniformProbability, Finset.natCast_card_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : E b <;> simp [h]

theorem fixed_noise_failure_law {Ω α : Type} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r k : ℕ} [MeasurableSpace (FixedSubset α k)]
    [MeasurableSingletonClass (FixedSubset α k)]
    (X : Ω → Matrix α (Fin r) ℝ) (S : Ω → FixedSubset α k)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j)) (hS : Measurable S)
    (hi : IndepFun (fun ω ↦ fun i j ↦ X ω i j) S μ)
    (hk : k ≤ Fintype.card α) (ε : ℝ)
    (hMarg : ∀ J, μ.real {ω | S ω = J} = 1 / Fintype.card (FixedSubset α k)) :
    μ.real {ω | euclideanOperatorNorm (fixedSampleGram (X ω) (S ω) - 1) > ε} =
      averagedFixedFailureProbability (k := k) μ ε X := by
  classical
  letI := fixedSubset_nonempty k hk
  have htotal : (∑ _ : FixedSubset α k, (1 : ℝ) / Fintype.card (FixedSubset α k)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv, one_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h := finiteNoiseFailureLaw Ω α (FixedSubset α k) μ r X S
    (fun _ ↦ 1 / Fintype.card (FixedSubset α k))
    (fun A J ↦ euclideanOperatorNorm (fixedSampleGram A J - 1) > ε)
    hX hS hi (fun J ↦ measurable_fixed_failure (fun A : α → Fin r → ℝ ↦ A) measurable_id J ε)
    (fun _ ↦ by positivity) htotal hMarg
  rw [h]
  unfold averagedFixedFailureProbability
  apply integral_congr_ae
  filter_upwards [] with ω
  exact uniform_event_weight_formula _

theorem bernoulli_noise_failure_law {Ω α : Type} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} [MeasurableSpace (SignLayer α)] [MeasurableSingletonClass (SignLayer α)]
    (X : Ω → Matrix α (Fin r) ℝ) (E : Ω → SignLayer α)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j)) (hE : Measurable E)
    (hi : IndepFun (fun ω ↦ fun i j ↦ X ω i j) E μ)
    (θ η : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hMarg : ∀ e, μ.real {ω | E ω = e} = bernoulliWeight θ e) :
    μ.real {ω | euclideanOperatorNorm (bernoulliGram θ (X ω) (E ω) - 1) > η} =
      averagedBernoulliFailureProbability μ θ η X := by
  classical
  have htotal : (∑ e : SignLayer α, bernoulliWeight θ e) = 1 := by
    have h := bernoulli_exp_count_sum (α := α) θ 0
    simpa using h
  exact finiteNoiseFailureLaw Ω α (SignLayer α) μ r X E (bernoulliWeight θ)
    (fun A e ↦ euclideanOperatorNorm (bernoulliGram θ A e - 1) > η)
    hX hE hi (fun e ↦ measurable_bernoulli_failure (fun A : α → Fin r → ℝ ↦ A) measurable_id e θ η)
    (bernoulliWeight_nonneg θ hθ) htotal hMarg

theorem general_sampling_joint : GeneralSamplingJointExpected := by
  intro Ω α _ _ _ μ _ r k _ _ _ _ X S Eminus Eplus hX horth hS hEm hEp hiS hiEm hiEp
    ε γ hε0 hε1 hk0 hkn
  dsimp only
  intro htminus htplus hSMarg hEmMarg hEpMarg hminus hplus
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast (hk0.trans hkn)
  have hm0 : 0 ≤ (1 - ε / 4) * (k : ℝ) / Fintype.card α := by
    apply div_nonneg _ hn.le
    apply mul_nonneg _ (Nat.cast_nonneg k)
    linarith
  have hp0 : 0 ≤ (1 + ε / 4) * (k : ℝ) / Fintype.card α := by positivity
  rw [bernoulli_noise_failure_law μ X Eminus hX hEm hiEm _ _ ⟨hm0,htminus⟩ hEmMarg] at hminus
  rw [bernoulli_noise_failure_law μ X Eplus hX hEp hiEp _ _ ⟨hp0,htplus⟩ hEpMarg] at hplus
  rw [fixed_noise_failure_law μ X S hX hS hiS hkn ε hSMarg]
  exact general_sampling Ω α μ r k X hX horth ε γ hε0 hε1 hk0 hkn htminus htplus hminus hplus

end Problem56.PaperV6
