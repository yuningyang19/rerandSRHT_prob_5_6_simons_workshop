import Problem56.Definitions
import Mathlib.Probability.Independence.Integration

/-!
Reviewer-owned expected statements for frozen v6 `lem:sampling`.
These are definitions of obligations, not proofs or axioms. The frame law is
an arbitrary probability measure. Sampling uses the literal finite laws from
B, independently of the frame; the separate finite-noise law transport below
must connect these iterated probabilities to an arbitrary independent joint
realization. The two Bernoulli draws need not be independent of each other.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

noncomputable def averagedBernoulliFailureProbability
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    {r : ℕ} (μ : Measure Ω) (θ η : ℝ)
    (X : Ω → Matrix α (Fin r) ℝ) : ℝ :=
  ∫ ω, bernoulliProbability θ (fun e ↦
    euclideanOperatorNorm (bernoulliGram θ (X ω) e - 1) > η) ∂μ

noncomputable def averagedFixedFailureProbability
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    {r k : ℕ} (μ : Measure Ω) (ε : ℝ)
    (X : Ω → Matrix α (Fin r) ℝ) : ℝ :=
  ∫ ω, uniformProbability (fun J : FixedSubset α k ↦
    euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε) ∂μ

/-- Exact general random-frame sampling target. The hypotheses bound the
averaged marginal failure probabilities, not a pointwise maximum in ω. -/
def GeneralSamplingExpected : Prop :=
  ∀ (Ω α : Type) [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r k : ℕ)
    (X : Ω → Matrix α (Fin r) ℝ),
    Measurable (fun ω ↦ fun i j ↦ X ω i j) → (∀ᵐ ω ∂μ, OrthonormalFrame (X ω)) →
    ∀ (ε γ : ℝ), 0 < ε → ε < 1 →
    1 ≤ k → k ≤ Fintype.card α →
    (1 - ε / 4) * k / Fintype.card α ≤ 1 →
    (1 + ε / 4) * k / Fintype.card α ≤ 1 →
    averagedBernoulliFailureProbability μ
      ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ →
    averagedBernoulliFailureProbability μ
      ((1 + ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ →
    averagedFixedFailureProbability (k := k) μ ε X ≤
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48))

/-- Independence gives the iterated finite-noise probability, for any joint
realization. Instantiations use q(e)=bernoulliWeight θ e, or the constant
1/card(FixedSubset α k). Measurability of the Gram failure sets and the
normalization/marginal identities for these two finite laws must be supplied
in their applications. No desired sampling estimate is an assumption. -/
def FiniteNoiseFailureLawExpected : Prop := by
  classical
  exact ∀ (Ω α β : Type) [MeasurableSpace Ω] [Fintype α]
    [DecidableEq α] [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r : ℕ)
    (X : Ω → Matrix α (Fin r) ℝ) (S : Ω → β)
    (q : β → ℝ) (event : Matrix α (Fin r) ℝ → β → Prop),
    Measurable (fun ω ↦ fun i j ↦ X ω i j) → Measurable S →
    IndepFun (fun ω ↦ fun i j ↦ X ω i j) S μ →
    (∀ b, MeasurableSet {A : α → Fin r → ℝ | event A b}) →
    (∀ b, 0 ≤ q b) → (∑ b, q b) = 1 →
    (∀ b, μ.real {ω | S ω = b} = q b) →
    μ.real {ω | event (X ω) (S ω)} =
      ∫ ω, (∑ b, if event (X ω) b then q b else 0) ∂μ

end Problem56.PaperV6
