import Problem56.PaperV6.GeneralSamplingExpected

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

/-- Concrete joint-realization reading of frozen v6 lem:sampling.
The exact finite marginals below are the uniform-subset and independent
Bernoulli-coordinate laws, not assumptions about spectral failure. -/
def GeneralSamplingJointExpected : Prop :=
  ∀ (Ω α : Type) [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r k : ℕ)
    [MeasurableSpace (FixedSubset α k)] [MeasurableSingletonClass (FixedSubset α k)]
    [MeasurableSpace (SignLayer α)] [MeasurableSingletonClass (SignLayer α)]
    (X : Ω → Matrix α (Fin r) ℝ) (S : Ω → FixedSubset α k)
    (Eminus Eplus : Ω → SignLayer α),
    Measurable (fun ω ↦ fun i j ↦ X ω i j) →
    (∀ᵐ ω ∂μ, OrthonormalFrame (X ω)) →
    Measurable S → Measurable Eminus → Measurable Eplus →
    IndepFun (fun ω ↦ fun i j ↦ X ω i j) S μ →
    IndepFun (fun ω ↦ fun i j ↦ X ω i j) Eminus μ →
    IndepFun (fun ω ↦ fun i j ↦ X ω i j) Eplus μ →
    ∀ (ε γ : ℝ), 0 < ε → ε < 1 → 1 ≤ k → k ≤ Fintype.card α →
    let θminus := (1 - ε / 4) * k / Fintype.card α
    let θplus := (1 + ε / 4) * k / Fintype.card α
    θminus ≤ 1 → θplus ≤ 1 →
    (∀ J, μ.real {ω | S ω = J} = 1 / Fintype.card (FixedSubset α k)) →
    (∀ e, μ.real {ω | Eminus ω = e} = bernoulliWeight θminus e) →
    (∀ e, μ.real {ω | Eplus ω = e} = bernoulliWeight θplus e) →
    μ.real {ω | euclideanOperatorNorm (bernoulliGram θminus (X ω) (Eminus ω) - 1) > ε / 4} ≤ γ →
    μ.real {ω | euclideanOperatorNorm (bernoulliGram θplus (X ω) (Eplus ω) - 1) > ε / 4} ≤ γ →
    μ.real {ω | euclideanOperatorNorm (fixedSampleGram (X ω) (S ω) - 1) > ε} ≤
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48))

end Problem56.PaperV6
