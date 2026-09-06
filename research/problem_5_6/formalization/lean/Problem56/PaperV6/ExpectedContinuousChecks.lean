import Problem56.PaperV6.ContinuousCoupling

/-!
Independent reviewer-owned explicit assignment for frozen C I-V6-42.
The law, measurable selection, marginal masses and independence are conclusions.
This assigns an existing proof term; it supplies no new coupling proof.
-/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

example :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (k : ℕ), k ≤ Fintype.card α →
      ∀ [MeasurableSpace (FixedSubset α k)] [MeasurableSingletonClass (FixedSubset α k)]
        [MeasurableSpace (SignLayer α)] [MeasurableSingletonClass (SignLayer α)],
      IsProbabilityMeasure (continuousKeyLaw α) ∧
      (∀ i : α, (continuousKeyLaw α).map (fun u ↦ u i) = continuousUnitUniform) ∧
      iIndepFun (fun (i : α) (u : α → ℝ) ↦ u i) (continuousKeyLaw α) ∧
      (∀ᵐ u ∂continuousKeyLaw α, Function.Injective u) ∧
      ∃ J : (α → ℝ) → FixedSubset α k,
        Measurable J ∧
        (∀ u i, i ∈ (J u).val → ∀ j, j ∉ (J u).val → u i ≤ u j) ∧
        (∀ K : FixedSubset α k,
          (continuousKeyLaw α).real {u | J u = K} =
            1 / Fintype.card (FixedSubset α k)) ∧
        (∀ θ : ℝ, Measurable (continuousThreshold (α := α) θ)) ∧
        (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ e : SignLayer α,
          (continuousKeyLaw α).real {u | continuousThreshold θ u = e} =
            bernoulliWeight θ e) ∧
        (∀ u (θminus θplus : ℝ),
          (continuousThresholdSet θminus u).card ≤ k →
          k ≤ (continuousThresholdSet θplus u).card →
          continuousThresholdSet θminus u ⊆ (J u).val ∧
            (J u).val ⊆ continuousThresholdSet θplus u) ∧
        (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (r : ℕ) (X : Ω → Matrix α (Fin r) ℝ),
          Measurable (fun ω ↦ fun i j ↦ X ω i j) →
          IndepFun (fun p : Ω × (α → ℝ) ↦ fun i j ↦ X p.1 i j)
            (fun p ↦ J p.2) (μ.prod (continuousKeyLaw α)) ∧
          ∀ θ : ℝ, IndepFun (fun p : Ω × (α → ℝ) ↦ fun i j ↦ X p.1 i j)
            (fun p ↦ continuousThreshold θ p.2) (μ.prod (continuousKeyLaw α))) :=
  continuousCoupling

end Problem56.PaperV6
