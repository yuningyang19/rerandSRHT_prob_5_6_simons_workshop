import Problem56.Definitions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic

/-! Definitions-only proposed expected target for frozen C, lines 2774--2789.
Pending independent scope approval. The underlying law is the actual product
of restricted Lebesgue uniform laws, not a finite ordering surrogate.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

/-- Literal uniform law on the closed unit interval (whose Lebesgue mass is one). -/
noncomputable def continuousUnitUniform : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Canonical independent continuous uniform keys. -/
noncomputable def continuousKeyLaw (α : Type) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α ↦ continuousUnitUniform)

/-- The manuscript uses the non-strict threshold, including both endpoints. -/
noncomputable def continuousThreshold {α : Type} (θ : ℝ) (u : α → ℝ) : SignLayer α := by
  classical
  exact fun i ↦ decide (u i ≤ θ)

noncomputable def continuousThresholdSet {α : Type} [Fintype α]
    (θ : ℝ) (u : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun i ↦ u i ≤ θ)

/-- A measurable choice of k smallest keys with a fallback at ties. The
ordering property is required even on ties; no particular tie permutation is
prescribed. Uniformity and all other laws below are conclusions. -/
def ContinuousCouplingExpected : Prop :=
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
        (continuousKeyLaw α).real {u | J u = K} = 1 / Fintype.card (FixedSubset α k)) ∧
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
          (fun p ↦ continuousThreshold θ p.2) (μ.prod (continuousKeyLaw α)))

end Problem56.PaperV6
