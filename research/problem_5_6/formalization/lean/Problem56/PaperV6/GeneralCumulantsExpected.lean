import Problem56.ProductCumulant
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration

/-!
Expected statements for frozen v6 `lem:cumulant-identities`.
These definitions state obligations; they assert no theorem or axiom.
The sample space is arbitrary, scalar values are real, and all products of
distinct occurrence positions have finite absolute first moment. Repeated
random variables remain permitted at distinct occurrence positions.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

def FiniteJointMoments {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) (Y : ι → Ω → ℝ) : Prop :=
  ∀ B : Finset ι, Integrable (fun ω ↦ ∏ j ∈ B, Y j ω) μ

noncomputable def measureJointCumulant {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (μ : Measure Ω) (Y : ι → Ω → ℝ) : ℝ :=
  ∑ P : Finpartition (Finset.univ : Finset ι),
    ((-1 : ℝ) ^ (P.parts.card - 1) * (Nat.factorial (P.parts.card - 1) : ℝ)) *
      ∏ B ∈ P.parts, ∫ ω, (∏ j ∈ B, Y j ω) ∂μ

noncomputable def measurePartitionCumulantProduct {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) : ℝ :=
  ∏ B ∈ P.parts, measureJointCumulant μ (fun j : B ↦ Y j.1)

def GeneralMomentIdentityExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    (∫ ω, (∏ j, Y j ω) ∂μ) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        measurePartitionCumulantProduct μ Y P

def GeneralProductIdentityExpected : Prop := by
  classical
  exact ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    ∀ τ : Finpartition (Finset.univ : Finset ι),
    measureJointCumulant μ (fun B : τ.parts ↦ fun ω ↦ ∏ j ∈ B.1, Y j ω) =
      ∑ σ : Finpartition (Finset.univ : Finset ι),
        if ProductPartitionConnected σ τ then
          measurePartitionCumulantProduct μ Y σ else 0

/-- Linearity in any chosen argument, on the domain of finite joint moments.
The two input families have finite moments; their linear combination needs no
extra moment hypothesis, since that is a consequence of these two hypotheses. -/
def GeneralMultilinearityExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (i : ι) (U V : Ω → ℝ) (a b : ℝ),
    FiniteJointMoments μ (Function.update Y i U) →
    FiniteJointMoments μ (Function.update Y i V) →
    measureJointCumulant μ (Function.update Y i (fun ω ↦ a * U ω + b * V ω)) =
      a * measureJointCumulant μ (Function.update Y i U) +
      b * measureJointCumulant μ (Function.update Y i V)

def GeneralMixedIndependenceExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    ∀ (A B : Finset ι), A.Nonempty → B.Nonempty → Disjoint A B →
    A ∪ B = Finset.univ →
    IndepFun (fun ω ↦ fun j : A ↦ Y j.1 ω)
      (fun ω ↦ fun j : B ↦ Y j.1 ω) μ →
    measureJointCumulant μ Y = 0

def GeneralShiftInvarianceExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (c : ι → ℝ), 2 ≤ Fintype.card ι →
    FiniteJointMoments μ Y →
    measureJointCumulant μ (fun j ω ↦ Y j ω + c j) = measureJointCumulant μ Y

def GeneralOddSymmetryExpected : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (q : ℕ), Odd q →
    FiniteJointMoments μ (fun _ : Fin q ↦ Z) →
    IdentDistrib Z (fun ω ↦ -Z ω) μ μ →
    measureJointCumulant μ (fun _ : Fin q ↦ Z) = 0

end Problem56.PaperV6
