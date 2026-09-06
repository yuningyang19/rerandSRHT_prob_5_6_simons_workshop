import Problem56.PaperV6.FormalLogInverse

/-!
Independent reviewer-owned assignments for frozen C I-V6-14, lines 1194–1233.
These explicit expected types were read from the frozen source and the
definitions-only FormalLogExpected module. They check existing theorem terms;
they do not supply a new coefficient proof or alter its provenance.
-/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

-- Ordered nonempty blocks give j! copies of each unordered partition.
example : (by
    classical
    exact ∀ (ι : Type) [DecidableEq ι] (f : Finset ι → ℝ), f ∅ = 0 →
      ∀ (S : Finset ι) (j : ℕ),
        squarefreePow f j S = (Nat.factorial j : ℝ) *
          ∑ P : Finpartition S,
            if P.parts.card = j then ∏ B ∈ P.parts, f B else 0) :=
  squarefreePowerCoefficient

-- The truncation bound includes empty S and excludes a nonzero constant term.
example : ∀ (ι : Type) [DecidableEq ι] (f : Finset ι → ℝ), f ∅ = 0 →
    ∀ (S : Finset ι) (j : ℕ), S.card < j → squarefreePow f j S = 0 :=
  squarefreePowerTruncation

-- Every nonempty occurrence subset has its actual joint cumulant coefficient.
example : ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    ∀ S : Finset ι, S.Nonempty →
      squarefreeLog (squarefreeMoment μ Y) S =
        measureJointCumulant μ (fun j : S ↦ Y j.1) :=
  formalLogMomentCoefficient

-- The exponential/logarithm recovery includes S = empty.
example : ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    ∀ S : Finset ι,
      squarefreeExp (squarefreeLog (squarefreeMoment μ Y)) S =
        squarefreeMoment μ Y S :=
  formalExpLogMoment

-- Normalization is probability normalization, not an assumed target identity.
example : ∀ (Ω ι : Type) [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ι → Ω → ℝ),
      squarefreeMoment μ Y ∅ = 1 ∧
      squarefreeLog (squarefreeMoment μ Y) ∅ = 0 ∧
      squarefreeExp (squarefreeLog (squarefreeMoment μ Y)) ∅ = 1 :=
  formalLogEmptyCoefficients

example : SquarefreePowerCoefficientExpected ∧ SquarefreePowerTruncationExpected ∧
    FormalLogMomentCoefficientExpected ∧ FormalExpLogMomentExpected ∧
    FormalLogEmptyCoefficientsExpected :=
  formalLogMomentInterface

end Problem56.PaperV6
