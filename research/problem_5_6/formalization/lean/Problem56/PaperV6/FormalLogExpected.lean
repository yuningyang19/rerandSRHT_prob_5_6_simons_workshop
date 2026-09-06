import Problem56.PaperV6.GeneralCumulants

/-!
Definitions-only expected targets for C I-V6-14, lines 1194–1233.
`squarefreeMul` is coefficient multiplication modulo the relations t_i² = 0:
to obtain the squarefree monomial on S, the first factor uses T ⊆ S and the
second factor uses S \ T. Powers are recursively formed using this actual
multiplication. No coefficient is defined in terms of a cumulant.
-/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

noncomputable def squarefreeUnit {ι : Type*} (S : Finset ι) : ℝ := by
  classical
  exact if S = ∅ then 1 else 0

noncomputable def squarefreeMul {ι : Type*} [DecidableEq ι]
    (f g : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T ∈ S.powerset, f T * g (S \ T)

noncomputable def squarefreePow {ι : Type*} [DecidableEq ι]
    (f : Finset ι → ℝ) : ℕ → Finset ι → ℝ
  | 0 => squarefreeUnit
  | j + 1 => squarefreeMul f (squarefreePow f j)

noncomputable def squarefreeLog {ι : Type*} [DecidableEq ι]
    (m : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ j ∈ Finset.range (S.card + 1),
    if j = 0 then 0 else
      ((-1 : ℝ) ^ (j - 1) / (j : ℝ)) *
        squarefreePow (fun T ↦ m T - squarefreeUnit T) j S

noncomputable def squarefreeExp {ι : Type*} [DecidableEq ι]
    (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ j ∈ Finset.range (S.card + 1),
    squarefreePow f j S / (Nat.factorial j : ℝ)

noncomputable def squarefreeMoment {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  ∫ ω, (∏ j ∈ S, Y j ω) ∂μ

def SquarefreePowerCoefficientExpected : Prop := by
  classical
  exact ∀ (ι : Type) [DecidableEq ι] (f : Finset ι → ℝ), f ∅ = 0 →
    ∀ (S : Finset ι) (j : ℕ),
      squarefreePow f j S = (Nat.factorial j : ℝ) *
        ∑ P : Finpartition S,
          if P.parts.card = j then ∏ B ∈ P.parts, f B else 0

def SquarefreePowerTruncationExpected : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (f : Finset ι → ℝ), f ∅ = 0 →
    ∀ (S : Finset ι) (j : ℕ), S.card < j → squarefreePow f j S = 0

def FormalLogMomentCoefficientExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    ∀ S : Finset ι, S.Nonempty →
      squarefreeLog (squarefreeMoment μ Y) S =
        measureJointCumulant μ (fun j : S ↦ Y j.1)

def FormalExpLogMomentExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ), FiniteJointMoments μ Y →
    ∀ S : Finset ι,
      squarefreeExp (squarefreeLog (squarefreeMoment μ Y)) S =
        squarefreeMoment μ Y S

def FormalLogEmptyCoefficientsExpected : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ι → Ω → ℝ),
      squarefreeMoment μ Y ∅ = 1 ∧
      squarefreeLog (squarefreeMoment μ Y) ∅ = 0 ∧
      squarefreeExp (squarefreeLog (squarefreeMoment μ Y)) ∅ = 1

end Problem56.PaperV6
