import Problem56.PaperV6.FormalLogExpected

/-! Finite coefficient truncation and the probability-normalized endpoints.
Expected targets were independently approved before these proofs were written.
-/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

theorem squarefreePow_above_card
    {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) (hf : f ∅ = 0)
    (j : ℕ) : ∀ S : Finset ι, S.card < j → squarefreePow f j S = 0 := by
  induction j with
  | zero => intro S h; omega
  | succ j ih =>
      intro S hS
      rw [squarefreePow, squarefreeMul]
      apply Finset.sum_eq_zero
      intro T hT
      by_cases he : T = ∅
      · simp [he, hf]
      · have hTS : T ⊆ S := Finset.mem_powerset.mp hT
        have hTcard : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        have hcard : (S \ T).card < j := by
          rw [Finset.card_sdiff_of_subset hTS]
          have := Finset.card_le_card hTS
          omega
        rw [ih (S \ T) hcard, mul_zero]

theorem squarefreePowerTruncation : SquarefreePowerTruncationExpected := by
  intro ι _ f hf S j hj
  exact squarefreePow_above_card f hf j S hj

theorem squarefreeLog_empty {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) :
    squarefreeLog m ∅ = 0 := by
  simp [squarefreeLog]

theorem squarefreeExp_empty {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) :
    squarefreeExp f ∅ = 1 := by
  simp [squarefreeExp, squarefreePow, squarefreeUnit]

theorem squarefreeMoment_empty {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ι → Ω → ℝ) :
    squarefreeMoment μ Y ∅ = 1 := by
  simp [squarefreeMoment]

theorem formalLogEmptyCoefficients : FormalLogEmptyCoefficientsExpected := by
  intro Ω ι _ _ μ _ Y
  exact ⟨squarefreeMoment_empty μ Y, squarefreeLog_empty _, squarefreeExp_empty _⟩

end Problem56.PaperV6
