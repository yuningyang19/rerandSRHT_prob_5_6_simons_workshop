import Problem56.PaperV6.FormalLogCoefficients

/-! Exp(log M) coefficient recovery. This uses the already proved general
moment identity as an independent finite partition cancellation theorem; it
does not retroactively change that theorem's proof lineage. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

private noncomputable def formalLog_mappedBlockElementEquiv
    {ι : Type*} [DecidableEq ι] (B : Finset ι) (C : Finset B) :
    C ≃ (C.map
      (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι)) where
  toFun j := ⟨j.1.1, Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩⟩
  invFun j :=
    let h := Finset.mem_map.mp j.2
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  left_inv j := by
    apply Subtype.ext
    let h := Finset.mem_map.mp
      (show j.1.1 ∈ C.map
        (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) from
          Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩)
    apply Subtype.ext
    exact (Classical.choose_spec h).2
  right_inv j := by
    apply Subtype.ext
    let h := Finset.mem_map.mp j.2
    exact (Classical.choose_spec h).2

private theorem formalLog_jointCumulant_mappedBlock
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (B : Finset ι) (C : Finset B) :
    measureJointCumulant μ (fun j : C ↦ Y j.1.1) =
      measureJointCumulant μ (fun j : C.map
        (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) ↦ Y j.1) := by
  calc
    _ = measureJointCumulant μ (fun j : C ↦
          (fun k : C.map
            (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) ↦ Y k.1)
            (formalLog_mappedBlockElementEquiv B C j)) := by
        rfl
    _ = _ := measure_jointCumulantOn_equiv (μ := μ) (formalLog_mappedBlockElementEquiv B C)
      (fun j ↦ Y j.1)


theorem formalLog_lift_cumulant_product
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (S : Finset ι)
    (Q : Finpartition (Finset.univ : Finset S)) :
    (∏ C ∈ Q.parts, measureJointCumulant μ (fun j : C ↦ Y j.1.1)) =
      ∏ B ∈ (liftBlockPartition S Q).parts,
        measureJointCumulant μ (fun j : B ↦ Y j.1) := by
  classical
  rw [liftBlockPartition_parts, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro C _
    exact formalLog_jointCumulant_mappedBlock μ Y S C
  · intro C _ D _ hCD
    exact Finset.map_injective (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ ι) hCD

theorem formalLog_ambient_moment_inverse
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (S : Finset ι) (hS : S.Nonempty) :
    squarefreeMoment μ Y S = ∑ P : Finpartition S,
      ∏ B ∈ P.parts, measureJointCumulant μ (fun j : B ↦ Y j.1) := by
  classical
  letI : Nonempty S := Finset.nonempty_coe_sort.mpr hS
  calc
    _ = ∫ ω, (∏ j : S, Y j.1 ω) ∂μ := by
      unfold squarefreeMoment
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ (Finset.prod_coe_sort S (fun j ↦ Y j ω)).symm
    _ = ∑ Q : Finpartition (Finset.univ : Finset S),
        ∏ C ∈ Q.parts, measureJointCumulant μ (fun j : C ↦ Y j.1.1) :=
      measure_moment_cumulant_inverse_nonempty_index μ (fun j : S ↦ Y j.1)
    _ = _ := by
      apply Fintype.sum_equiv (formalLogFinpartitionEquiv S)
      intro Q
      exact formalLog_lift_cumulant_product μ Y S Q

theorem formalExpLogMoment : FormalExpLogMomentExpected := by
  intro Ω ι _ _ _ μ _ Y hY S
  classical
  by_cases hS : S = ∅
  · simp [hS, squarefreeExp_empty, squarefreeMoment_empty]
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rw [squarefreeExp_partition _ (squarefreeLog_empty _) S]
    calc
      _ = ∑ P : Finpartition S, ∏ B ∈ P.parts,
          measureJointCumulant μ (fun j : B ↦ Y j.1) := by
        apply Finset.sum_congr rfl
        intro P _
        apply Finset.prod_congr rfl
        intro B hB
        exact formalLogMomentCoefficient Ω ι μ Y hY B (P.nonempty_of_mem_parts hB)
      _ = _ := (formalLog_ambient_moment_inverse μ Y S hSne).symm

theorem formalLogMomentInterface :
    SquarefreePowerCoefficientExpected ∧ SquarefreePowerTruncationExpected ∧
    FormalLogMomentCoefficientExpected ∧ FormalExpLogMomentExpected ∧
    FormalLogEmptyCoefficientsExpected :=
  ⟨squarefreePowerCoefficient, squarefreePowerTruncation, formalLogMomentCoefficient,
    formalExpLogMoment, formalLogEmptyCoefficients⟩

end Problem56.PaperV6
