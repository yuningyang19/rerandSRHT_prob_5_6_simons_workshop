import Problem56.PaperV6.FormalLogPartitions

/-! Ordered-partition multiplicity from the actual coefficient multiplication. -/
open scoped BigOperators
namespace Problem56.PaperV6

theorem formalLog_sum_nonempty_subsets
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : Finset ι → ℝ)
    (hg : g ∅ = 0) :
    (∑ T ∈ S.powerset, g T) = ∑ T : FormalLogNonemptySubset S, g T.1.1 := by
  classical
  rw [← Finset.sum_coe_sort S.powerset g]
  calc
    (∑ T : S.powerset, g T.1) =
        ∑ T ∈ (Finset.univ : Finset S.powerset).filter (fun T ↦ T.1.Nonempty), g T.1 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro T _ hT
      have hne : ¬T.1.Nonempty := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hT
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, hg]
    _ = _ := Finset.sum_subtype _ (by simp) (fun T : S.powerset ↦ g T.1)

theorem formalLog_convolution_partition_sum
    {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) (hf : f ∅ = 0)
    (S : Finset ι) (j : ℕ) :
    (∑ T ∈ S.powerset, f T *
      ∑ Q : Finpartition (S \ T), if Q.parts.card = j then ∏ B ∈ Q.parts, f B else 0) =
      (j + 1 : ℝ) * ∑ P : Finpartition S,
        if P.parts.card = j + 1 then ∏ B ∈ P.parts, f B else 0 := by
  classical
  rw [formalLog_sum_nonempty_subsets S _ (by simp [hf])]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ x : FormalLogSplit S,
        f x.1.1.1 * (if x.2.parts.card = j then ∏ B ∈ x.2.parts, f B else 0) :=
      (Fintype.sum_sigma _).symm
    _ = ∑ y : (Σ P : Finpartition S, P.parts),
        if y.1.parts.card = j + 1 then ∏ B ∈ y.1.parts, f B else 0 := by
      apply Fintype.sum_equiv (formalLogSplitEquivPointed S)
      rintro ⟨T, Q⟩
      change f T.1.1 * (if Q.parts.card = j then ∏ B ∈ Q.parts, f B else 0) =
        if (formalLogInsertBlock T Q).parts.card = j + 1 then
          ∏ B ∈ (formalLogInsertBlock T Q).parts, f B else 0
      rw [formalLogInsertBlock_parts,
        Finset.card_insert_of_notMem (formalLogInsertBlock_notMem T Q),
        Finset.prod_insert (formalLogInsertBlock_notMem T Q)]
      by_cases h : Q.parts.card = j <;> simp [h]
    _ = ∑ P : Finpartition S, ∑ _ : P.parts,
        if P.parts.card = j + 1 then ∏ B ∈ P.parts, f B else 0 := Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      by_cases h : P.parts.card = j + 1
      · simp [h, Nat.cast_add, Nat.cast_one]
      · simp [h]

theorem squarefreePow_partition_zero
    {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) (S : Finset ι) :
    squarefreePow f 0 S = (Nat.factorial 0 : ℝ) *
      ∑ P : Finpartition S, if P.parts.card = 0 then ∏ B ∈ P.parts, f B else 0 := by
  classical
  by_cases hS : S = ∅
  · subst S
    letI : Subsingleton (Finpartition (∅ : Finset ι)) := ⟨by
      intro P Q
      ext B
      rw [Finpartition.parts_eq_empty_iff.mpr rfl,
        Finpartition.parts_eq_empty_iff.mpr rfl]⟩
    have hsum := Fintype.sum_subsingleton
      (fun P : Finpartition (∅ : Finset ι) ↦
        if P.parts.card = 0 then ∏ B ∈ P.parts, f B else 0)
      (Finpartition.empty (Finset ι))
    rw [hsum]
    simp [squarefreePow, squarefreeUnit]
  · have hparts (P : Finpartition S) : P.parts.card ≠ 0 :=
      Finset.card_ne_zero.mpr (P.parts_nonempty hS)
    simp [squarefreePow, squarefreeUnit, hS, hparts]

theorem squarefreePow_partition
    {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) (hf : f ∅ = 0)
    (j : ℕ) : ∀ S : Finset ι,
    squarefreePow f j S = (Nat.factorial j : ℝ) *
      ∑ P : Finpartition S, if P.parts.card = j then ∏ B ∈ P.parts, f B else 0 := by
  classical
  induction j with
  | zero => exact squarefreePow_partition_zero f
  | succ j ih =>
      intro S
      rw [squarefreePow, squarefreeMul]
      simp_rw [ih]
      calc
        _ = (Nat.factorial j : ℝ) *
            (∑ T ∈ S.powerset, f T *
              ∑ Q : Finpartition (S \ T),
                if Q.parts.card = j then ∏ B ∈ Q.parts, f B else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          ring
        _ = (Nat.factorial j : ℝ) * ((j + 1 : ℝ) *
            ∑ P : Finpartition S,
              if P.parts.card = j + 1 then ∏ B ∈ P.parts, f B else 0) := by
          rw [formalLog_convolution_partition_sum f hf]
        _ = _ := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring

theorem squarefreePowerCoefficient : SquarefreePowerCoefficientExpected := by
  intro ι _ f hf S j
  exact squarefreePow_partition f hf j S

end Problem56.PaperV6
