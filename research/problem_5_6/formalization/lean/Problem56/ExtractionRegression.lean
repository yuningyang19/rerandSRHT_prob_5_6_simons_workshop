import Problem56.Definitions

/-!
Definitions-only extraction regressions for the four Gate-3 boundary cases.

This file deliberately does not import `Problem56.Statements`: every witness and
contradiction below is checked directly from the frozen definitions, without
depending on any admitted public theorem.
-/

open scoped BigOperators

namespace Problem56.ExtractionRegression

/-! ## I35: unconditional sandwich support is impossible -/

private def emptyUpperSign : SignLayer (Fin 2) := fun _ ↦ false

theorem i35_empty_upper_mass_and_guard :
    bernoulliWeight (((1 + (1 / 8 : ℝ)) * 1 / 2)) emptyUpperSign = 49 / 256 ∧
      ¬ 1 ≤ ((Finset.univ.filter fun i : Fin 2 ↦ emptyUpperSign i).card) := by
  constructor
  · norm_num [bernoulliWeight, emptyUpperSign, Fin.prod_univ_two]
  · norm_num [emptyUpperSign]

theorem i35_unconditional_support_conflict
    (coupling : FixedSubset (Fin 2) 1 × SignLayer (Fin 2) ×
        SignLayer (Fin 2) → ℝ)
    (hsupport : ∀ sample, coupling sample ≠ 0 →
      (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
      (∀ i, i ∈ sample.1.1 → sample.2.2 i = true))
    (hupper : ∀ bplus,
      (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
        bernoulliWeight (((1 + (1 / 8 : ℝ)) * 1 / 2)) bplus) :
    False := by
  have hzero : ∀ (J : FixedSubset (Fin 2) 1) (bminus : SignLayer (Fin 2)),
      coupling (J, bminus, emptyUpperSign) = 0 := by
    intro J bminus
    by_contra hne
    have hsubset := (hsupport (J, bminus, emptyUpperSign) hne).2
    have hJ : J.1.Nonempty := Finset.card_pos.mp (by simp [J.2])
    obtain ⟨i, hi⟩ := hJ
    have := hsubset i hi
    simp [emptyUpperSign] at this
  have hmarginal := hupper emptyUpperSign
  simp_rw [hzero] at hmarginal
  rw [i35_empty_upper_mass_and_guard.1] at hmarginal
  norm_num at hmarginal

/-! ## I16: truncated subtraction admits empty selector data -/

private def emptyFinPartition :
    Finpartition (Finset.univ : Finset (Fin 0)) :=
  (Finpartition.empty (Finset (Fin 0))).copy (by simp)

private def i16EmptySelectorData : SelectorEqualityData 0 1 0 := by
  refine ⟨emptyFinPartition, ?_⟩
  simp [emptyFinPartition, equalityOddIncidentVertices]

theorem i16_empty_selector_counterexample :
    ∃ _Q : SelectorEqualityData 0 1 0, ¬ 1 ≤ 0 - 1 := by
  exact ⟨i16EmptySelectorData, by omega⟩

theorem i16_expected_rank_guard : ¬ 2 ≤ (0 : ℕ) := by omega

/-! ## I19: the one-block two-loop endpoint is not in the three classes -/

private def twoLoopPartition :
    Finpartition (Finset.univ : Finset (Fin 2)) :=
  Finpartition.indiscrete (by
    intro h
    have hmem : (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
    rw [h] at hmem
    simp at hmem)

private lemma twoLoopPartition_part (i : Fin 2) :
    twoLoopPartition.part i = Finset.univ := by
  apply twoLoopPartition.part_eq_of_mem
  · simp [twoLoopPartition]
  · simp

private def i19TwoLoopSelectorData : SelectorEqualityData 1 0 0 := by
  refine ⟨twoLoopPartition, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    have hB' : B = (Finset.univ : Finset (Fin 2)) := by
      simpa [twoLoopPartition] using hB
    subst B
    simp
  · simp [twoLoopPartition]
  · simp [equalityOddIncidentVertices, twoLoopPartition]

private def twoLoopBlock : Finset (Fin 2) := Finset.univ

theorem i19_two_loop_endpoint_counterexample :
    twoLoopBlock ∈ i19TwoLoopSelectorData.1.parts ∧
    twoLoopBlock ∉ equalityExceptionalVertices i19TwoLoopSelectorData.1 ∧
    equalityLoopOccurrences i19TwoLoopSelectorData.1 = 2 ∧
    ¬ IsEqualityInternal i19TwoLoopSelectorData.1 twoLoopBlock ∧
    ¬ IsEqualityLoopTerminal i19TwoLoopSelectorData.1 twoLoopBlock ∧
    ¬ IsEqualityFourEdgeTerminal i19TwoLoopSelectorData.1 twoLoopBlock := by
  have hparts : i19TwoLoopSelectorData.1.parts =
      {(Finset.univ : Finset (Fin 2))} := by
    rfl
  have hodd : equalityOddIncidentVertices i19TwoLoopSelectorData.1 = ∅ := by
    simp [equalityOddIncidentVertices, hparts]
  have hexceptional : equalityExceptionalVertices i19TwoLoopSelectorData.1 = ∅ := by
    simp [equalityExceptionalVertices, hodd, hparts]
  have hloopOccurrences : equalityLoopOccurrences i19TwoLoopSelectorData.1 = 2 := by
    simp [equalityLoopOccurrences, i19TwoLoopSelectorData,
      twoLoopPartition_part]
  have hloopsAt : equalityLoopsAt i19TwoLoopSelectorData.1 twoLoopBlock = 2 := by
    simp [equalityLoopsAt, i19TwoLoopSelectorData, twoLoopBlock,
      twoLoopPartition_part]
  refine ⟨?_, ?_, hloopOccurrences, ?_, ?_, ?_⟩
  · simp [hparts, twoLoopBlock]
  · simp [hexceptional]
  · intro h
    have hz := h.1
    rw [hloopsAt] at hz
    omega
  · intro h
    have hone := h.1
    rw [hloopsAt] at hone
    omega
  · intro h
    have hz := h.1
    rw [hloopsAt] at hz
    omega

theorem i19_expected_rank_guard : ¬ 2 ≤ (1 : ℕ) := by omega

/-! ## I08: uniform expectation on the empty sample space -/

private def emptyVariables : Fin 0 → Empty → ℝ := fun i ↦ Fin.elim0 i

theorem i08_empty_lhs :
    uniformExpectation (Ω := Empty)
      (fun ω ↦ ∏ j : Fin 0, emptyVariables j ω) = 0 := by
  simp [uniformExpectation]

theorem i08_empty_rhs :
    (∑ P : Finpartition (Finset.univ : Finset (Fin 0)),
      ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ emptyVariables j.1)) = 1 := by
  classical
  rw [show (Finset.univ :
      Finset (Finpartition (Finset.univ : Finset (Fin 0)))) =
        {emptyFinPartition} by
    ext P
    have hP : P = emptyFinPartition := by
      ext B
      have hparts : P.parts = ∅ :=
        Finpartition.parts_eq_empty_iff.mpr (by simp)
      simp [hparts, emptyFinPartition]
    simp [hP]]
  simp [emptyFinPartition]

theorem i08_empty_boundary_conflict :
    uniformExpectation (Ω := Empty)
      (fun ω ↦ ∏ j : Fin 0, emptyVariables j ω) ≠
    ∑ P : Finpartition (Finset.univ : Finset (Fin 0)),
      ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ emptyVariables j.1) := by
  rw [i08_empty_lhs, i08_empty_rhs]
  norm_num

theorem i08_expected_nonempty_guard : ¬ Nonempty Empty := by simp

#print axioms i35_empty_upper_mass_and_guard
#print axioms i35_unconditional_support_conflict
#print axioms i16_empty_selector_counterexample
#print axioms i16_expected_rank_guard
#print axioms i19_two_loop_endpoint_counterexample
#print axioms i19_expected_rank_guard
#print axioms i08_empty_lhs
#print axioms i08_empty_rhs
#print axioms i08_empty_boundary_conflict
#print axioms i08_expected_nonempty_guard

end Problem56.ExtractionRegression
