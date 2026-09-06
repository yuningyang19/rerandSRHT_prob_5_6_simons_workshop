import Problem56.Definitions

/-! Finite block-cardinality accounting for the selector equality graph. -/

open scoped BigOperators

namespace Problem56

theorem selector_exceptional_vertex_degree_budget
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (equalityExceptionalVertices Q.1).card ≤ t + 2 * s ∧
    equalityExceptionalDegree Q.1 ≤ 4 * t + 12 * s := by
  classical
  let O := equalityOddIncidentVertices Q.1
  let L := Q.1.parts.filter fun B ↦ 2 < B.card
  have hOsub : O ⊆ Q.1.parts := by
    intro B hB
    exact (Finset.mem_filter.mp hB).1
  have hLsub : L ⊆ Q.1.parts := Finset.filter_subset _ _
  have hpartsne : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  have hpartspos : 0 < Q.1.parts.card := Finset.card_pos.mpr hpartsne
  have hslt : s < p := by
    rw [Q.2.2.1] at hpartspos
    omega
  have hexcess : ∑ B ∈ Q.1.parts, (B.card - 2) = 2 * s := by
    rw [Finset.sum_tsub_distrib Q.1.parts Q.2.1]
    rw [Q.1.sum_card_parts]
    simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const_nat]
    rw [Q.2.2.1]
    omega
  have hlargeCard : L.card ≤ 2 * s := by
    calc
      L.card = ∑ _B ∈ L, 1 := by simp
      _ ≤ ∑ B ∈ L, (B.card - 2) := by
        apply Finset.sum_le_sum
        intro B hB
        have hlarge : 2 < B.card := (Finset.mem_filter.mp hB).2
        omega
      _ ≤ ∑ B ∈ Q.1.parts, (B.card - 2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hLsub
          (fun _ _ _ ↦ Nat.zero_le _)
      _ = 2 * s := hexcess
  have hlargeDegree : ∑ B ∈ L, 2 * B.card ≤ 12 * s := by
    calc
      (∑ B ∈ L, 2 * B.card) ≤ ∑ B ∈ L, 6 * (B.card - 2) := by
        apply Finset.sum_le_sum
        intro B hB
        have hlarge : 2 < B.card := (Finset.mem_filter.mp hB).2
        omega
      _ = 6 * ∑ B ∈ L, (B.card - 2) := by
        rw [Finset.mul_sum]
      _ ≤ 6 * ∑ B ∈ Q.1.parts, (B.card - 2) := by
        exact Nat.mul_le_mul_left 6
          (Finset.sum_le_sum_of_subset_of_nonneg hLsub
            (fun _ _ _ ↦ Nat.zero_le _))
      _ = 12 * s := by rw [hexcess]; omega
  have hEsub : O ∪ L ⊆ Q.1.parts := Finset.union_subset hOsub hLsub
  have hfilterO : Q.1.parts.filter (fun B ↦ B ∈ O) = O := by
    ext B
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hOsub h, h⟩
  have hfilterL : Q.1.parts.filter (fun B ↦ B ∈ L) = L := by
    ext B
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hLsub h, h⟩
  have hsumO :
      (∑ B ∈ Q.1.parts, if B ∈ O then 4 else 0) = 4 * O.card := by
    rw [← Finset.sum_filter, hfilterO]
    simp [Nat.mul_comm]
  have hsumL :
      (∑ B ∈ Q.1.parts, if B ∈ L then 2 * B.card else 0) =
        ∑ B ∈ L, 2 * B.card := by
    rw [← Finset.sum_filter, hfilterL]
  constructor
  · change (O ∪ L).card ≤ t + 2 * s
    calc
      (O ∪ L).card ≤ O.card + L.card := Finset.card_union_le _ _
      _ ≤ t + 2 * s := by
        have hOcard : O.card = t := Q.2.2.2
        omega
  · change (∑ B ∈ O ∪ L, 2 * B.card) ≤ 4 * t + 12 * s
    calc
      (∑ B ∈ O ∪ L, 2 * B.card) ≤
          ∑ B ∈ O ∪ L,
            ((if B ∈ O then 4 else 0) +
              if B ∈ L then 2 * B.card else 0) := by
        apply Finset.sum_le_sum
        intro B hB
        by_cases hBL : B ∈ L
        · simp [hBL]
        · have hBO : B ∈ O := (Finset.mem_union.mp hB).resolve_right hBL
          have hBpart : B ∈ Q.1.parts := hOsub hBO
          have hcard : B.card ≤ 2 := by
            simp only [L, Finset.mem_filter, hBpart, true_and] at hBL
            omega
          simp [hBO, hBL]
          omega
      _ ≤ ∑ B ∈ Q.1.parts,
            ((if B ∈ O then 4 else 0) +
              if B ∈ L then 2 * B.card else 0) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hEsub
          (fun _ _ _ ↦ Nat.zero_le _)
      _ = 4 * O.card + ∑ B ∈ L, 2 * B.card := by
        rw [Finset.sum_add_distrib, hsumO, hsumL]
      _ ≤ 4 * t + 12 * s := by
        have hOcard : O.card = t := Q.2.2.2
        omega

#print axioms selector_exceptional_vertex_degree_budget

end Problem56
