import Problem56.PaperV6.GraphBridges

open scoped BigOperators Matrix
namespace Problem56.PaperV6

set_option maxHeartbeats 2000000

 theorem pair_eq_iff {α : Type*} [DecidableEq α] (u v w z : α) :
    ({u, v} : Finset α) = {w, z} ↔
      (u = w ∧ v = z) ∨ (u = z ∧ v = w) := by
  constructor
  · intro h
    have hu : u = w ∨ u = z := by
      have : u ∈ ({w, z} : Finset α) := h ▸ (by simp)
      simpa using this
    have hv : v = w ∨ v = z := by
      have : v ∈ ({w, z} : Finset α) := h ▸ (by simp)
      simpa using this
    have hw : w = u ∨ w = v := by
      have : w ∈ ({u, v} : Finset α) := h.symm ▸ (by simp)
      simpa using this
    have hz : z = u ∨ z = v := by
      have : z ∈ ({u, v} : Finset α) := h.symm ▸ (by simp)
      simpa using this
    aesop
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

theorem not_forbidden_iff_surviving {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) (B : Finset (Fin (2 * p))) :
    ¬ PaperForbiddenPairBlock D.selector B ↔ IsSurvivingEntryPairBlock D B := by
  classical
  constructor
  · intro hnot hc e he f hf hef
    let u := equalityVertexAt D.selector.1 e
    let v := equalityVertexAt D.selector.1 (cyclicSucc e)
    let w := equalityVertexAt D.selector.1 f
    let z := equalityVertexAt D.selector.1 (cyclicSucc f)
    change (u = v ∧ w = z) ∨
      (u ≠ v ∧ w ≠ z ∧ ((u = w ∧ v = z) ∨ (u = z ∧ v = w))) ∨
      (u ≠ v ∧ w ≠ z ∧ Disjoint ({u, v} : Finset _) {w, z})
    have hbad : ¬ ((u = v ∧ w ≠ z) ∨ (u ≠ v ∧ w = z) ∨
        (u ≠ v ∧ w ≠ z ∧ ¬ Disjoint ({u, v} : Finset _) {w, z} ∧
          ({u, v} : Finset _) ≠ {w, z})) := by
      intro h
      exact hnot ⟨hc, e, he, f, hf, hef, h⟩
    by_cases huv : u = v
    · left
      refine ⟨huv, ?_⟩
      by_contra hwz
      exact hbad (Or.inl ⟨huv, hwz⟩)
    · by_cases hwz : w = z
      · exact (hbad (Or.inr (Or.inl ⟨huv, hwz⟩))).elim
      · by_cases hd : Disjoint ({u, v} : Finset _) {w, z}
        · exact Or.inr (Or.inr ⟨huv, hwz, hd⟩)
        · right; left
          refine ⟨huv, hwz, (pair_eq_iff u v w z).mp ?_⟩
          by_contra heq
          exact hbad (Or.inr (Or.inr ⟨huv, hwz, hd, heq⟩))
  · intro hsurv hbad
    obtain ⟨hc, e, he, f, hf, hef, hbad⟩ := hbad
    have hs := hsurv hc e he f hf hef
    dsimp only at hs hbad
    rcases hs with ⟨huv, hwz⟩ | ⟨huv, hwz, hpair⟩ | ⟨huv, hwz, hd⟩
    · aesop
    · have hset := (pair_eq_iff _ _ _ _).mpr hpair
      aesop
    · aesop

theorem binary_count : BinaryCountExpected := by
  classical
  intro m p s t D
  have heq : Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
      PaperXorConstraints D lab} =
        walshCard m ^ (D.selector.1.parts.card - Matrix.rank (entryConstraintMatrix D)) :=
    by
      convert entryXorConstraintSolutionCount (m := m) D using 1
      exact Fintype.card_congr (Equiv.refl _)
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact Fintype.card_le_of_injective
    (fun lab : {lab : EqualityVertex D.selector.1 → WalshIndex m //
      Function.Injective lab ∧ PaperXorConstraints D lab} ↦
        (⟨lab.1, lab.2.2⟩ : {lab // PaperXorConstraints D lab}))
    (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : {lab // PaperXorConstraints D lab} ↦ z.1) h)

theorem entry_parts_card_pos {p : ℕ} (hp : 1 ≤ p)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) :
    0 < P.parts.card := by
  apply Finset.card_pos.mpr
  apply P.parts_nonempty
  exact Finset.ne_empty_of_mem
    (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))

theorem binary_odd_incidence : BinaryOddIncidenceExpected := by
  intro p s t d hp D hn hb hf
  have hpos := entry_parts_card_pos (by omega) D.entry
  have hd : d ≤ p - 1 := by omega
  have ha : AdmissibleEntryPairBlocks D := by
    intro B hB
    exact (not_forbidden_iff_surviving D B).mp (hf B hB)
  exact (I24_large_block_and_support_rank_bound hp hd D hn ha hb rfl).2.2.2.2.2

/-- Finite reindexing from B's cyclic block interface to the manuscript sum. -/
theorem paperBlock_xor_sum {m q : ℕ} (x : Fin q → WalshIndex m)
    (B : Finset (Fin q)) :
    (∑ f : Fin B.card,
      (cyclicBlockSourceLabels x B f + cyclicBlockTargetLabels x B f)) =
      ∑ e ∈ B, (x e + x (cyclicSucc e)) := by
  classical
  let e : Fin B.card ≃ B :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
  calc
    _ = ∑ z : B, (x z.1 + x (cyclicSucc z.1)) := by
      apply Fintype.sum_equiv e
      intro f
      rfl
    _ = _ := by rw [Finset.sum_subtype B (fun _ ↦ Iff.rfl)]

theorem binary_forbidden_pair : BinaryForbiddenPairExpected := by
  classical
  intro m r p s t V hV Q B hB lab hinj
  obtain ⟨hc, e, he, f, hf, hef, hbad⟩ := hB
  have hpair : ({e, f} : Finset (Fin (2 * p))) = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      aesop
    · simp [hc, hef]
  have hxor : (∑ x ∈ B,
      (lab (equalityVertexAt Q.1 x) +
        lab (equalityVertexAt Q.1 (cyclicSucc x)))) ≠ 0 := by
    intro hz
    rw [← hpair, Finset.sum_pair hef] at hz
    have hclass := walsh_label_vanishing_pair_classification_of_injective m lab hinj
      (equalityVertexAt Q.1 e) (equalityVertexAt Q.1 (cyclicSucc e))
      (equalityVertexAt Q.1 f) (equalityVertexAt Q.1 (cyclicSucc f))
      (by simpa only [add_assoc] using hz)
    dsimp only at hbad
    simp only [ne_eq, pair_eq_iff] at hbad
    aesop
  have hvan := (centeredProjection_blockCumulant_bound_and_vanish
    (show GraphRankContractionPrinciple from @graph_rank_contraction)
    V hV (fun x ↦ lab (equalityVertexAt Q.1 x)) B (by omega)).2
  apply hvan
  simpa only [paperBlock_xor_sum]
    using hxor

end Problem56.PaperV6
