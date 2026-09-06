import Problem56.Definitions

/-! Counting a small vertex support together with a pairing of internal occurrences. -/

open scoped BigOperators

namespace Problem56

private theorem selector_excess_sum {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) :
    ∑ B ∈ Q.1.parts, (B.card - 2) = 2 * s := by
  have hpartsne : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  have hpartspos : 0 < Q.1.parts.card := Finset.card_pos.mpr hpartsne
  have hslt : s < p := by
    rw [Q.2.2.1] at hpartspos
    omega
  rw [Finset.sum_tsub_distrib Q.1.parts Q.2.1]
  rw [Q.1.sum_card_parts]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const_nat]
  rw [Q.2.2.1]
  omega

private theorem occurrenceWithinVertices_card_le {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) (h : ℕ)
    (U : Finset (EqualityVertex Q.1)) (hU : U.card ≤ 4 * h) :
    (occurrenceWithinVertices Q U).card ≤ 8 * h + 2 * s := by
  classical
  let blocks : Finset (Finset (Fin (2 * p))) :=
    U.map ⟨Subtype.val, Subtype.val_injective⟩
  have hblocks : blocks ⊆ Q.1.parts := by
    intro B hB
    rw [Finset.mem_map] at hB
    obtain ⟨u, hu, rfl⟩ := hB
    exact u.2
  have hocc : occurrenceWithinVertices Q U ⊆ U.biUnion (fun u ↦ u.1) := by
    intro e he
    have he' := (Finset.mem_filter.mp he).2.1
    exact Finset.mem_biUnion.mpr
      ⟨equalityVertexAt Q.1 e, he', Q.1.mem_part (Finset.mem_univ e)⟩
  have hsumU :
      (∑ u ∈ U, (u.1.card - 2)) = ∑ B ∈ blocks, (B.card - 2) := by
    simp [blocks]
  have hexcessU : (∑ u ∈ U, (u.1.card - 2)) ≤ 2 * s := by
    rw [hsumU, ← selector_excess_sum hp Q]
    exact Finset.sum_le_sum_of_subset_of_nonneg hblocks
      (fun _ _ _ ↦ Nat.zero_le _)
  calc
    (occurrenceWithinVertices Q U).card ≤ (U.biUnion (fun u ↦ u.1)).card :=
      Finset.card_le_card hocc
    _ ≤ ∑ u ∈ U, u.1.card := Finset.card_biUnion_le
    _ = ∑ u ∈ U, ((u.1.card - 2) + 2) := by
      apply Finset.sum_congr rfl
      intro u hu
      have huLarge : 2 ≤ u.1.card := Q.2.1 u.1 u.2
      omega
    _ = (∑ u ∈ U, (u.1.card - 2)) + 2 * U.card := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ ≤ 2 * s + 2 * (4 * h) := add_le_add hexcessU (Nat.mul_le_mul_left 2 hU)
    _ = 8 * h + 2 * s := by omega

private def equalityVertexRepresentative {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1) : Fin (2 * p) :=
  u.1.min' (Q.1.nonempty_of_mem_parts u.2)

private theorem equalityVertexRepresentative_injective {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    Function.Injective (equalityVertexRepresentative Q) := by
  intro u v huv
  apply Subtype.ext
  apply Q.1.eq_of_mem_parts (a := equalityVertexRepresentative Q u) u.2 v.2
  · exact Finset.min'_mem u.1 (Q.1.nonempty_of_mem_parts u.2)
  · have hv : equalityVertexRepresentative Q u ∈ v.1 := by
      rw [huv]
      exact Finset.min'_mem v.1 (Q.1.nonempty_of_mem_parts v.2)
    exact hv

private noncomputable def disjointVertexCode {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (h : ℕ) (U : {U : Finset (EqualityVertex Q.1) // U.card ≤ 4 * h}) :
    Fin (4 * h) → Option (Fin (2 * p)) := fun i ↦
  if hi : i.1 < U.1.card then
    let j : Fin U.1.card := ⟨i.1, hi⟩
    some (equalityVertexRepresentative Q (U.1.equivFin.symm j).1)
  else
    none

private theorem disjointVertexCode_support {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (h : ℕ)
    (U : {U : Finset (EqualityVertex Q.1) // U.card ≤ 4 * h})
    (u : EqualityVertex Q.1) :
    u ∈ U.1 ↔ ∃ i, disjointVertexCode Q h U i = some (equalityVertexRepresentative Q u) := by
  constructor
  · intro hu
    let j : Fin U.1.card := U.1.equivFin ⟨u, hu⟩
    have hj : j.1 < 4 * h := lt_of_lt_of_le j.2 U.2
    let i : Fin (4 * h) := ⟨j.1, hj⟩
    refine ⟨i, ?_⟩
    simp [disjointVertexCode, i, j]
  · rintro ⟨i, hi⟩
    simp only [disjointVertexCode] at hi
    split at hi
    · have hmem := (U.1.equivFin.symm (⟨i.1, ‹i.1 < U.1.card›⟩)).2
      have heq : (U.1.equivFin.symm (⟨i.1, ‹i.1 < U.1.card›⟩)).1 = u :=
        equalityVertexRepresentative_injective Q (Option.some.inj hi)
      rw [heq] at hmem
      exact hmem
    · simp at hi

private theorem pairing_existsUnique_mate {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    ∃! y, y ∈ P.1.part x ∧ y ≠ x := by
  have hxpart : x ∈ P.1.part x := P.1.mem_part hx
  have hcard : (P.1.part x).card = 2 := P.2 _ (P.1.part_mem.2 hx)
  have herase : ((P.1.part x).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxpart, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp herase
  refine ⟨y, ?_, ?_⟩
  · have hyerase : y ∈ (P.1.part x).erase x := by rw [hy]; simp
    exact ⟨Finset.mem_of_mem_erase hyerase, Finset.ne_of_mem_erase hyerase⟩
  · intro z hz
    have hzerase : z ∈ (P.1.part x).erase x :=
      Finset.mem_erase.mpr ⟨hz.2, hz.1⟩
    rw [hy] at hzerase
    simpa using hzerase

private def pairingMate {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : α :=
  Finset.choose (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)

private theorem pairingMate_mem {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : pairingMate P x hx ∈ P.1.part x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)).1

private theorem pairingMate_ne {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : pairingMate P x hx ≠ x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)).2

private theorem pairingMate_mem_support {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    pairingMate P x hx ∈ S :=
  P.1.part_subset x (pairingMate_mem P x hx)

private theorem pairingMate_involutive {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    pairingMate P (pairingMate P x hx) (pairingMate_mem_support P x hx) = x := by
  let y := pairingMate P x hx
  have hyPart : y ∈ P.1.part x := pairingMate_mem P x hx
  have hyS : y ∈ S := pairingMate_mem_support P x hx
  have hpart : P.1.part y = P.1.part x :=
    P.1.part_eq_of_mem (P.1.part_mem.2 hx) hyPart
  apply (pairing_existsUnique_mate P y hyS).unique
  · exact (Finset.choose_spec (fun z ↦ z ≠ y) (P.1.part y)
      (pairing_existsUnique_mate P y hyS))
  · constructor
    · rw [hpart]
      exact P.1.mem_part hx
    · exact (pairingMate_ne P x hx).symm

private theorem pairing_part_eq_pair {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    P.1.part x = {x, pairingMate P x hx} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact P.1.mem_part hx
    · exact pairingMate_mem P x hx
  · rw [P.2 _ (P.1.part_mem.2 hx)]
    simp [(pairingMate_ne P x hx).symm]

private def paddedPairingCode {α : Type*} [LinearOrder α] {S : Finset α}
    (L : ℕ) (P : Pairing S) : Fin L → Option α := fun i ↦
  if hi : i.1 < S.card then
    let j : Fin S.card := ⟨i.1, hi⟩
    let x : α := S.orderEmbOfFin rfl j
    some (pairingMate P x (S.orderEmbOfFin_mem rfl j))
  else
    none

private theorem paddedPairingCode_support {α : Type*} [LinearOrder α]
    {S : Finset α} (L : ℕ) (P : Pairing S) (hS : S.card ≤ L) (x : α) :
    x ∈ S ↔ ∃ i, paddedPairingCode L P i = some x := by
  constructor
  · intro hx
    let y := pairingMate P x hx
    have hy : y ∈ S := pairingMate_mem_support P x hx
    let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨y, hy⟩
    have hj : j.1 < L := lt_of_lt_of_le j.2 hS
    let i : Fin L := ⟨j.1, hj⟩
    refine ⟨i, ?_⟩
    have henum : S.orderEmbOfFin rfl j = y := by
      exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨y, hy⟩)
    simp [paddedPairingCode, i, j, henum, y, pairingMate_involutive P x hx]
  · rintro ⟨i, hi⟩
    simp only [paddedPairingCode] at hi
    split at hi
    · have hmem := pairingMate_mem_support P
          (S.orderEmbOfFin rfl (⟨i.1, ‹i.1 < S.card›⟩))
          (S.orderEmbOfFin_mem rfl (⟨i.1, ‹i.1 < S.card›⟩))
      rw [Option.some.inj hi] at hmem
      exact hmem
    · simp at hi

private theorem disjointPairChoice_support_card_le {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) (h : ℕ) (C : DisjointPairChoice Q h) :
    C.2.1.1.card ≤ 8 * h + 2 * s :=
  (Finset.card_le_card C.2.1.2).trans
    (occurrenceWithinVertices_card_le hp Q h C.1.1 C.1.2)

private noncomputable def disjointPairChoiceCode {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (h : ℕ) (C : DisjointPairChoice Q h) :
    (Fin (4 * h) → Option (Fin (2 * p))) ×
      (Fin (8 * h + 2 * s) → Option (Fin (2 * p))) :=
  (disjointVertexCode Q h C.1,
    paddedPairingCode (8 * h + 2 * s) C.2.2)

private theorem disjointPairChoiceCode_injective {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) (h : ℕ) :
    Function.Injective (disjointPairChoiceCode Q h) := by
  intro C₁ C₂ hcode
  have hvertexCode : disjointVertexCode Q h C₁.1 = disjointVertexCode Q h C₂.1 :=
    congrArg Prod.fst hcode
  have hU : C₁.1 = C₂.1 := by
    apply Subtype.ext
    ext u
    rw [disjointVertexCode_support Q h C₁.1 u,
      disjointVertexCode_support Q h C₂.1 u]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hvertexCode]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [hvertexCode]; exact hi⟩
  rcases C₁ with ⟨U, S, P⟩
  rcases C₂ with ⟨V, T, R⟩
  dsimp only at hU
  subst V
  have hpairCode : paddedPairingCode (8 * h + 2 * s) P =
      paddedPairingCode (8 * h + 2 * s) R := congrArg Prod.snd hcode
  have hSbound : S.1.card ≤ 8 * h + 2 * s :=
    disjointPairChoice_support_card_le hp Q h ⟨U, S, P⟩
  have hTbound : T.1.card ≤ 8 * h + 2 * s :=
    disjointPairChoice_support_card_le hp Q h ⟨U, T, R⟩
  have hSTval : S.1 = T.1 := by
    ext x
    rw [paddedPairingCode_support (8 * h + 2 * s) P hSbound x,
      paddedPairingCode_support (8 * h + 2 * s) R hTbound x]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hpairCode]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [hpairCode]; exact hi⟩
  have hST : S = T := Subtype.ext hSTval
  subst T
  have hmate : ∀ (x : Fin (2 * p)) (hx : x ∈ S.1),
      pairingMate P x hx = pairingMate R x hx := by
    intro x hx
    let j : Fin S.1.card := (S.1.orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hj : j.1 < 8 * h + 2 * s := lt_of_lt_of_le j.2 hSbound
    let i : Fin (8 * h + 2 * s) := ⟨j.1, hj⟩
    have henum : S.1.orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val ((S.1.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    have hi : i.1 < S.1.card := j.2
    have hc := congrFun hpairCode i
    simpa [paddedPairingCode, i, j, hi, henum] using hc
  have hPRval : P.1 = R.1 := by
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      obtain ⟨x, hx⟩ := P.1.nonempty_of_mem_parts hB
      have hxS : x ∈ S.1 := P.1.le hB hx
      have hPx : P.1.part x = B := P.1.part_eq_of_mem hB hx
      rw [← hPx, pairing_part_eq_pair P x hxS,
        hmate x hxS, ← pairing_part_eq_pair R x hxS]
      exact R.1.part_mem.2 hxS
    · intro hB
      obtain ⟨x, hx⟩ := R.1.nonempty_of_mem_parts hB
      have hxS : x ∈ S.1 := R.1.le hB hx
      have hRx : R.1.part x = B := R.1.part_eq_of_mem hB hx
      rw [← hRx, pairing_part_eq_pair R x hxS,
        ← hmate x hxS, ← pairing_part_eq_pair P x hxS]
      exact P.1.part_mem.2 hxS
  have hPR : P = R := Subtype.ext hPRval
  subst R
  rfl

theorem disjoint_pair_support_bound
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) (h : ℕ) :
    (∀ U : Finset (EqualityVertex Q.1), U.card ≤ 4 * h →
      (occurrenceWithinVertices Q U).card ≤ 8 * h + 2 * s) ∧
    Fintype.card (DisjointPairChoice Q h) ≤
      (4 * p + 1) ^ (12 * h + 2 * s) := by
  constructor
  · exact occurrenceWithinVertices_card_le hp Q h
  · calc
      Fintype.card (DisjointPairChoice Q h) ≤
          Fintype.card ((Fin (4 * h) → Option (Fin (2 * p))) ×
            (Fin (8 * h + 2 * s) → Option (Fin (2 * p)))) :=
        Fintype.card_le_of_injective (disjointPairChoiceCode Q h)
          (disjointPairChoiceCode_injective hp Q h)
      _ = (2 * p + 1) ^ (4 * h) * (2 * p + 1) ^ (8 * h + 2 * s) := by
        simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option,
          Fintype.card_fin]
      _ = (2 * p + 1) ^ (12 * h + 2 * s) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ (4 * p + 1) ^ (12 * h + 2 * s) :=
        Nat.pow_le_pow_left (by omega) _

end Problem56
