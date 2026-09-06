import Problem56.LargeBlockSupportRank
import Problem56.LargeBlockCount
import Problem56.DisjointPairCount
import Problem56.PairingParallelBound
import Problem56.EqualityDegreeFour

/-!
The exact weighted entry-partition aggregation from interface I28.
-/

open scoped BigOperators

namespace Problem56

noncomputable section

private noncomputable def selectedParts {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop) :
    Finset (Finset α) := by
  classical
  exact P.parts.filter pred

private noncomputable def selectedSupport {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop) : Finset α :=
  (selectedParts P pred).sup id

private noncomputable def selectedPartition {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop) :
    Finpartition (selectedSupport P pred) := by
  classical
  apply Finpartition.ofPairwiseDisjoint (selectedParts P pred)
  intro A hA B hB hAB
  have hA' : A ∈ P.parts :=
    ((by simpa [selectedParts] using hA) : A ∈ P.parts ∧ pred A).1
  have hB' : B ∈ P.parts :=
    ((by simpa [selectedParts] using hB) : B ∈ P.parts ∧ pred B).1
  exact P.disjoint hA' hB' hAB

private theorem selectedPartition_parts {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop) :
    (selectedPartition P pred).parts = selectedParts P pred := by
  classical
  simp only [selectedPartition, Finpartition.ofPairwiseDisjoint]
  rw [Finset.erase_eq_self.mpr]
  intro h
  have : ∅ ∈ P.parts := by simpa [selectedParts] using h
  exact P.bot_notMem this

private theorem mem_selectedParts {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop)
    (B : Finset α) :
    B ∈ selectedParts P pred ↔ B ∈ P.parts ∧ pred B := by
  classical
  simp [selectedParts]

private theorem mem_selectedSupport {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop)
    [DecidablePred pred] (x : α) :
    x ∈ selectedSupport P pred ↔
      ∃ B ∈ P.parts, pred B ∧ x ∈ B := by
  classical
  simp only [selectedSupport, Finset.mem_sup, mem_selectedParts]
  aesop

theorem pairing_existsUnique_mate {α : Type*} [DecidableEq α]
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

def pairingMate {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : α :=
  Finset.choose (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)

theorem pairingMate_mem {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : pairingMate P x hx ∈ P.1.part x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)).1

theorem pairingMate_ne {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : pairingMate P x hx ≠ x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)).2

theorem pairingMate_mem_support {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    pairingMate P x hx ∈ S :=
  P.1.part_subset x (pairingMate_mem P x hx)

theorem pairing_part_eq_pair {α : Type*} [DecidableEq α]
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

theorem pairingMate_involutive {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    pairingMate P (pairingMate P x hx)
      (pairingMate_mem_support P x hx) = x := by
  let y := pairingMate P x hx
  have hyS : y ∈ S := pairingMate_mem_support P x hx
  have hyPart : y ∈ P.1.part x := pairingMate_mem P x hx
  have hparts : P.1.part y = P.1.part x :=
    P.1.part_eq_of_mem (P.1.part_mem.2 hx) hyPart
  apply (pairing_existsUnique_mate P y hyS).unique
  · exact ⟨pairingMate_mem P y hyS, pairingMate_ne P y hyS⟩
  · refine ⟨?_, (pairingMate_ne P x hx).symm⟩
    rw [hparts]
    exact P.1.mem_part hx

private theorem selectedSupport_ne_part_eq_erase_pair
    {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) :
    selectedSupport P.1 (fun B ↦ B ≠ P.1.part x) =
      (S.erase x).erase (pairingMate P x hx) := by
  classical
  ext z
  rw [mem_selectedSupport]
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨B, hB, hBne, hzB⟩
    have hzS : z ∈ S := P.1.le hB hzB
    refine ⟨?_, ?_, hzS⟩
    · intro hzy
      subst z
      have hmatePart : pairingMate P x hx ∈ P.1.part x :=
        pairingMate_mem P x hx
      have hparts : B = P.1.part x :=
        P.1.eq_of_mem_parts hB (P.1.part_mem.2 hx) hzB hmatePart
      exact hBne hparts
    · intro hzx
      subst z
      exact hBne (P.1.part_eq_of_mem hB hzB).symm
  · rintro ⟨hzy, hzx, hzS⟩
    let B := P.1.part z
    have hB : B ∈ P.1.parts := P.1.part_mem.2 hzS
    refine ⟨B, hB, ?_, P.1.mem_part hzS⟩
    intro hBeq
    have hzpair : z ∈ ({x, pairingMate P x hx} : Finset α) := by
      rw [← pairing_part_eq_pair P x hx, ← hBeq]
      exact P.1.mem_part hzS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzpair
    exact hzpair.elim hzx hzy

private theorem pairing_restrict_erase_pair_parts
    {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S)
    (hT : (S.erase x).erase (pairingMate P x hx) ⊆ S) :
    (P.1.restrict hT).parts = P.1.parts.erase (P.1.part x) := by
  classical
  let y := pairingMate P x hx
  let T := (S.erase x).erase y
  have hpart : P.1.part x ∈ P.1.parts := P.1.part_mem.2 hx
  have hpartPair : P.1.part x = {x, y} := pairing_part_eq_pair P x hx
  have hpartT : P.1.part x ∩ T = ∅ := by
    rw [hpartPair]
    ext z
    simp [T, y]
  have hotherSubset : ∀ C ∈ P.1.parts, C ≠ P.1.part x → C ⊆ T := by
    intro C hC hCne z hzC
    have hzS : z ∈ S := P.1.le hC hzC
    have hdis : Disjoint C (P.1.part x) := P.1.disjoint hC hpart hCne
    have hzx : z ≠ x := by
      intro hzx
      subst z
      exact (Finset.disjoint_left.mp hdis) hzC (P.1.mem_part hx)
    have hzy : z ≠ y := by
      intro hzy
      subst z
      exact (Finset.disjoint_left.mp hdis) hzC (pairingMate_mem P x hx)
    exact Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hzS⟩⟩
  change (P.1.restrict hT).parts = P.1.parts.erase (P.1.part x)
  ext B
  simp only [Finpartition.restrict, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hBne, C, hC, hCB⟩
    have hCne : C ≠ P.1.part x := by
      intro hCeq
      subst C
      have : B = ∅ := by simpa [T] using hCB.symm.trans hpartT
      exact hBne this
    have hCT : C ∩ T = C := Finset.inter_eq_left.mpr (hotherSubset C hC hCne)
    have hCT' : C ∩ (S.erase x).erase (pairingMate P x hx) = C := by
      simpa [T, y] using hCT
    have hBC : B = C := hCB.symm.trans hCT'
    constructor
    · rw [hBC]
      exact hCne
    · rw [hBC]
      exact hC
  · rintro ⟨hBnePart, hB⟩
    have hBT : B ∩ T = B := Finset.inter_eq_left.mpr
      (hotherSubset B hB hBnePart)
    refine ⟨P.1.ne_empty hB, B, hB, ?_⟩
    simpa [T, y] using hBT

private noncomputable def pairingRemove {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    Pairing ((S.erase x).erase (pairingMate P x hx)) := by
  classical
  let T := (S.erase x).erase (pairingMate P x hx)
  have hT : T ⊆ S := by
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  refine ⟨P.1.restrict hT, ?_⟩
  intro B hB
  rw [pairing_restrict_erase_pair_parts P x hx hT] at hB
  exact P.2 B (Finset.mem_of_mem_erase hB)

private theorem pairingRemove_parts {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    (pairingRemove P x hx).1.parts =
      P.1.parts.erase (P.1.part x) := by
  classical
  unfold pairingRemove
  dsimp only
  apply pairing_restrict_erase_pair_parts

private noncomputable def pairingSplit {α : Type*} [LinearOrder α]
    {S : Finset α} (hS : S.Nonempty) (P : Pairing S) :
    (y : {y // y ∈ S.erase (S.min' hS)}) ×
      Pairing ((S.erase (S.min' hS)).erase y.1) := by
  let x := S.min' hS
  have hx : x ∈ S := Finset.min'_mem S hS
  let y := pairingMate P x hx
  have hyS : y ∈ S := pairingMate_mem_support P x hx
  have hyx : y ≠ x := pairingMate_ne P x hx
  exact ⟨⟨y, Finset.mem_erase.mpr ⟨hyx, hyS⟩⟩, pairingRemove P x hx⟩

private theorem pairingSplit_injective {α : Type*} [LinearOrder α]
    {S : Finset α} (hS : S.Nonempty) : Function.Injective (pairingSplit hS) := by
  classical
  intro P R hsplit
  let x := S.min' hS
  have hx : x ∈ S := Finset.min'_mem S hS
  have hmate : pairingMate P x hx = pairingMate R x hx :=
    by
      have hfirst := congrArg (fun z ↦ z.1.1) hsplit
      simpa only [pairingSplit] using hfirst
  have hremove : (pairingRemove P x hx).1.parts =
      (pairingRemove R x hx).1.parts := by
    have hsecond := congrArg (fun z ↦ z.2.1.parts) hsplit
    simpa only [pairingSplit] using hsecond
  apply Subtype.ext
  apply Finpartition.ext
  ext B
  rw [pairingRemove_parts P x hx, pairingRemove_parts R x hx] at hremove
  have hpartEq : P.1.part x = R.1.part x := by
    rw [pairing_part_eq_pair P x hx, pairing_part_eq_pair R x hx, hmate]
  by_cases hB : B = R.1.part x
  · subst B
    have hmemP : R.1.part x ∈ P.1.parts := by
      rw [← hpartEq]
      exact P.1.part_mem.2 hx
    exact iff_of_true hmemP (R.1.part_mem.2 hx)
  have hmemErase : B ∈ P.1.parts.erase (P.1.part x) ↔
      B ∈ R.1.parts.erase (R.1.part x) := by rw [hremove]
  have hBP : B ≠ P.1.part x := by rwa [hpartEq]
  simpa [hBP, hB] using hmemErase

private theorem pairing_subsingleton_of_card_eq_two
    {α : Type*} [DecidableEq α] {S : Finset α} (hcard : S.card = 2) :
    ∀ P R : Pairing S, P = R := by
  classical
  intro P R
  apply Subtype.ext
  apply Finpartition.ext
  ext B
  have hpart_eq_support : ∀ T : Pairing S, ∀ C ∈ T.1.parts, C = S := by
    intro T C hC
    apply Finset.eq_of_subset_of_card_le (T.1.le hC)
    rw [T.2 C hC, hcard]
  constructor
  · intro hB
    have hBS := hpart_eq_support P B hB
    rw [hBS]
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hSne
    have hRx : R.1.part x = S :=
      hpart_eq_support R (R.1.part x) (R.1.part_mem.2 hx)
    simpa only [hRx] using R.1.part_mem.2 hx
  · intro hB
    have hBS := hpart_eq_support R B hB
    rw [hBS]
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hSne
    have hPx : P.1.part x = S :=
      hpart_eq_support P (P.1.part x) (P.1.part_mem.2 hx)
    simpa only [hPx] using P.1.part_mem.2 hx

/-- A sharp ambient-cardinality bound for pairings of any finite ordered
support.  The first four points cost the factor `3`; each later pair costs at
most one ambient symbol. -/
theorem pairing_card_sharp_bound {α : Type*} [Fintype α] [LinearOrder α]
    (M : ℕ) (S : Finset α) (hcap : S.card ≤ M)
    (hpos : 0 < S.card) (heven : Even S.card) :
    Fintype.card (Pairing S) ≤ 3 * M ^ ((S.card - 4) / 2) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
      have hSne : S.Nonempty := Finset.card_pos.mp (hcard ▸ hpos)
      have hnEven : Even n := hcard ▸ heven
      have hncap : n ≤ M := hcard ▸ hcap
      have hn2 : 2 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      by_cases hnEq2 : n = 2
      · have hS2 : S.card = 2 := hcard.trans hnEq2
        have hsub : Fintype.card (Pairing S) ≤ 1 :=
          Fintype.card_le_one_iff.mpr
            (pairing_subsingleton_of_card_eq_two hS2)
        simpa [hnEq2] using hsub.trans (by omega : 1 ≤ 3)
      have hn4 : 4 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      have hsplit : Fintype.card (Pairing S) ≤
          Fintype.card ((y : {y // y ∈ S.erase (S.min' hSne)}) ×
            Pairing ((S.erase (S.min' hSne)).erase y.1)) :=
        Fintype.card_le_of_injective (pairingSplit hSne)
          (pairingSplit_injective hSne)
      by_cases hnEq4 : n = 4
      · have hS4 : S.card = 4 := hcard.trans hnEq4
        calc
          Fintype.card (Pairing S) ≤
              Fintype.card ((y : {y // y ∈ S.erase (S.min' hSne)}) ×
                Pairing ((S.erase (S.min' hSne)).erase y.1)) := hsplit
          _ = ∑ y : {y // y ∈ S.erase (S.min' hSne)},
                Fintype.card
                  (Pairing ((S.erase (S.min' hSne)).erase y.1)) :=
            Fintype.card_sigma
          _ ≤ ∑ _y : {y // y ∈ S.erase (S.min' hSne)}, 1 := by
            apply Finset.sum_le_sum
            intro y _
            apply Fintype.card_le_one_iff.mpr
            apply pairing_subsingleton_of_card_eq_two
            rw [Finset.card_erase_of_mem y.2,
              Finset.card_erase_of_mem (Finset.min'_mem S hSne), hS4]
          _ = 3 := by
            simp [Finset.card_erase_of_mem
              (Finset.min'_mem S hSne), hS4]
          _ = 3 * M ^ ((n - 4) / 2) := by
            rw [hnEq4]
            norm_num
      have hn6 : 6 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      let x := S.min' hSne
      have hx : x ∈ S := Finset.min'_mem S hSne
      have hsum :
          (∑ y : {y // y ∈ S.erase x},
              Fintype.card (Pairing ((S.erase x).erase y.1))) ≤
            ∑ _y : {y // y ∈ S.erase x},
              3 * M ^ ((n - 6) / 2) := by
        apply Finset.sum_le_sum
        intro y _
        let T := (S.erase x).erase y.1
        have hTcard : T.card = n - 2 := by
          dsimp only [T]
          rw [Finset.card_erase_of_mem y.2,
            Finset.card_erase_of_mem hx, hcard]
          omega
        have hTcap : T.card ≤ M := by omega
        have hTpos : 0 < T.card := by omega
        have hTEven : Even T.card := by
          obtain ⟨k, hk⟩ := hnEven
          refine ⟨k - 1, ?_⟩
          omega
        have hih := ih T.card (by omega) T hTcap hTpos hTEven rfl
        have hexp : (T.card - 4) / 2 = (n - 6) / 2 := by
          rw [hTcard]
          omega
        simpa [hexp] using hih
      calc
        Fintype.card (Pairing S) ≤
            Fintype.card ((y : {y // y ∈ S.erase x}) ×
              Pairing ((S.erase x).erase y.1)) := by simpa [x] using hsplit
        _ = ∑ y : {y // y ∈ S.erase x},
              Fintype.card (Pairing ((S.erase x).erase y.1)) :=
          Fintype.card_sigma
        _ ≤ ∑ _y : {y // y ∈ S.erase x},
              3 * M ^ ((n - 6) / 2) := hsum
        _ = (n - 1) * (3 * M ^ ((n - 6) / 2)) := by
          simp [Finset.card_erase_of_mem hx, hcard, Nat.mul_comm]
        _ ≤ M * (3 * M ^ ((n - 6) / 2)) := by
          gcongr
          omega
        _ = 3 * M ^ (((n - 6) / 2) + 1) := by
          rw [pow_succ]
          ac_rfl
        _ = 3 * M ^ ((n - 4) / 2) := by
          congr 2
          omega

/-- The sharp pairing bound specialized to the full finite type.  This wrapper
keeps dependent applications from unfolding the subtype-valued support. -/
theorem pairing_univ_card_sharp_bound {α : Type*} [Fintype α] [LinearOrder α]
    (M : ℕ) (hcap : Fintype.card α ≤ M) (hpos : 0 < Fintype.card α)
    (heven : Even (Fintype.card α)) :
    Fintype.card (Pairing (Finset.univ : Finset α)) ≤
      3 * M ^ ((Fintype.card α - 4) / 2) := by
  simpa using pairing_card_sharp_bound M (Finset.univ : Finset α)
    (by simpa using hcap) (by simpa using hpos) (by simpa using heven)

theorem pairing_card_parallel_bound (p : ℕ) :
    ∀ S : Finset (Fin (2 * p)), 0 < S.card → Even S.card →
      Fintype.card (Pairing S) ≤
        3 * (4 * p) ^ ((S.card - 4) / 2) := by
  classical
  intro S hpos heven
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
      have hSne : S.Nonempty := Finset.card_pos.mp (hcard ▸ hpos)
      have hnEven : Even n := hcard ▸ heven
      have hnle : n ≤ 2 * p := by
        rw [← hcard]
        simpa using Finset.card_le_univ S
      have hn2 : 2 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      by_cases hnEq2 : n = 2
      · have hS2 : S.card = 2 := hcard.trans hnEq2
        have hsub : Fintype.card (Pairing S) ≤ 1 :=
          Fintype.card_le_one_iff.mpr
            (pairing_subsingleton_of_card_eq_two hS2)
        simpa [hnEq2] using hsub.trans (by omega : 1 ≤ 3)
      have hn4 : 4 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      have hsplit : Fintype.card (Pairing S) ≤
          Fintype.card ((y : {y // y ∈ S.erase (S.min' hSne)}) ×
            Pairing ((S.erase (S.min' hSne)).erase y.1)) :=
        Fintype.card_le_of_injective (pairingSplit hSne)
          (pairingSplit_injective hSne)
      by_cases hnEq4 : n = 4
      · have hS4 : S.card = 4 := hcard.trans hnEq4
        calc
          Fintype.card (Pairing S) ≤
              Fintype.card ((y : {y // y ∈ S.erase (S.min' hSne)}) ×
                Pairing ((S.erase (S.min' hSne)).erase y.1)) := hsplit
          _ = ∑ y : {y // y ∈ S.erase (S.min' hSne)},
                Fintype.card
                  (Pairing ((S.erase (S.min' hSne)).erase y.1)) :=
            Fintype.card_sigma
          _ ≤ ∑ _y : {y // y ∈ S.erase (S.min' hSne)}, 1 := by
            apply Finset.sum_le_sum
            intro y _
            apply Fintype.card_le_one_iff.mpr
            apply pairing_subsingleton_of_card_eq_two
            rw [Finset.card_erase_of_mem y.2,
              Finset.card_erase_of_mem (Finset.min'_mem S hSne), hS4]
          _ = 3 := by
            simp [Finset.card_erase_of_mem
              (Finset.min'_mem S hSne), hS4]
          _ = 3 * (4 * p) ^ ((n - 4) / 2) := by
            rw [hnEq4]
            norm_num
      have hn6 : 6 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      let x := S.min' hSne
      have hx : x ∈ S := Finset.min'_mem S hSne
      have hsum :
          (∑ y : {y // y ∈ S.erase x},
              Fintype.card (Pairing ((S.erase x).erase y.1))) ≤
            ∑ _y : {y // y ∈ S.erase x},
              3 * (4 * p) ^ ((n - 6) / 2) := by
        apply Finset.sum_le_sum
        intro y _
        let T := (S.erase x).erase y.1
        have hTcard : T.card = n - 2 := by
          dsimp only [T]
          rw [Finset.card_erase_of_mem y.2,
            Finset.card_erase_of_mem hx, hcard]
          omega
        have hTpos : 0 < T.card := by omega
        have hTEven : Even T.card := by
          obtain ⟨k, hk⟩ := hnEven
          refine ⟨k - 1, ?_⟩
          omega
        have hih := ih T.card (by omega) T hTpos hTEven rfl
        have hexp : (T.card - 4) / 2 = (n - 6) / 2 := by
          rw [hTcard]
          omega
        simpa [hexp] using hih
      calc
        Fintype.card (Pairing S) ≤
            Fintype.card ((y : {y // y ∈ S.erase x}) ×
              Pairing ((S.erase x).erase y.1)) := by simpa [x] using hsplit
        _ = ∑ y : {y // y ∈ S.erase x},
              Fintype.card (Pairing ((S.erase x).erase y.1)) :=
          Fintype.card_sigma
        _ ≤ ∑ _y : {y // y ∈ S.erase x},
              3 * (4 * p) ^ ((n - 6) / 2) := hsum
        _ = (n - 1) * (3 * (4 * p) ^ ((n - 6) / 2)) := by
          simp [Finset.card_erase_of_mem hx, hcard,
            Nat.mul_comm]
        _ ≤ (4 * p) * (3 * (4 * p) ^ ((n - 6) / 2)) := by
          gcongr
          omega
        _ = 3 * (4 * p) ^ (((n - 6) / 2) + 1) := by
          rw [pow_succ]
          ac_rfl
        _ = 3 * (4 * p) ^ ((n - 4) / 2) := by
          congr 2
          omega

private theorem pairing_card_ambient_power_bound (p : ℕ) :
    ∀ S : Finset (Fin (2 * p)), Even S.card →
      Fintype.card (Pairing S) ≤ (2 * p) ^ (S.card / 2) := by
  classical
  intro S heven
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
      have hnEven : Even n := hcard ▸ heven
      by_cases hn0 : n = 0
      · have hSempty : S = ∅ := Finset.card_eq_zero.mp (hcard.trans hn0)
        subst S
        have hsub : Fintype.card
            (Pairing (∅ : Finset (Fin (2 * p)))) ≤ 1 :=
          Fintype.card_le_one_iff.mpr fun P R ↦ by
            apply Subtype.ext
            apply Finpartition.ext
            have hparts : ∀ T : Finpartition
                (∅ : Finset (Fin (2 * p))), T.parts = ∅ := by
              intro T
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro B hB
              have hBempty : B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
                fun z hz ↦ by simpa using T.le hB hz
              exact T.ne_empty hB hBempty
            rw [hparts P.1, hparts R.1]
        simpa [hn0] using hsub
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      let x := S.min' hSne
      have hx : x ∈ S := Finset.min'_mem S hSne
      have hn2 : 2 ≤ n := by
        obtain ⟨k, hk⟩ := hnEven
        omega
      have hsum :
          (∑ y : {y // y ∈ S.erase x},
              Fintype.card (Pairing ((S.erase x).erase y.1))) ≤
            ∑ _y : {y // y ∈ S.erase x},
              (2 * p) ^ ((n - 2) / 2) := by
        apply Finset.sum_le_sum
        intro y _
        let T := (S.erase x).erase y.1
        have hTcard : T.card = n - 2 := by
          dsimp only [T]
          rw [Finset.card_erase_of_mem y.2,
            Finset.card_erase_of_mem hx, hcard]
          omega
        have hTEven : Even T.card := by
          obtain ⟨k, hk⟩ := hnEven
          refine ⟨k - 1, ?_⟩
          omega
        have hih := ih T.card (by omega) T hTEven rfl
        have hexp : T.card / 2 = (n - 2) / 2 := by rw [hTcard]
        simpa [hexp] using hih
      have hsplit : Fintype.card (Pairing S) ≤
          Fintype.card ((y : {y // y ∈ S.erase x}) ×
            Pairing ((S.erase x).erase y.1)) := by
        exact Fintype.card_le_of_injective (pairingSplit hSne)
          (pairingSplit_injective hSne)
      have hnle : n ≤ 2 * p := by
        rw [← hcard]
        simpa using Finset.card_le_univ S
      calc
        Fintype.card (Pairing S) ≤
            Fintype.card ((y : {y // y ∈ S.erase x}) ×
              Pairing ((S.erase x).erase y.1)) := hsplit
        _ = ∑ y : {y // y ∈ S.erase x},
              Fintype.card (Pairing ((S.erase x).erase y.1)) :=
          Fintype.card_sigma
        _ ≤ ∑ _y : {y // y ∈ S.erase x},
              (2 * p) ^ ((n - 2) / 2) := hsum
        _ = (n - 1) * (2 * p) ^ ((n - 2) / 2) := by
          simp [Finset.card_erase_of_mem hx, hcard, Nat.mul_comm]
        _ ≤ (2 * p) * (2 * p) ^ ((n - 2) / 2) := by
          gcongr
          omega
        _ = (2 * p) ^ (((n - 2) / 2) + 1) := by
          rw [pow_succ]
          ac_rfl
        _ = (2 * p) ^ (n / 2) := by
          congr 1
          obtain ⟨k, hk⟩ := hnEven
          omega

private def IsLargeEntryPart {p : ℕ} (B : Finset (Fin (2 * p))) : Prop :=
  3 ≤ B.card

private def IsLoopEntryPart {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (B : Finset (Fin (2 * p))) : Prop :=
  B.card = 2 ∧ ∀ e ∈ B,
    equalityVertexAt Q.1 e = equalityVertexAt Q.1 (cyclicSucc e)

private def IsDisjointEntryPart {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t)
    (B : Finset (Fin (2 * p))) : Prop :=
  B.card = 2 ∧ ∃ hB : B ∈ D.entry.parts,
    (⟨B, hB⟩ : EntryBlock D) ∈ disjointPairRows D

private def IsParallelEntryPart {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t)
    (B : Finset (Fin (2 * p))) : Prop :=
  B.card = 2 ∧ ¬ IsLoopEntryPart D.selector B ∧
    ¬ IsDisjointEntryPart D B

private theorem aggregate_entry_excess_sum
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t} (hd : d ≤ p)
    (A : AggregateEntryPartition (p := p) (s := s) (t := t) Q d h) :
    ∑ B ∈ A.1.parts, (B.card - 2) = 2 * d := by
  rw [Finset.sum_tsub_distrib A.1.parts A.2.1]
  rw [A.1.sum_card_parts]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const_nat]
  rw [A.2.2.2.1]
  omega

private theorem selected_large_excess_sum
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t} (hd : d ≤ p)
    (A : AggregateEntryPartition (p := p) (s := s) (t := t) Q d h) :
    ∑ B ∈ (selectedPartition A.1 IsLargeEntryPart).parts,
        (B.card - 2) = 2 * d := by
  classical
  rw [selectedPartition_parts]
  unfold selectedParts
  have hzero : ∑ B ∈ A.1.parts.filter (fun B ↦ ¬ IsLargeEntryPart B),
      (B.card - 2) = 0 := by
    apply Finset.sum_eq_zero
    intro B hB
    have hBpart := (Finset.mem_filter.mp hB).1
    have hBnot := (Finset.mem_filter.mp hB).2
    have hBle2 : B.card ≤ 2 := by
      unfold IsLargeEntryPart at hBnot
      omega
    have hBge2 := A.2.1 B hBpart
    omega
  calc
    (∑ B ∈ A.1.parts.filter IsLargeEntryPart, (B.card - 2)) =
        (∑ B ∈ A.1.parts.filter IsLargeEntryPart, (B.card - 2)) +
          ∑ B ∈ A.1.parts.filter (fun B ↦ ¬ IsLargeEntryPart B),
            (B.card - 2) := by rw [hzero, add_zero]
    _ = ∑ B ∈ A.1.parts, (B.card - 2) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = 2 * d := aggregate_entry_excess_sum hd A

private noncomputable def aggregateLargePattern
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t} (hd : d ≤ p)
    (A : AggregateEntryPartition (p := p) (s := s) (t := t) Q d h) :
    LargeBlockPattern p d := by
  classical
  refine ⟨⟨selectedSupport A.1 IsLargeEntryPart,
    selectedPartition A.1 IsLargeEntryPart⟩, ?_, ?_⟩
  · intro B hB
    rw [selectedPartition_parts] at hB
    exact (mem_selectedParts A.1 IsLargeEntryPart B).mp hB |>.2
  · exact selected_large_excess_sum hd A

private theorem aggregateLargePattern_support
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t} (hd : d ≤ p)
    (A : AggregateEntryPartition (p := p) (s := s) (t := t) Q d h) :
    (aggregateLargePattern hd A).1.1 =
      largeBlockOccurrences (entryPartitionData Q A.1) := by
  classical
  ext e
  change e ∈ selectedSupport A.1 IsLargeEntryPart ↔
    e ∈ largeBlockOccurrences (entryPartitionData Q A.1)
  rw [mem_selectedSupport]
  simp only [largeBlockOccurrences, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨B, hB, hlarge, heB⟩
    have hpart : A.1.part e = B := A.1.part_eq_of_mem hB heB
    change 3 ≤ (A.1.part e).card
    rw [hpart]
    exact hlarge
  · intro hlarge
    refine ⟨A.1.part e, A.1.part_mem.2 (Finset.mem_univ e), ?_,
      A.1.mem_part (Finset.mem_univ e)⟩
    change 3 ≤ (A.1.part e).card at hlarge
    exact hlarge

private noncomputable def rowSupport {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) (B : EntryBlock D) :
    Finset (EqualityVertex D.selector.1) :=
  Finset.univ.filter fun u ↦ entryConstraintMatrix D B u ≠ 0

private def blockEndpointSupport {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (B : Finset (Fin (2 * p))) :
    Finset (EqualityVertex Q.1) :=
  B.biUnion fun e ↦
    {equalityVertexAt Q.1 e, equalityVertexAt Q.1 (cyclicSucc e)}

private theorem rowSupport_subset_blockEndpointSupport
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) (B : EntryBlock D) :
    rowSupport D B ⊆ blockEndpointSupport D.selector B.1 := by
  classical
  intro u hu
  have hne : entryConstraintMatrix D B u ≠ 0 :=
    (Finset.mem_filter.mp hu).2
  by_contra hnot
  have hzero : entryConstraintMatrix D B u = 0 := by
    unfold entryConstraintMatrix
    apply Finset.sum_eq_zero
    intro e he
    have huNot : u ∉ B.1.biUnion (fun z ↦
        {equalityVertexAt D.selector.1 z,
          equalityVertexAt D.selector.1 (cyclicSucc z)}) := hnot
    have hsrc : equalityVertexAt D.selector.1 e ≠ u := by
      intro h
      apply huNot
      apply Finset.mem_biUnion.mpr
      exact ⟨e, he, by simp [h]⟩
    have hdst : equalityVertexAt D.selector.1 (cyclicSucc e) ≠ u := by
      intro h
      apply huNot
      apply Finset.mem_biUnion.mpr
      exact ⟨e, he, by simp [h]⟩
    simp [hsrc, hdst]
  exact hne hzero

private theorem blockEndpointSupport_card_le
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (B : Finset (Fin (2 * p))) :
    (blockEndpointSupport Q B).card ≤ 2 * B.card := by
  classical
  calc
    (blockEndpointSupport Q B).card ≤
        ∑ e ∈ B, ({equalityVertexAt Q.1 e,
          equalityVertexAt Q.1 (cyclicSucc e)} :
            Finset (EqualityVertex Q.1)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ B, 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact Finset.card_le_two
    _ = 2 * B.card := by simp [Nat.mul_comm]

private theorem rowSupport_eq_blockEndpointSupport_of_disjoint_part
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (B : Finset (Fin (2 * p))) (hB : IsDisjointEntryPart D B) :
    rowSupport D ⟨B, hB.2.choose⟩ = blockEndpointSupport D.selector B := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · exact rowSupport_subset_blockEndpointSupport D ⟨B, hB.2.choose⟩
  · have hrow := (Finset.mem_filter.mp hB.2.choose_spec).2
    change (rowSupport D ⟨B, hB.2.choose⟩).card = 4 at hrow
    calc
      (blockEndpointSupport D.selector B).card ≤ 2 * B.card :=
        blockEndpointSupport_card_le D.selector B
      _ = 4 := by rw [hB.1]
      _ = (rowSupport D ⟨B, hB.2.choose⟩).card := hrow.symm

private lemma exists_other_of_mem_card_two {α : Type*} [DecidableEq α]
    {B : Finset α} {e : α} (he : e ∈ B) (hBcard : B.card = 2) :
    ∃ f ∈ B, e ≠ f ∧ B = {e, f} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hBcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨y, by simp, hxy, rfl⟩
  · exact ⟨x, by simp, hxy.symm, by ext z; simp [or_comm]⟩

private theorem genuine_disjoint_row_support_eq
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (B : EntryBlock D) (e f : Fin (2 * p))
    (hB : B.1 = {e, f}) (hef : e ≠ f)
    (he : equalityVertexAt D.selector.1 e ≠
      equalityVertexAt D.selector.1 (cyclicSucc e))
    (hf : equalityVertexAt D.selector.1 f ≠
      equalityVertexAt D.selector.1 (cyclicSucc f))
    (hdisjoint : Disjoint
      ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} :
        Finset (EqualityVertex D.selector.1))
      ({equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} :
        Finset (EqualityVertex D.selector.1))) :
    rowSupport D B =
      {equalityVertexAt D.selector.1 e,
        equalityVertexAt D.selector.1 (cyclicSucc e),
        equalityVertexAt D.selector.1 f,
        equalityVertexAt D.selector.1 (cyclicSucc f)} := by
  classical
  let a := equalityVertexAt D.selector.1 e
  let b := equalityVertexAt D.selector.1 (cyclicSucc e)
  let c := equalityVertexAt D.selector.1 f
  let d := equalityVertexAt D.selector.1 (cyclicSucc f)
  have hab : a ≠ b := he
  have hcd : c ≠ d := hf
  have hac : a ≠ c := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint)
      (show equalityVertexAt D.selector.1 e ∈
        ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} : Finset _) by simp)
      (show equalityVertexAt D.selector.1 e ∈
        ({equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} : Finset _) by
            exact Finset.mem_insert.mpr (Or.inl h))
  have had : a ≠ d := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint)
      (show equalityVertexAt D.selector.1 e ∈
        ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} : Finset _) by simp)
      (show equalityVertexAt D.selector.1 e ∈
        ({equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} : Finset _) by
            exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton.mpr h)))
  have hbc : b ≠ c := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint)
      (show equalityVertexAt D.selector.1 (cyclicSucc e) ∈
        ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} : Finset _) by simp)
      (show equalityVertexAt D.selector.1 (cyclicSucc e) ∈
        ({equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} : Finset _) by
            exact Finset.mem_insert.mpr (Or.inl h))
  have hbd : b ≠ d := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint)
      (show equalityVertexAt D.selector.1 (cyclicSucc e) ∈
        ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} : Finset _) by simp)
      (show equalityVertexAt D.selector.1 (cyclicSucc e) ∈
        ({equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} : Finset _) by
            exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton.mpr h)))
  ext u
  simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  change entryConstraintMatrix D B u ≠ 0 ↔
    u = a ∨ u = b ∨ u = c ∨ u = d
  by_cases hua : u = a
  · subst u
    simp [entryConstraintMatrix, hB, hef, a, b, c, d, hab, hab.symm,
      hac, hac.symm, had, had.symm]
  by_cases hub : u = b
  · subst u
    simp [entryConstraintMatrix, hB, hef, a, b, c, d, hab, hab.symm,
      hbc, hbc.symm, hbd, hbd.symm]
  by_cases huc : u = c
  · subst u
    simp [entryConstraintMatrix, hB, hef, a, b, c, d, hac, hac.symm,
      hbc, hbc.symm, hcd, hcd.symm]
  by_cases hud : u = d
  · subst u
    simp [entryConstraintMatrix, hB, hef, a, b, c, d, had, had.symm,
      hbd, hbd.symm, hcd, hcd.symm]
  · simp [entryConstraintMatrix, hB, hef, a, b, c, d,
      hua, hub, huc, hud, Ne.symm hua, Ne.symm hub, Ne.symm huc,
      Ne.symm hud]

private theorem genuine_disjoint_is_disjoint_entry_part
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (B : Finset (Fin (2 * p))) (hBpart : B ∈ D.entry.parts)
    (hBcard : B.card = 2) (e f : Fin (2 * p))
    (hB : B = {e, f}) (hef : e ≠ f)
    (he : equalityVertexAt D.selector.1 e ≠
      equalityVertexAt D.selector.1 (cyclicSucc e))
    (hf : equalityVertexAt D.selector.1 f ≠
      equalityVertexAt D.selector.1 (cyclicSucc f))
    (hdisjoint : Disjoint
      ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} :
        Finset (EqualityVertex D.selector.1))
      ({equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} :
        Finset (EqualityVertex D.selector.1))) :
    IsDisjointEntryPart D B := by
  classical
  refine ⟨hBcard, hBpart, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (rowSupport D ⟨B, hBpart⟩).card = 4
  rw [genuine_disjoint_row_support_eq D ⟨B, hBpart⟩ e f hB hef he hf hdisjoint]
  have hpairs :
      ({equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e),
          equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} :
        Finset (EqualityVertex D.selector.1)) =
      {equalityVertexAt D.selector.1 e,
          equalityVertexAt D.selector.1 (cyclicSucc e)} ∪
        {equalityVertexAt D.selector.1 f,
          equalityVertexAt D.selector.1 (cyclicSucc f)} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  rw [hpairs, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_pair he, Finset.card_pair hf]

private theorem disjoint_part_endpoints_mem_constraintSupport
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (B : Finset (Fin (2 * p))) (hB : IsDisjointEntryPart D B)
    (e : Fin (2 * p)) (heB : e ∈ B) :
    equalityVertexAt D.selector.1 e ∈ disjointConstraintSupport D ∧
      equalityVertexAt D.selector.1 (cyclicSucc e) ∈
        disjointConstraintSupport D := by
  classical
  let EB : EntryBlock D := ⟨B, hB.2.choose⟩
  have hrowmem : EB ∈ disjointPairRows D := by
    simpa [EB] using hB.2.choose_spec
  have hroweq : rowSupport D EB = blockEndpointSupport D.selector B := by
    simpa [EB] using rowSupport_eq_blockEndpointSupport_of_disjoint_part D B hB
  have endpoint_to_constraint : ∀ u ∈ blockEndpointSupport D.selector B,
      u ∈ disjointConstraintSupport D := by
    intro u hu
    have hurow : u ∈ rowSupport D EB := by rwa [hroweq]
    have huentry : entryConstraintMatrix D EB u ≠ 0 :=
      (Finset.mem_filter.mp hurow).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ u, EB, ?_⟩
    simp only [disjointConstraintMatrix, hrowmem, if_true]
    exact huentry
  constructor
  · apply endpoint_to_constraint
    apply Finset.mem_biUnion.mpr
    exact ⟨e, heB, by simp⟩
  · apply endpoint_to_constraint
    apply Finset.mem_biUnion.mpr
    exact ⟨e, heB, by simp⟩

private noncomputable def disjointEntryPairing
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    Pairing (selectedSupport D.entry (IsDisjointEntryPart D)) := by
  classical
  refine ⟨selectedPartition D.entry (IsDisjointEntryPart D), ?_⟩
  intro B hB
  rw [selectedPartition_parts] at hB
  exact (mem_selectedParts D.entry (IsDisjointEntryPart D) B).mp hB |>.2.1

private noncomputable def loopEntryPairing
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    Pairing (selectedSupport D.entry (IsLoopEntryPart D.selector)) := by
  classical
  refine ⟨selectedPartition D.entry (IsLoopEntryPart D.selector), ?_⟩
  intro B hB
  rw [selectedPartition_parts] at hB
  exact (mem_selectedParts D.entry (IsLoopEntryPart D.selector) B).mp hB |>.2.1

private noncomputable def parallelEntryPairing
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    Pairing (selectedSupport D.entry (IsParallelEntryPart D)) := by
  classical
  refine ⟨selectedPartition D.entry (IsParallelEntryPart D), ?_⟩
  intro B hB
  rw [selectedPartition_parts] at hB
  exact (mem_selectedParts D.entry (IsParallelEntryPart D) B).mp hB |>.2.1

private noncomputable def aggregateDisjointChoice
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1)
    (A : AggregateEntryPartition Q d h) : DisjointPairChoice Q h := by
  classical
  let D : EntryCumulantPartitionData p s t := entryPartitionData Q A.1
  have h24 := large_block_and_support_rank_bound hp hd D
    A.2.1 A.2.2.1 A.2.2.2.1 A.2.2.2.2
  let U : {U : Finset (EqualityVertex Q.1) // U.card ≤ 4 * h} :=
    ⟨disjointConstraintSupport D, h24.2.2.2.2.1⟩
  let S := selectedSupport D.entry (IsDisjointEntryPart D)
  have hS : S ⊆ occurrenceWithinVertices Q U.1 := by
    intro e he
    obtain ⟨B, hBpart, hBdisjoint, heB⟩ :=
      (mem_selectedSupport D.entry (IsDisjointEntryPart D) e).mp he
    have hend := disjoint_part_endpoints_mem_constraintSupport D B hBdisjoint e heB
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ e, hend⟩
  exact ⟨U, ⟨S, hS⟩, disjointEntryPairing D⟩

private def loopOccurrenceSupport {p s t : ℕ}
    (Q : SelectorEqualityData p s t) : Finset (Fin (2 * p)) :=
  Finset.univ.filter fun e ↦
    equalityVertexAt Q.1 e = equalityVertexAt Q.1 (cyclicSucc e)

private theorem loopOccurrenceSupport_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (loopOccurrenceSupport Q).card = equalityLoopOccurrences Q.1 := by
  simp [loopOccurrenceSupport, equalityLoopOccurrences, equalityVertexAt,
    Subtype.ext_iff]

private theorem selectedLoopSupport_eq
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hd : d ≤ p)
    (A : AggregateEntryPartition Q d h) :
    selectedSupport A.1 (IsLoopEntryPart Q) =
      loopOccurrenceSupport Q \ (aggregateLargePattern hd A).1.1 := by
  classical
  ext e
  rw [mem_selectedSupport]
  simp only [Finset.mem_sdiff, loopOccurrenceSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨B, hBpart, hBloop, heB⟩
    refine ⟨hBloop.2 e heB, ?_⟩
    intro helarge
    have hlargeDef : e ∈ largeBlockOccurrences (entryPartitionData Q A.1) := by
      rw [← aggregateLargePattern_support hd A]
      exact helarge
    have hpartLarge : 3 ≤ (A.1.part e).card := by
      have hraw := (Finset.mem_filter.mp hlargeDef).2
      change 3 ≤ (A.1.part e).card at hraw
      exact hraw
    have hpart : A.1.part e = B := A.1.part_eq_of_mem hBpart heB
    rw [hpart, hBloop.1] at hpartLarge
    omega
  · rintro ⟨heLoop, heNotLarge⟩
    have heUniv : e ∈ (Finset.univ : Finset (Fin (2 * p))) := Finset.mem_univ e
    let B := A.1.part e
    have hBpart : B ∈ A.1.parts := A.1.part_mem.2 heUniv
    have heB : e ∈ B := A.1.mem_part heUniv
    have hnotthree : ¬ 3 ≤ B.card := by
      intro hthree
      apply heNotLarge
      rw [aggregateLargePattern_support hd A]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hthree⟩
    have hBcard : B.card = 2 := by
      have hge := A.2.1 B hBpart
      omega
    obtain ⟨f, hfB, hef, hBpair⟩ :=
      exists_other_of_mem_card_two heB hBcard
    have htri := A.2.2.1 B hBpart hBcard e heB f hfB hef
    have hloops :
        equalityVertexAt Q.1 e = equalityVertexAt Q.1 (cyclicSucc e) ∧
          equalityVertexAt Q.1 f = equalityVertexAt Q.1 (cyclicSucc f) := by
      rcases htri with hloops | hparallel | hdisjoint
      · exact hloops
      · exact (hparallel.1 heLoop).elim
      · exact (hdisjoint.1 heLoop).elim
    refine ⟨B, hBpart, ⟨hBcard, ?_⟩, heB⟩
    intro z hz
    rw [hBpair] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hloops.1
    · exact hloops.2

private theorem pairing_support_even {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) : Even S.card := by
  refine ⟨P.1.parts.card, ?_⟩
  calc
    S.card = ∑ B ∈ P.1.parts, B.card := P.1.sum_card_parts.symm
    _ = ∑ _B ∈ P.1.parts, 2 := by
      apply Finset.sum_congr rfl
      intro B hB
      exact P.2 B hB
    _ = P.1.parts.card * 2 := by simp
    _ = P.1.parts.card + P.1.parts.card := by omega

private noncomputable def pairingRestrict {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (T : Finset α) (hT : T ⊆ S)
    (hclosed : ∀ x ∈ T, P.1.part x ⊆ T) : Pairing T := by
  classical
  refine ⟨P.1.restrict hT, ?_⟩
  intro B hB
  rw [Finpartition.restrict] at hB
  have hBne : B ≠ ∅ := (Finset.mem_erase.mp hB).1
  obtain ⟨C, hCpart, hCB⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hB)
  obtain ⟨x, hxB⟩ := Finset.nonempty_iff_ne_empty.mpr hBne
  have hxC : x ∈ C := by
    have hxInf : x ∈ C ⊓ T := hCB.symm ▸ hxB
    exact (Finset.mem_inter.mp hxInf).1
  have hxT : x ∈ T := by
    have hxInf : x ∈ C ⊓ T := hCB.symm ▸ hxB
    exact (Finset.mem_inter.mp hxInf).2
  have hpartC : P.1.part x = C := P.1.part_eq_of_mem hCpart hxC
  have hCsub : C ⊆ T := by simpa [hpartC] using hclosed x hxT
  have hCT : C ∩ T = C := Finset.inter_eq_left.mpr hCsub
  have hBC : B = C := hCB ▸ hCT
  rw [hBC]
  exact P.2 C hCpart

private theorem pairingRestrict_part
    {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (T : Finset α) (hT : T ⊆ S)
    (hclosed : ∀ x ∈ T, P.1.part x ⊆ T) (x : α) (hx : x ∈ T) :
    (pairingRestrict P T hT hclosed).1.part x = P.1.part x := by
  classical
  apply (pairingRestrict P T hT hclosed).1.part_eq_of_mem
  · change P.1.part x ∈
      (P.1.parts.image (fun C ↦ C ⊓ T)).erase ∅
    apply Finset.mem_erase.mpr
    refine ⟨P.1.ne_empty (P.1.part_mem.2 (hT hx)), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨P.1.part x, P.1.part_mem.2 (hT hx), ?_⟩
    exact Finset.inter_eq_left.mpr (hclosed x hx)
  · exact P.1.mem_part (hT hx)

private theorem selectedPartition_part
    {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Finpartition S) (pred : Finset α → Prop) (x : α)
    (hx : x ∈ selectedSupport P pred) :
    (selectedPartition P pred).part x = P.part x := by
  classical
  obtain ⟨B, hBpart, hBpred, hxB⟩ :=
    (mem_selectedSupport P pred x).mp hx
  have hpart : P.part x = B := P.part_eq_of_mem hBpart hxB
  apply (selectedPartition P pred).part_eq_of_mem
  · rw [selectedPartition_parts]
    apply (mem_selectedParts P pred (P.part x)).mpr
    exact ⟨P.part_mem.2 (P.le hBpart hxB), hpart.symm ▸ hBpred⟩
  · exact P.mem_part (P.le hBpart hxB)

private def entryEdgeKey {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (e : Fin (2 * p)) : Finset (EqualityVertex Q.1) :=
  {equalityVertexAt Q.1 e, equalityVertexAt Q.1 (cyclicSucc e)}

private theorem parallel_entry_part_description
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (hadmissible : AdmissibleEntryPairBlocks D)
    (B : Finset (Fin (2 * p))) (hBpart : B ∈ D.entry.parts)
    (hBparallel : IsParallelEntryPart D B)
    (e : Fin (2 * p)) (heB : e ∈ B) :
    ∃ f ∈ B, e ≠ f ∧ B = {e, f} ∧
      equalityVertexAt D.selector.1 e ≠
        equalityVertexAt D.selector.1 (cyclicSucc e) ∧
      equalityVertexAt D.selector.1 f ≠
        equalityVertexAt D.selector.1 (cyclicSucc f) ∧
      entryEdgeKey D.selector e = entryEdgeKey D.selector f := by
  classical
  obtain ⟨f, hfB, hef, hBpair⟩ :=
    exists_other_of_mem_card_two heB hBparallel.1
  have htri := hadmissible B hBpart hBparallel.1 e heB f hfB hef
  rcases htri with hloops | hparallel | hdisjoint
  · have hloopPart : IsLoopEntryPart D.selector B := by
      refine ⟨hBparallel.1, ?_⟩
      intro z hz
      rw [hBpair] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hloops.1
      · exact hloops.2
    exact (hBparallel.2.1 hloopPart).elim
  · refine ⟨f, hfB, hef, hBpair, hparallel.1, hparallel.2.1, ?_⟩
    rcases hparallel.2.2 with hsame | hswap
    · ext u
      simp only [entryEdgeKey, Finset.mem_insert, Finset.mem_singleton]
      constructor <;> intro hu
      · rcases hu with rfl | rfl
        · exact Or.inl hsame.1
        · exact Or.inr hsame.2
      · rcases hu with hu | hu
        · exact Or.inl (hu.trans hsame.1.symm)
        · exact Or.inr (hu.trans hsame.2.symm)
    · ext u
      simp only [entryEdgeKey, Finset.mem_insert, Finset.mem_singleton]
      constructor <;> intro hu
      · rcases hu with rfl | rfl
        · exact Or.inr hswap.1
        · exact Or.inl hswap.2
      · rcases hu with hu | hu
        · exact Or.inr (hu.trans hswap.2.symm)
        · exact Or.inl (hu.trans hswap.1.symm)
  · have hdisjointPart : IsDisjointEntryPart D B :=
      genuine_disjoint_is_disjoint_entry_part D B hBpart hBparallel.1
        e f hBpair hef hdisjoint.1 hdisjoint.2.1 hdisjoint.2.2
    exact (hBparallel.2.2 hdisjointPart).elim

private theorem parallel_entry_part_edgeKey_eq
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (hadmissible : AdmissibleEntryPairBlocks D)
    (B : Finset (Fin (2 * p))) (hBpart : B ∈ D.entry.parts)
    (hBparallel : IsParallelEntryPart D B)
    {e f : Fin (2 * p)} (heB : e ∈ B) (hfB : f ∈ B) :
    entryEdgeKey D.selector e = entryEdgeKey D.selector f := by
  obtain ⟨g, hgB, heg, hBpair, heNonloop, hgNonloop, hkey⟩ :=
    parallel_entry_part_description D hadmissible B hBpart hBparallel e heB
  rw [hBpair] at hfB
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfB
  rcases hfB with rfl | rfl
  · rfl
  · exact hkey

private theorem selectedParallelSupport_eq_complement
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hd : d ≤ p)
    (A : AggregateEntryPartition Q d h) :
    selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) =
      Finset.univ \ ((aggregateLargePattern hd A).1.1 ∪
        selectedSupport A.1
          (IsDisjointEntryPart (entryPartitionData Q A.1)) ∪
        selectedSupport A.1 (IsLoopEntryPart Q)) := by
  classical
  let D : EntryCumulantPartitionData p s t := entryPartitionData Q A.1
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hePar
    obtain ⟨B, hBpart, hBpar, heB⟩ :=
      (mem_selectedSupport A.1 (IsParallelEntryPart D) e).mp hePar
    intro hbad
    rcases hbad with (heLarge | heDis) | heLoop
    ·
      rw [aggregateLargePattern_support hd A] at heLarge
      have hthree := (Finset.mem_filter.mp heLarge).2
      change 3 ≤ (A.1.part e).card at hthree
      have hpart : A.1.part e = B := A.1.part_eq_of_mem hBpart heB
      rw [hpart, hBpar.1] at hthree
      omega
    ·
      obtain ⟨C, hCpart, hCdis, heC⟩ :=
        (mem_selectedSupport A.1 (IsDisjointEntryPart D) e).mp heDis
      have hBC : B = C := A.1.eq_of_mem_parts hBpart hCpart heB heC
      exact hBpar.2.2 (hBC ▸ hCdis)
    ·
      obtain ⟨C, hCpart, hCloop, heC⟩ :=
        (mem_selectedSupport A.1 (IsLoopEntryPart Q) e).mp heLoop
      have hBC : B = C := A.1.eq_of_mem_parts hBpart hCpart heB heC
      exact hBpar.2.1 (hBC ▸ hCloop)
  · intro hnotUnion
    have heNotLarge : e ∉ (aggregateLargePattern hd A).1.1 := by
      intro heLarge
      exact hnotUnion (Or.inl (Or.inl heLarge))
    have heNotDis : e ∉ selectedSupport A.1
        (IsDisjointEntryPart D) := by
      intro heDis
      exact hnotUnion (Or.inl (Or.inr heDis))
    have heNotLoop : e ∉ selectedSupport A.1 (IsLoopEntryPart Q) := by
      intro heLoop
      exact hnotUnion (Or.inr heLoop)
    let B := A.1.part e
    have heU : e ∈ (Finset.univ : Finset (Fin (2 * p))) := Finset.mem_univ e
    have hBpart : B ∈ A.1.parts := A.1.part_mem.2 heU
    have heB : e ∈ B := A.1.mem_part heU
    have hBcard : B.card = 2 := by
      have hge := A.2.1 B hBpart
      have hnotthree : ¬ 3 ≤ B.card := by
        intro hthree
        apply heNotLarge
        rw [aggregateLargePattern_support hd A]
        exact Finset.mem_filter.mpr ⟨heU, hthree⟩
      omega
    have hnotLoopPart : ¬ IsLoopEntryPart Q B := by
      intro hloop
      apply heNotLoop
      exact (mem_selectedSupport A.1 (IsLoopEntryPart Q) e).mpr
        ⟨B, hBpart, hloop, heB⟩
    have hnotDisjointPart : ¬ IsDisjointEntryPart D B := by
      intro hdis
      apply heNotDis
      exact (mem_selectedSupport A.1 (IsDisjointEntryPart D) e).mpr
        ⟨B, hBpart, hdis, heB⟩
    exact (mem_selectedSupport A.1 (IsParallelEntryPart D) e).mpr
      ⟨B, hBpart, ⟨hBcard, hnotLoopPart, hnotDisjointPart⟩, heB⟩

private abbrev AggregateSkeletonBase {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (d h : ℕ) :=
  LargeBlockPattern p d × DisjointPairChoice Q h

private def skeletonLoopSupport {p s t d h : ℕ}
    (Q : SelectorEqualityData p s t) (X : AggregateSkeletonBase Q d h) :
    Finset (Fin (2 * p)) :=
  loopOccurrenceSupport Q \ X.1.1.1

private def skeletonParallelSupport {p s t d h : ℕ}
    (Q : SelectorEqualityData p s t) (X : AggregateSkeletonBase Q d h) :
    Finset (Fin (2 * p)) :=
  Finset.univ \ (X.1.1.1 ∪ X.2.2.1.1 ∪ skeletonLoopSupport Q X)

private def parallelEdgeKeys {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (S : Finset (Fin (2 * p))) : Finset (Finset (EqualityVertex Q.1)) :=
  S.image (entryEdgeKey Q)

private noncomputable def parallelEdgeAt {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (S : Finset (Fin (2 * p)))
    (i : Fin (parallelEdgeKeys Q S).card) : Finset (EqualityVertex Q.1) :=
  ((parallelEdgeKeys Q S).equivFin.symm i).1

private def parallelGroup {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (S : Finset (Fin (2 * p)))
    (i : Fin (parallelEdgeKeys Q S).card) : Finset (Fin (2 * p)) :=
  S.filter fun e ↦ entryEdgeKey Q e = parallelEdgeAt Q S i

private theorem parallelGroup_subset {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (i : Fin (parallelEdgeKeys Q S).card) : parallelGroup Q S i ⊆ S :=
  Finset.filter_subset _ _

private theorem parallelGroup_nonempty {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (i : Fin (parallelEdgeKeys Q S).card) : (parallelGroup Q S i).Nonempty := by
  classical
  have hkey : parallelEdgeAt Q S i ∈ parallelEdgeKeys Q S :=
    ((parallelEdgeKeys Q S).equivFin.symm i).2
  obtain ⟨e, heS, heKey⟩ := Finset.mem_image.mp hkey
  exact ⟨e, Finset.mem_filter.mpr ⟨heS, heKey⟩⟩

private theorem sum_parallelGroup_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p))) :
    ∑ i : Fin (parallelEdgeKeys Q S).card, (parallelGroup Q S i).card = S.card := by
  classical
  let K := parallelEdgeKeys Q S
  let e : Fin K.card ≃ K := K.equivFin.symm
  calc
    (∑ i : Fin K.card, (parallelGroup Q S i).card) =
        ∑ E : K, (S.filter fun x ↦ entryEdgeKey Q x = E.1).card := by
      apply Fintype.sum_equiv e
      intro i
      simp only [e, K, parallelGroup, parallelEdgeAt]
      rfl
    _ = ∑ E ∈ K, (S.filter fun x ↦ entryEdgeKey Q x = E).card := by
      rw [Finset.sum_subtype K (fun _ ↦ Iff.rfl)]
    _ = S.card := (Finset.card_eq_sum_card_image (entryEdgeKey Q) S).symm

private noncomputable def aggregateSkeletonBase
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    AggregateSkeletonBase Q d h :=
  (aggregateLargePattern (by omega) A, aggregateDisjointChoice hp hd A)

private theorem aggregateDisjointChoice_support
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    (aggregateDisjointChoice hp hd A).2.1.1 =
      selectedSupport A.1
        (IsDisjointEntryPart (entryPartitionData Q A.1)) := by
  rfl

private theorem aggregateSkeleton_loopSupport
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    skeletonLoopSupport Q (aggregateSkeletonBase hp hd A) =
      selectedSupport A.1 (IsLoopEntryPart Q) := by
  rw [selectedLoopSupport_eq (by omega) A]
  rfl

private theorem aggregateSkeleton_parallelSupport
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    skeletonParallelSupport Q (aggregateSkeletonBase hp hd A) =
      selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) := by
  rw [selectedParallelSupport_eq_complement (by omega) A]
  rw [← aggregateSkeleton_loopSupport hp hd A]
  rfl

private theorem parallelEdgeAt_mem_keys {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (i : Fin (parallelEdgeKeys Q S).card) :
    parallelEdgeAt Q S i ∈ parallelEdgeKeys Q S := by
  classical
  exact ((parallelEdgeKeys Q S).equivFin.symm i).2

private theorem parallelEdgeAt_card_eq_two_of_nonloop {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (hnonloop : ∀ e ∈ S,
      equalityVertexAt Q.1 e ≠ equalityVertexAt Q.1 (cyclicSucc e))
    (i : Fin (parallelEdgeKeys Q S).card) :
    (parallelEdgeAt Q S i).card = 2 := by
  classical
  obtain ⟨e, heS, hkey⟩ :=
    Finset.mem_image.mp (parallelEdgeAt_mem_keys Q S i)
  rw [← hkey]
  exact Finset.card_pair (hnonloop e heS)

private theorem actual_parallelSupport_nonloop
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (e : Fin (2 * p))
    (he : e ∈ skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) :
    equalityVertexAt Q.1 e ≠ equalityVertexAt Q.1 (cyclicSucc e) := by
  classical
  rw [aggregateSkeleton_parallelSupport hp hd A] at he
  obtain ⟨B, hBpart, hBpar, heB⟩ :=
    (mem_selectedSupport A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) e).mp he
  obtain ⟨f, hfB, hef, hBpair, heNonloop, hfNonloop, hkey⟩ :=
    parallel_entry_part_description (entryPartitionData Q A.1)
      A.2.2.1 B hBpart hBpar e heB
  exact heNonloop

private theorem actual_parallelEdgeAt_card_eq_two
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card) :
    (parallelEdgeAt Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i).card = 2 :=
  parallelEdgeAt_card_eq_two_of_nonloop Q _
    (actual_parallelSupport_nonloop hp hd A) i

private theorem actualParallelGroup_subset
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card) :
    parallelGroup Q (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i ⊆
      selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) := by
  intro x hx
  rw [← aggregateSkeleton_parallelSupport hp hd A]
  exact parallelGroup_subset Q _ i hx

private theorem actualParallelGroup_closed
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card) :
    ∀ x ∈ parallelGroup Q
        (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i,
      (parallelEntryPairing (entryPartitionData Q A.1)).1.part x ⊆
        parallelGroup Q
          (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i := by
  classical
  intro x hxT y hyPart
  have hxSel : x ∈ selectedSupport A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) :=
    actualParallelGroup_subset hp hd A i hxT
  obtain ⟨B, hBpart, hBpar, hxB⟩ :=
    (mem_selectedSupport A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) x).mp hxSel
  have hpartX :
      (parallelEntryPairing (entryPartitionData Q A.1)).1.part x =
        A.1.part x := by
    change (selectedPartition A.1
      (IsParallelEntryPart (entryPartitionData Q A.1))).part x = A.1.part x
    exact selectedPartition_part A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) x hxSel
  have hAx : A.1.part x = B := A.1.part_eq_of_mem hBpart hxB
  have hyB : y ∈ B := by
    rw [← hAx, ← hpartX]
    exact hyPart
  have hySel : y ∈ selectedSupport A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) :=
    (parallelEntryPairing (entryPartitionData Q A.1)).1.part_subset x hyPart
  have hkeyYX : entryEdgeKey Q y = entryEdgeKey Q x := by
    exact parallel_entry_part_edgeKey_eq (entryPartitionData Q A.1)
      A.2.2.1 B hBpart hBpar hyB hxB
  have hxFilter := (Finset.mem_filter.mp hxT).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · rw [aggregateSkeleton_parallelSupport hp hd A]
    exact hySel
  · exact hkeyYX.trans hxFilter

private noncomputable def actualParallelGroupPairing
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card) :
  Pairing (parallelGroup Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i) :=
  pairingRestrict (parallelEntryPairing (entryPartitionData Q A.1)) _
    (by simpa only [entryPartitionData] using
      actualParallelGroup_subset hp hd A i)
    (by simpa only [entryPartitionData] using
      actualParallelGroup_closed hp hd A i)

private theorem actualParallelGroup_even
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card) :
    Even (parallelGroup Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i).card :=
  pairing_support_even (actualParallelGroupPairing hp hd A i)

private theorem actualSkeleton_loopEven
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    Even (skeletonLoopSupport Q (aggregateSkeletonBase hp hd A)).card := by
  rw [aggregateSkeleton_loopSupport hp hd A]
  exact pairing_support_even (loopEntryPairing (entryPartitionData Q A.1))

private theorem actualSkeleton_parallelGroup_count_le
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card ≤ p := by
  classical
  let S := skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)
  let g := (parallelEdgeKeys Q S).card
  have htwo : ∀ i : Fin g, 2 ≤ (parallelGroup Q S i).card := by
    intro i
    have hpos : 0 < (parallelGroup Q S i).card :=
      (parallelGroup_nonempty Q S i).card_pos
    have heven : Even (parallelGroup Q S i).card := by
      simpa [S, g] using actualParallelGroup_even hp hd A i
    obtain ⟨k, hk⟩ := heven
    omega
  have hsumLower : 2 * g ≤ ∑ i : Fin g, (parallelGroup Q S i).card := by
    calc
      2 * g = ∑ _i : Fin g, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin g, (parallelGroup Q S i).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact htwo i
  have hsumEq : (∑ i : Fin g, (parallelGroup Q S i).card) = S.card := by
    simpa [g] using sum_parallelGroup_card Q S
  have hScard : S.card ≤ 2 * p := by
    simpa using Finset.card_le_univ S
  have hg : g ≤ p := by omega
  simpa [g, S] using hg

private theorem parallelEdgeAt_injective {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p))) :
    Function.Injective (parallelEdgeAt Q S) := by
  classical
  intro i j hij
  apply (parallelEdgeKeys Q S).equivFin.symm.injective
  apply Subtype.ext
  exact hij

private def parallelIncidentGroups {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (u : EqualityVertex Q.1) :
    Finset (Fin (parallelEdgeKeys Q S).card) :=
  Finset.univ.filter fun i ↦ u ∈ parallelEdgeAt Q S i

private theorem biUnion_parallelIncidentGroups {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (u : EqualityVertex Q.1) :
    (parallelIncidentGroups Q S u).biUnion (parallelGroup Q S) =
      S.filter fun e ↦ u ∈ entryEdgeKey Q e := by
  classical
  ext e
  simp only [Finset.mem_biUnion, parallelIncidentGroups, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hui, hei⟩
    have heData := Finset.mem_filter.mp hei
    exact ⟨heData.1, heData.2 ▸ hui⟩
  · rintro ⟨heS, hue⟩
    have hkeyMem : entryEdgeKey Q e ∈ parallelEdgeKeys Q S :=
      Finset.mem_image.mpr ⟨e, heS, rfl⟩
    let i : Fin (parallelEdgeKeys Q S).card :=
      (parallelEdgeKeys Q S).equivFin ⟨entryEdgeKey Q e, hkeyMem⟩
    have hiKey : parallelEdgeAt Q S i = entryEdgeKey Q e := by
      exact congrArg Subtype.val
        ((parallelEdgeKeys Q S).equivFin.symm_apply_apply
          ⟨entryEdgeKey Q e, hkeyMem⟩)
    refine ⟨i, ?_, ?_⟩
    · rwa [hiKey]
    · exact Finset.mem_filter.mpr ⟨heS, hiKey.symm⟩

private theorem parallelGroups_pairwiseDisjoint {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p))) :
    ((Finset.univ : Finset (Fin (parallelEdgeKeys Q S).card)) : Set
      (Fin (parallelEdgeKeys Q S).card)).PairwiseDisjoint
        (parallelGroup Q S) := by
  classical
  intro i hi j hj hij
  change Disjoint (parallelGroup Q S i) (parallelGroup Q S j)
  rw [Finset.disjoint_left]
  intro e hei hej
  have hki := (Finset.mem_filter.mp hei).2
  have hkj := (Finset.mem_filter.mp hej).2
  apply hij
  apply parallelEdgeAt_injective Q S
  exact hki.symm.trans hkj

private theorem sum_parallelIncidentGroup_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (u : EqualityVertex Q.1) :
    (∑ i ∈ parallelIncidentGroups Q S u, (parallelGroup Q S i).card) =
      (S.filter fun e ↦ u ∈ entryEdgeKey Q e).card := by
  classical
  rw [← Finset.card_biUnion]
  · exact congrArg Finset.card (biUnion_parallelIncidentGroups Q S u)
  · intro i hi j hj hij
    exact parallelGroups_pairwiseDisjoint Q S (by simp) (by simp) hij

private theorem parallelIncidentOccurrence_card_le_degree {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (S : Finset (Fin (2 * p))) (u : EqualityVertex Q.1) :
    (S.filter fun e ↦ u ∈ entryEdgeKey Q e).card ≤ 2 * u.1.card := by
  classical
  let sourceSet := (Finset.univ : Finset (Fin (2 * p))).filter fun e ↦
    equalityVertexAt Q.1 e = u
  let targetSet := (Finset.univ : Finset (Fin (2 * p))).filter fun e ↦
    equalityVertexAt Q.1 (cyclicSucc e) = u
  have hsubset : (S.filter fun e ↦ u ∈ entryEdgeKey Q e) ⊆
      sourceSet ∪ targetSet := by
    intro e he
    have heData := Finset.mem_filter.mp he
    have hendpoint : equalityVertexAt Q.1 e = u ∨
        equalityVertexAt Q.1 (cyclicSucc e) = u := by
      simpa [entryEdgeKey, eq_comm] using heData.2
    rcases hendpoint with hsrc | hdst
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hsrc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hdst⟩)
  calc
    (S.filter fun e ↦ u ∈ entryEdgeKey Q e).card ≤
        (sourceSet ∪ targetSet).card := Finset.card_le_card hsubset
    _ ≤ sourceSet.card + targetSet.card := Finset.card_union_le sourceSet targetSet
    _ = graphDegree (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
          (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) u := by
      rfl
    _ = 2 * u.1.card := selector_quotient_degree hp Q u

private def highParallelIncidentGroups {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (u : EqualityVertex Q.1) :
    Finset (Fin (parallelEdgeKeys Q S).card) :=
  (parallelIncidentGroups Q S u).filter fun i ↦
    4 < (parallelGroup Q S i).card

private def parallelVertexExcess {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (u : EqualityVertex Q.1) : ℕ :=
  ∑ i ∈ parallelIncidentGroups Q S u,
    ((parallelGroup Q S i).card - 4)

private theorem parallelVertexExcess_le_selectorExcess {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (S : Finset (Fin (2 * p))) (u : EqualityVertex Q.1) :
    parallelVertexExcess Q S u ≤ 2 * u.1.card - 4 := by
  classical
  let I := parallelIncidentGroups Q S u
  let H := highParallelIncidentGroups Q S u
  have hHsub : H ⊆ I := Finset.filter_subset _ _
  have hzero : ∑ i ∈ I.filter (fun i ↦ ¬ 4 < (parallelGroup Q S i).card),
      ((parallelGroup Q S i).card - 4) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hnot := (Finset.mem_filter.mp hi).2
    omega
  have hreduce : parallelVertexExcess Q S u =
      ∑ i ∈ H, ((parallelGroup Q S i).card - 4) := by
    change (∑ i ∈ I, ((parallelGroup Q S i).card - 4)) = _
    calc
      (∑ i ∈ I, ((parallelGroup Q S i).card - 4)) =
          (∑ i ∈ I.filter (fun i ↦ 4 < (parallelGroup Q S i).card),
            ((parallelGroup Q S i).card - 4)) +
          ∑ i ∈ I.filter (fun i ↦ ¬ 4 < (parallelGroup Q S i).card),
            ((parallelGroup Q S i).card - 4) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      _ = ∑ i ∈ H, ((parallelGroup Q S i).card - 4) := by
        rw [hzero, add_zero]
        rfl
  rw [hreduce]
  by_cases hHempty : H = ∅
  · simp [hHempty]
  have hHpos : 0 < H.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hHempty)
  have hsubsum : (∑ i ∈ H, ((parallelGroup Q S i).card - 4)) =
      (∑ i ∈ H, (parallelGroup Q S i).card) - ∑ _i ∈ H, 4 := by
    apply Finset.sum_tsub_distrib
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    omega
  have hHcardSum : (∑ i ∈ H, (parallelGroup Q S i).card) ≤
      ∑ i ∈ I, (parallelGroup Q S i).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hHsub (fun _ _ _ ↦ Nat.zero_le _)
  have hincident : (∑ i ∈ I, (parallelGroup Q S i).card) ≤
      2 * u.1.card := by
    calc
      (∑ i ∈ I, (parallelGroup Q S i).card) =
          (S.filter fun e ↦ u ∈ entryEdgeKey Q e).card := by
        simpa [I] using sum_parallelIncidentGroup_card Q S u
      _ ≤ 2 * u.1.card := parallelIncidentOccurrence_card_le_degree hp Q S u
  have huCard : 2 ≤ u.1.card := Q.2.1 u.1 u.2
  simp only [Finset.sum_const_nat] at hsubsum
  omega

private theorem sum_parallelVertexExcess_eq_twice_groupExcess {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (S : Finset (Fin (2 * p)))
    (hkeyCard : ∀ i : Fin (parallelEdgeKeys Q S).card,
      (parallelEdgeAt Q S i).card = 2) :
    (∑ u : EqualityVertex Q.1, parallelVertexExcess Q S u) =
      2 * ∑ i : Fin (parallelEdgeKeys Q S).card,
        ((parallelGroup Q S i).card - 4) := by
  classical
  have hvertex (u : EqualityVertex Q.1) :
      parallelVertexExcess Q S u =
        ∑ i : Fin (parallelEdgeKeys Q S).card,
          if u ∈ parallelEdgeAt Q S i then
            ((parallelGroup Q S i).card - 4) else 0 := by
    unfold parallelVertexExcess parallelIncidentGroups
    rw [Finset.sum_filter]
  simp_rw [hvertex]
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin (parallelEdgeKeys Q S).card,
        ∑ u : EqualityVertex Q.1,
          if u ∈ parallelEdgeAt Q S i then
            ((parallelGroup Q S i).card - 4) else 0) =
        ∑ i : Fin (parallelEdgeKeys Q S).card,
          2 * ((parallelGroup Q S i).card - 4) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hfilter :
          (Finset.univ : Finset (EqualityVertex Q.1)).filter
              (fun u ↦ u ∈ parallelEdgeAt Q S i) = parallelEdgeAt Q S i := by
        ext u
        simp
      calc
        (∑ u : EqualityVertex Q.1,
            if u ∈ parallelEdgeAt Q S i then
              ((parallelGroup Q S i).card - 4) else 0) =
            (parallelEdgeAt Q S i).card *
              ((parallelGroup Q S i).card - 4) := by
          rw [← Finset.sum_filter, hfilter]
          simp
        _ = 2 * ((parallelGroup Q S i).card - 4) :=
          congrArg (fun n ↦ n * ((parallelGroup Q S i).card - 4))
            (hkeyCard i)
    _ = 2 * ∑ i : Fin (parallelEdgeKeys Q S).card,
          ((parallelGroup Q S i).card - 4) := by
      rw [Finset.mul_sum]

private theorem actualSkeleton_parallelExcess_le
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    (∑ i : Fin (parallelEdgeKeys Q
        (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card,
      ((parallelGroup Q
        (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i).card - 4)) ≤
      2 * s := by
  classical
  let S := skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)
  let excess := ∑ i : Fin (parallelEdgeKeys Q S).card,
    ((parallelGroup Q S i).card - 4)
  have hdouble : (∑ u : EqualityVertex Q.1, parallelVertexExcess Q S u) =
      2 * excess := by
    simpa [excess] using sum_parallelVertexExcess_eq_twice_groupExcess Q S
      (actual_parallelEdgeAt_card_eq_two hp hd A)
  have hvertexSum : (∑ u : EqualityVertex Q.1, parallelVertexExcess Q S u) ≤
      ∑ u : EqualityVertex Q.1, (2 * u.1.card - 4) := by
    apply Finset.sum_le_sum
    intro u hu
    exact parallelVertexExcess_le_selectorExcess hp Q S u
  have htotal : (∑ u : EqualityVertex Q.1, (2 * u.1.card - 4)) =
      4 * s := by
    calc
      (∑ u : EqualityVertex Q.1, (2 * u.1.card - 4)) =
          ∑ B ∈ Q.1.parts, (2 * B.card - 4) := by
        symm
        exact Finset.sum_subtype Q.1.parts (fun _ ↦ Iff.rfl)
          (fun B ↦ 2 * B.card - 4)
      _ = 4 * s := selector_quotient_total_excess hp Q
  have hexcess : excess ≤ 2 * s := by omega
  simpa [excess, S] using hexcess

private structure AggregateSkeletonValid {p s t d h : ℕ}
    (Q : SelectorEqualityData p s t) (X : AggregateSkeletonBase Q d h) : Prop where
  loopEven : Even (skeletonLoopSupport Q X).card
  parallelEven : ∀ i : Fin (parallelEdgeKeys Q
    (skeletonParallelSupport Q X)).card,
    Even (parallelGroup Q (skeletonParallelSupport Q X) i).card
  parallelCount : (parallelEdgeKeys Q (skeletonParallelSupport Q X)).card ≤ p
  parallelExcess :
    (∑ i : Fin (parallelEdgeKeys Q (skeletonParallelSupport Q X)).card,
      ((parallelGroup Q (skeletonParallelSupport Q X) i).card - 4)) ≤ 2 * s

private abbrev AggregateSkeleton {p s t d h : ℕ}
    (Q : SelectorEqualityData p s t) :=
  {X : AggregateSkeletonBase Q d h // AggregateSkeletonValid Q X}

private noncomputable instance aggregateSkeletonFintype
    {p s t d h : ℕ} (Q : SelectorEqualityData p s t) :
    Fintype (AggregateSkeleton (d := d) (h := h) Q) :=
  Fintype.ofFinite _

private noncomputable def aggregateSkeleton
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    AggregateSkeleton (d := d) (h := h) Q :=
  ⟨aggregateSkeletonBase hp hd A,
    { loopEven := actualSkeleton_loopEven hp hd A
      parallelEven := actualParallelGroup_even hp hd A
      parallelCount := actualSkeleton_parallelGroup_count_le hp hd A
      parallelExcess := actualSkeleton_parallelExcess_le hp hd A }⟩

private theorem skeletonLoopSupport_card_le_loopOccurrences
    {p s t d h : ℕ} (Q : SelectorEqualityData p s t)
    (X : AggregateSkeletonBase Q d h) :
    (skeletonLoopSupport Q X).card ≤ equalityLoopOccurrences Q.1 := by
  calc
    (skeletonLoopSupport Q X).card ≤ (loopOccurrenceSupport Q).card :=
      Finset.card_le_card (Finset.sdiff_subset)
    _ = equalityLoopOccurrences Q.1 := loopOccurrenceSupport_card Q

private theorem skeletonLoopSupport_card_le_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (X : AggregateSkeletonBase Q d h) :
    (skeletonLoopSupport Q X).card ≤ 4 * t + 12 * s + 2 :=
  (skeletonLoopSupport_card_le_loopOccurrences Q X).trans
    (degree_four_classification_and_loop_bound hp Q).2.2

private theorem skeletonLoopSupport_card_le_ambient
    {p s t d h : ℕ} (Q : SelectorEqualityData p s t)
    (X : AggregateSkeletonBase Q d h) :
    (skeletonLoopSupport Q X).card ≤ 2 * p := by
  simpa using Finset.card_le_univ (skeletonLoopSupport Q X)

private def pairingCast {α : Type*} [DecidableEq α] {S T : Finset α}
    (hST : S = T) (P : Pairing S) : Pairing T := by
  subst T
  exact P

private theorem pairingCast_parts {α : Type*} [DecidableEq α]
    {S T : Finset α} (hST : S = T) (P : Pairing S) :
    (pairingCast hST P).1.parts = P.1.parts := by
  subst T
  rfl

private abbrev AggregatePartitionCode {p s t d h : ℕ}
    (Q : SelectorEqualityData p s t) :=
  (X : AggregateSkeleton (d := d) (h := h) Q) ×
    Pairing (skeletonLoopSupport Q X.1) ×
      ((i : Fin (parallelEdgeKeys Q
        (skeletonParallelSupport Q X.1)).card) →
        Pairing (parallelGroup Q (skeletonParallelSupport Q X.1) i))

private noncomputable def aggregatePartitionCode
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    AggregatePartitionCode (d := d) (h := h) Q := by
  let X := aggregateSkeleton hp hd A
  refine ⟨X, ?_, ?_⟩
  · exact pairingCast (aggregateSkeleton_loopSupport hp hd A).symm
      (loopEntryPairing (entryPartitionData Q A.1))
  · intro i
    exact actualParallelGroupPairing hp hd A i

private theorem actualParallelGroupPairing_part
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h)
    (i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A))).card)
    (e : Fin (2 * p))
    (he : e ∈ parallelGroup Q
      (skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)) i) :
    (actualParallelGroupPairing hp hd A i).1.part e = A.1.part e := by
  classical
  have hrestrict :
      (actualParallelGroupPairing hp hd A i).1.part e =
        (parallelEntryPairing (entryPartitionData Q A.1)).1.part e := by
    unfold actualParallelGroupPairing
    exact pairingRestrict_part _ _ _ _ e he
  have heSelected : e ∈ selectedSupport A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) :=
    actualParallelGroup_subset hp hd A i he
  have hselected :
      (parallelEntryPairing (entryPartitionData Q A.1)).1.part e =
        A.1.part e := by
    change (selectedPartition A.1
      (IsParallelEntryPart (entryPartitionData Q A.1))).part e = A.1.part e
    exact selectedPartition_part A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) e heSelected
  exact hrestrict.trans hselected

private noncomputable def aggregateCodeParallelParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (C : AggregatePartitionCode (d := d) (h := h) Q) :
    Finset (Finset (Fin (2 * p))) :=
  Finset.univ.biUnion fun i ↦ (C.2.2 i).1.parts

private theorem aggregatePartitionCode_parallelParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    aggregateCodeParallelParts (aggregatePartitionCode hp hd A) =
      selectedParts A.1 (IsParallelEntryPart (entryPartitionData Q A.1)) := by
  classical
  let S := skeletonParallelSupport Q (aggregateSkeletonBase hp hd A)
  change (Finset.univ.biUnion fun i : Fin (parallelEdgeKeys Q S).card ↦
      (actualParallelGroupPairing hp hd A i).1.parts) = _
  ext B
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hBgroup⟩
    obtain ⟨e, heB⟩ :=
      (actualParallelGroupPairing hp hd A i).1.nonempty_of_mem_parts hBgroup
    have heGroup : e ∈ parallelGroup Q S i :=
      (actualParallelGroupPairing hp hd A i).1.le hBgroup heB
    have hgroupPart :
        (actualParallelGroupPairing hp hd A i).1.part e = B :=
      (actualParallelGroupPairing hp hd A i).1.part_eq_of_mem hBgroup heB
    have hAB : A.1.part e = B := by
      rw [← hgroupPart]
      exact (actualParallelGroupPairing_part hp hd A i e heGroup).symm
    have heSelected : e ∈ selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) := by
      simpa [S] using actualParallelGroup_subset hp hd A i heGroup
    obtain ⟨C, hCpart, hCpar, heC⟩ :=
      (mem_selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) e).mp heSelected
    have hAC : A.1.part e = C := A.1.part_eq_of_mem hCpart heC
    apply (mem_selectedParts A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) B).mpr
    refine ⟨?_, ?_⟩
    · rw [← hAB]
      exact A.1.part_mem.2 (Finset.mem_univ e)
    · rw [← hAB, hAC]
      exact hCpar
  · intro hBselected
    have hBdata := (mem_selectedParts A.1
      (IsParallelEntryPart (entryPartitionData Q A.1)) B).mp hBselected
    obtain ⟨e, heB⟩ := A.1.nonempty_of_mem_parts hBdata.1
    have heSelected : e ∈ selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) :=
      (mem_selectedSupport A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) e).mpr
          ⟨B, hBdata.1, hBdata.2, heB⟩
    have heS : e ∈ S := by
      simpa [S, aggregateSkeleton_parallelSupport hp hd A] using heSelected
    have hkeyMem : entryEdgeKey Q e ∈ parallelEdgeKeys Q S :=
      Finset.mem_image.mpr ⟨e, heS, rfl⟩
    let i : Fin (parallelEdgeKeys Q S).card :=
      (parallelEdgeKeys Q S).equivFin ⟨entryEdgeKey Q e, hkeyMem⟩
    have hiKey : parallelEdgeAt Q S i = entryEdgeKey Q e := by
      exact congrArg Subtype.val
        ((parallelEdgeKeys Q S).equivFin.symm_apply_apply
          ⟨entryEdgeKey Q e, hkeyMem⟩)
    have heGroup : e ∈ parallelGroup Q S i :=
      Finset.mem_filter.mpr ⟨heS, hiKey.symm⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hpartMem :=
      (actualParallelGroupPairing hp hd A i).1.part_mem.2 heGroup
    have hcodePart := actualParallelGroupPairing_part hp hd A i e heGroup
    have hApart : A.1.part e = B := A.1.part_eq_of_mem hBdata.1 heB
    rwa [hcodePart, hApart] at hpartMem

private def aggregateCodeLargeParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (C : AggregatePartitionCode (d := d) (h := h) Q) :
    Finset (Finset (Fin (2 * p))) :=
  C.1.1.1.1.2.parts

private def aggregateCodeDisjointParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (C : AggregatePartitionCode (d := d) (h := h) Q) :
    Finset (Finset (Fin (2 * p))) :=
  C.1.1.2.2.2.1.parts

private def aggregateCodeLoopParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (C : AggregatePartitionCode (d := d) (h := h) Q) :
    Finset (Finset (Fin (2 * p))) :=
  C.2.1.1.parts

private theorem aggregatePartitionCode_largeParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    aggregateCodeLargeParts (aggregatePartitionCode hp hd A) =
      selectedParts A.1 IsLargeEntryPart := by
  change (aggregateLargePattern (by omega) A).1.2.parts = _
  change (selectedPartition A.1 IsLargeEntryPart).parts = _
  rw [selectedPartition_parts]

private theorem aggregatePartitionCode_disjointParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    aggregateCodeDisjointParts (aggregatePartitionCode hp hd A) =
      selectedParts A.1
        (IsDisjointEntryPart (entryPartitionData Q A.1)) := by
  change (aggregateDisjointChoice hp hd A).2.2.1.parts = _
  change (selectedPartition A.1
    (IsDisjointEntryPart (entryPartitionData Q A.1))).parts = _
  rw [selectedPartition_parts]

private theorem aggregatePartitionCode_loopParts
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    aggregateCodeLoopParts (aggregatePartitionCode hp hd A) =
      selectedParts A.1 (IsLoopEntryPart Q) := by
  change (pairingCast _
      (loopEntryPairing (entryPartitionData Q A.1))).1.parts =
    selectedParts (entryPartitionData Q A.1).entry
      (IsLoopEntryPart (entryPartitionData Q A.1).selector)
  calc
    (pairingCast _
        (loopEntryPairing (entryPartitionData Q A.1))).1.parts =
        (loopEntryPairing (entryPartitionData Q A.1)).1.parts :=
      pairingCast_parts _ _
    _ = selectedParts (entryPartitionData Q A.1).entry
        (IsLoopEntryPart (entryPartitionData Q A.1).selector) :=
      selectedPartition_parts _ _

private theorem aggregate_entry_parts_component_union
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (A : AggregateEntryPartition Q d h) :
    A.1.parts =
      ((selectedParts A.1 IsLargeEntryPart ∪
        selectedParts A.1
          (IsDisjointEntryPart (entryPartitionData Q A.1))) ∪
        selectedParts A.1 (IsLoopEntryPart Q)) ∪
        selectedParts A.1
          (IsParallelEntryPart (entryPartitionData Q A.1)) := by
  classical
  ext B
  constructor
  · intro hB
    have hBge : 2 ≤ B.card := A.2.1 B hB
    by_cases hlarge : 3 ≤ B.card
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact (mem_selectedParts A.1 IsLargeEntryPart B).mpr ⟨hB, hlarge⟩
    have hBcard : B.card = 2 := by omega
    by_cases hdis : IsDisjointEntryPart (entryPartitionData Q A.1) B
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact (mem_selectedParts A.1
        (IsDisjointEntryPart (entryPartitionData Q A.1)) B).mpr ⟨hB, hdis⟩
    by_cases hloop : IsLoopEntryPart Q B
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact (mem_selectedParts A.1 (IsLoopEntryPart Q) B).mpr ⟨hB, hloop⟩
    · apply Finset.mem_union_right
      apply (mem_selectedParts A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) B).mpr
      exact ⟨hB, hBcard, hloop, hdis⟩
  · intro hB
    rcases Finset.mem_union.mp hB with hfirst | hparallel
    · rcases Finset.mem_union.mp hfirst with hsecond | hloop
      · rcases Finset.mem_union.mp hsecond with hlarge | hdis
        · exact (mem_selectedParts A.1 IsLargeEntryPart B).mp hlarge |>.1
        · exact (mem_selectedParts A.1
            (IsDisjointEntryPart (entryPartitionData Q A.1)) B).mp hdis |>.1
      · exact (mem_selectedParts A.1 (IsLoopEntryPart Q) B).mp hloop |>.1
    · exact (mem_selectedParts A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) B).mp hparallel |>.1

private theorem aggregatePartitionCode_injective
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hp : 2 ≤ p) (hd : d ≤ p - 1) :
    Function.Injective
      (aggregatePartitionCode hp hd : AggregateEntryPartition Q d h →
        AggregatePartitionCode (d := d) (h := h) Q) := by
  classical
  intro A B hcode
  have hlargeCode := congrArg aggregateCodeLargeParts hcode
  have hdisjointCode := congrArg aggregateCodeDisjointParts hcode
  have hloopCode := congrArg aggregateCodeLoopParts hcode
  have hparallelCode := congrArg aggregateCodeParallelParts hcode
  have hlarge : selectedParts A.1 IsLargeEntryPart =
      selectedParts B.1 IsLargeEntryPart := by
    rw [← aggregatePartitionCode_largeParts hp hd A,
      ← aggregatePartitionCode_largeParts hp hd B]
    exact hlargeCode
  have hdisjoint : selectedParts A.1
        (IsDisjointEntryPart (entryPartitionData Q A.1)) =
      selectedParts B.1
        (IsDisjointEntryPart (entryPartitionData Q B.1)) := by
    rw [← aggregatePartitionCode_disjointParts hp hd A,
      ← aggregatePartitionCode_disjointParts hp hd B]
    exact hdisjointCode
  have hloop : selectedParts A.1 (IsLoopEntryPart Q) =
      selectedParts B.1 (IsLoopEntryPart Q) := by
    rw [← aggregatePartitionCode_loopParts hp hd A,
      ← aggregatePartitionCode_loopParts hp hd B]
    exact hloopCode
  have hparallel : selectedParts A.1
        (IsParallelEntryPart (entryPartitionData Q A.1)) =
      selectedParts B.1
        (IsParallelEntryPart (entryPartitionData Q B.1)) := by
    rw [← aggregatePartitionCode_parallelParts hp hd A,
      ← aggregatePartitionCode_parallelParts hp hd B]
    exact hparallelCode
  apply Subtype.ext
  apply Finpartition.ext
  rw [aggregate_entry_parts_component_union A,
    aggregate_entry_parts_component_union B,
    hlarge, hdisjoint, hloop, hparallel]

private theorem skeleton_loopPairing_card_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (X : AggregateSkeleton (d := d) (h := h) Q) :
    Fintype.card (Pairing (skeletonLoopSupport Q X.1)) ≤
      (4 * p + 1) ^ (2 * t + 6 * s + 1) := by
  have hraw := pairing_card_ambient_power_bound p
    (skeletonLoopSupport Q X.1) X.2.loopEven
  have hbase : 2 * p ≤ 4 * p + 1 := by omega
  have hcard := skeletonLoopSupport_card_le_bound hp Q X.1
  have hexp : (skeletonLoopSupport Q X.1).card / 2 ≤
      2 * t + 6 * s + 1 := by omega
  exact hraw.trans (pow_le_pow hbase (by omega) hexp)

private theorem skeleton_parallelPairing_card_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (X : AggregateSkeleton (d := d) (h := h) Q) :
    Fintype.card ((i : Fin (parallelEdgeKeys Q
      (skeletonParallelSupport Q X.1)).card) →
        Pairing (parallelGroup Q (skeletonParallelSupport Q X.1) i)) ≤
      3 ^ p * (4 * p + 1) ^ s := by
  classical
  let S := skeletonParallelSupport Q X.1
  let g := (parallelEdgeKeys Q S).card
  let a : Fin g → ℕ := fun i ↦ (parallelGroup Q S i).card
  have ha : ∀ i : Fin g, 0 < a i ∧ Even (a i) := by
    intro i
    constructor
    · exact (parallelGroup_nonempty Q S i).card_pos
    · simpa [a, g, S] using X.2.parallelEven i
  have hpoint : ∀ i : Fin g,
      Fintype.card (Pairing (parallelGroup Q S i)) ≤
        3 * (4 * p) ^ ((a i - 4) / 2) := by
    intro i
    exact pairing_card_parallel_bound p (parallelGroup Q S i) (ha i).1 (ha i).2
  calc
    Fintype.card ((i : Fin g) → Pairing (parallelGroup Q S i)) =
        ∏ i : Fin g, Fintype.card (Pairing (parallelGroup Q S i)) :=
      Fintype.card_pi
    _ ≤ ∏ i : Fin g, 3 * (4 * p) ^ ((a i - 4) / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        exact hpoint i
    _ ≤ 3 ^ p * (4 * p + 1) ^ s := by
      apply (loop_parallel_pairing_bound p s t 0 hp (by omega) (by omega)).2
      · simpa [g, S] using X.2.parallelCount
      · exact ha
      · simpa [a, g, S] using X.2.parallelExcess

private theorem aggregateSkeleton_card_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    Fintype.card (AggregateSkeleton (d := d) (h := h) Q) ≤
      (4 * p + 1) ^ (12 * d + 12 * h + 2 * s) := by
  calc
    Fintype.card (AggregateSkeleton (d := d) (h := h) Q) ≤
        Fintype.card (AggregateSkeletonBase Q d h) :=
      Fintype.card_subtype_le _
    _ = Fintype.card (LargeBlockPattern p d) *
        Fintype.card (DisjointPairChoice Q h) :=
      Fintype.card_prod _ _
    _ ≤ (4 * p + 1) ^ (12 * d) *
        (4 * p + 1) ^ (12 * h + 2 * s) :=
      Nat.mul_le_mul (large_block_partition_constant_bound p d).1
        (disjoint_pair_support_bound hp Q h).2
    _ = (4 * p + 1) ^ (12 * d + 12 * h + 2 * s) := by
      rw [← pow_add]
      congr 1
      omega

private theorem aggregatePartitionCode_card_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    Fintype.card (AggregatePartitionCode (d := d) (h := h) Q) ≤
      3 ^ p * (4 * p + 1) ^
        (12 * d + 12 * h + 9 * s + 2 * t + 1) := by
  classical
  let skelBound := (4 * p + 1) ^ (12 * d + 12 * h + 2 * s)
  let loopBound := (4 * p + 1) ^ (2 * t + 6 * s + 1)
  let parallelBound := 3 ^ p * (4 * p + 1) ^ s
  have hfiber : ∀ X : AggregateSkeleton (d := d) (h := h) Q,
      Fintype.card (Pairing (skeletonLoopSupport Q X.1) ×
        ((i : Fin (parallelEdgeKeys Q
          (skeletonParallelSupport Q X.1)).card) →
          Pairing (parallelGroup Q (skeletonParallelSupport Q X.1) i))) ≤
        loopBound * parallelBound := by
    intro X
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul (skeleton_loopPairing_card_bound hp Q X)
      (skeleton_parallelPairing_card_bound hp Q X)
  calc
    Fintype.card (AggregatePartitionCode (d := d) (h := h) Q) =
        ∑ X : AggregateSkeleton (d := d) (h := h) Q,
          Fintype.card (Pairing (skeletonLoopSupport Q X.1) ×
            ((i : Fin (parallelEdgeKeys Q
              (skeletonParallelSupport Q X.1)).card) →
              Pairing (parallelGroup Q (skeletonParallelSupport Q X.1) i))) :=
      Fintype.card_sigma
    _ ≤ ∑ _X : AggregateSkeleton (d := d) (h := h) Q,
        loopBound * parallelBound := by
      apply Finset.sum_le_sum
      intro X hX
      exact hfiber X
    _ = Fintype.card (AggregateSkeleton (d := d) (h := h) Q) *
        (loopBound * parallelBound) := by simp
    _ ≤ skelBound * (loopBound * parallelBound) :=
      Nat.mul_le_mul_right _ (aggregateSkeleton_card_bound hp Q)
    _ = 3 ^ p * (4 * p + 1) ^
        (12 * d + 12 * h + 9 * s + 2 * t + 1) := by
      dsimp only [skelBound, loopBound, parallelBound]
      calc
        (4 * p + 1) ^ (12 * d + 12 * h + 2 * s) *
            ((4 * p + 1) ^ (2 * t + 6 * s + 1) *
              (3 ^ p * (4 * p + 1) ^ s)) =
            3 ^ p * (((4 * p + 1) ^ (12 * d + 12 * h + 2 * s) *
              (4 * p + 1) ^ (2 * t + 6 * s + 1)) *
              (4 * p + 1) ^ s) := by ring
        _ = 3 ^ p * (4 * p + 1) ^
            ((12 * d + 12 * h + 2 * s) + (2 * t + 6 * s + 1) + s) := by
          rw [← pow_add, ← pow_add]
        _ = 3 ^ p * (4 * p + 1) ^
            (12 * d + 12 * h + 9 * s + 2 * t + 1) := by
          congr 2
          omega

private theorem selectedParts_sum_card {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Finpartition S) (pred : Finset α → Prop) :
    (∑ B ∈ selectedParts P pred, B.card) = (selectedSupport P pred).card := by
  classical
  rw [← selectedPartition_parts]
  exact (selectedPartition P pred).sum_card_parts

private theorem aggregate_largeBlockConstant_bound
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    (∏ B ∈ selectedParts A.1 IsLargeEntryPart,
      (2 * B.card) ^ (12 * B.card)) ≤
      (4 * p + 1) ^ (72 * d) := by
  classical
  let pattern := aggregateLargePattern (by omega) A
  have hpoint : ∀ B ∈ selectedParts A.1 IsLargeEntryPart,
      (2 * B.card) ^ (12 * B.card) ≤
        (4 * p) ^ (12 * B.card) := by
    intro B hB
    have hBpart := (mem_selectedParts A.1 IsLargeEntryPart B).mp hB |>.1
    have hBcard : B.card ≤ 2 * p := by
      calc
        B.card ≤ (Finset.univ : Finset (Fin (2 * p))).card :=
          Finset.card_le_card (A.1.le hBpart)
        _ = 2 * p := by simp
    exact Nat.pow_le_pow_left (by omega) _
  calc
    (∏ B ∈ selectedParts A.1 IsLargeEntryPart,
        (2 * B.card) ^ (12 * B.card)) ≤
        ∏ B ∈ selectedParts A.1 IsLargeEntryPart,
          (4 * p) ^ (12 * B.card) := by
      apply Finset.prod_le_prod
      · intro B hB
        exact Nat.zero_le _
      · exact hpoint
    _ = (4 * p) ^
        (∑ B ∈ selectedParts A.1 IsLargeEntryPart, 12 * B.card) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (4 * p) ^ (12 * (selectedSupport A.1 IsLargeEntryPart).card) := by
      congr 1
      rw [← Finset.mul_sum, selectedParts_sum_card]
    _ = (4 * p) ^ (12 * pattern.1.1.card) := by rfl
    _ ≤ (4 * p + 1) ^ (72 * d) :=
      (large_block_partition_constant_bound p d).2 pattern

private theorem aggregate_pairBlockConstant_bound
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    (∏ B ∈ selectedParts A.1 (fun B ↦ ¬ IsLargeEntryPart B),
      (2 * B.card) ^ (12 * B.card)) ≤ K₂ ^ p := by
  classical
  let pairs := selectedParts A.1 (fun B ↦ ¬ IsLargeEntryPart B)
  have hcardTwo : ∀ B ∈ pairs, B.card = 2 := by
    intro B hB
    have hB' : B ∈ selectedParts A.1 (fun B ↦ ¬ IsLargeEntryPart B) := by
      simpa only [pairs] using hB
    have hdata := (mem_selectedParts A.1
      (fun B ↦ ¬ IsLargeEntryPart B) B).mp hB'
    have hge := A.2.1 B hdata.1
    unfold IsLargeEntryPart at hdata
    omega
  have hpairsCard : pairs.card ≤ p := by
    calc
      pairs.card ≤ A.1.parts.card := by
        apply Finset.card_le_card
        intro B hB
        exact (mem_selectedParts A.1 (fun B ↦ ¬ IsLargeEntryPart B) B).mp hB |>.1
      _ = p - d := A.2.2.2.1
      _ ≤ p := Nat.sub_le _ _
  calc
    (∏ B ∈ selectedParts A.1 (fun B ↦ ¬ IsLargeEntryPart B),
        (2 * B.card) ^ (12 * B.card)) =
        ∏ _B ∈ pairs, K₂ := by
      apply Finset.prod_congr
      · rfl
      · intro B hB
        rw [hcardTwo B hB]
        norm_num [K₂]
    _ = K₂ ^ pairs.card := by simp
    _ ≤ K₂ ^ p := Nat.pow_le_pow_right (by norm_num [K₂]) hpairsCard

private theorem aggregate_entryPartitionConstant_bound
    {p s t d h : ℕ} {Q : SelectorEqualityData p s t}
    (hd : d ≤ p - 1) (A : AggregateEntryPartition Q d h) :
    entryPartitionCumulantConstant A.1 ≤
      K₂ ^ p * (4 * p + 1) ^ (72 * d) := by
  classical
  unfold entryPartitionCumulantConstant
  calc
    (∏ B ∈ A.1.parts, (2 * B.card) ^ (12 * B.card)) =
        (∏ B ∈ selectedParts A.1 IsLargeEntryPart,
          (2 * B.card) ^ (12 * B.card)) *
        (∏ B ∈ selectedParts A.1 (fun B ↦ ¬ IsLargeEntryPart B),
          (2 * B.card) ^ (12 * B.card)) := by
      unfold selectedParts
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ ≤ (4 * p + 1) ^ (72 * d) * K₂ ^ p :=
      Nat.mul_le_mul (aggregate_largeBlockConstant_bound hd A)
        (aggregate_pairBlockConstant_bound hd A)
    _ = K₂ ^ p * (4 * p + 1) ^ (72 * d) := by ac_rfl

theorem aggregate_partition_cumulant_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (hd : d ≤ p - 1)
    (Q : SelectorEqualityData p s t) :
    aggregateEntryPartitionCumulantSum Q d h ≤
      (3 * K₂) ^ p *
        (4 * p + 1) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) := by
  classical
  let weightBound := K₂ ^ p * (4 * p + 1) ^ (72 * d)
  let countBound := 3 ^ p * (4 * p + 1) ^
    (12 * d + 12 * h + 9 * s + 2 * t + 1)
  have hcard : Fintype.card (AggregateEntryPartition Q d h) ≤
      Fintype.card (AggregatePartitionCode (d := d) (h := h) Q) :=
    Fintype.card_le_of_injective (aggregatePartitionCode hp hd)
      (aggregatePartitionCode_injective hp hd)
  have hsum : aggregateEntryPartitionCumulantSum Q d h ≤
      Fintype.card (AggregateEntryPartition Q d h) * weightBound := by
    unfold aggregateEntryPartitionCumulantSum
    calc
      (∑ A : AggregateEntryPartition Q d h,
          entryPartitionCumulantConstant A.1) ≤
          ∑ _A : AggregateEntryPartition Q d h, weightBound := by
        apply Finset.sum_le_sum
        intro A hA
        exact aggregate_entryPartitionConstant_bound hd A
      _ = Fintype.card (AggregateEntryPartition Q d h) * weightBound := by
        simp
  calc
    aggregateEntryPartitionCumulantSum Q d h ≤
        Fintype.card (AggregateEntryPartition Q d h) * weightBound := hsum
    _ ≤ Fintype.card (AggregatePartitionCode (d := d) (h := h) Q) *
        weightBound := Nat.mul_le_mul_right weightBound hcard
    _ ≤ countBound * weightBound :=
      Nat.mul_le_mul_right weightBound (aggregatePartitionCode_card_bound hp Q)
    _ = (3 * K₂) ^ p *
        (4 * p + 1) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) := by
      dsimp only [countBound, weightBound]
      calc
        (3 ^ p * (4 * p + 1) ^
            (12 * d + 12 * h + 9 * s + 2 * t + 1)) *
            (K₂ ^ p * (4 * p + 1) ^ (72 * d)) =
          (3 * K₂) ^ p *
            ((4 * p + 1) ^ (12 * d + 12 * h + 9 * s + 2 * t + 1) *
              (4 * p + 1) ^ (72 * d)) := by
            rw [mul_pow]
            ring
        _ = (3 * K₂) ^ p * (4 * p + 1) ^
            ((12 * d + 12 * h + 9 * s + 2 * t + 1) + 72 * d) := by
          rw [← pow_add]
        _ = (3 * K₂) ^ p * (4 * p + 1) ^
            (84 * d + 12 * h + 9 * s + 2 * t + 1) := by
          congr 2
          omega

#print axioms pairing_card_sharp_bound
#print axioms pairing_univ_card_sharp_bound
#print axioms pairing_card_parallel_bound
#print axioms aggregate_partition_cumulant_bound

end

end Problem56
