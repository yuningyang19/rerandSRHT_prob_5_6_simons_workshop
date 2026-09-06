import Problem56.Definitions

/-!
Source-faithful counting and support lemmas for the large-block/disjoint-pair
decomposition in interface I24.
-/

open scoped BigOperators

namespace Problem56

private lemma exists_other_of_mem_card_two {α : Type*} [DecidableEq α]
    {B : Finset α} {e : α} (he : e ∈ B) (hBcard : B.card = 2) :
    ∃ f ∈ B, e ≠ f ∧ B = {e, f} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hBcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨y, by simp, hxy, rfl⟩
  · exact ⟨x, by simp, hxy.symm, by ext z; simp [or_comm]⟩

private theorem disjoint_pair_row_support_eq
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
    (Finset.univ.filter fun u ↦ entryConstraintMatrix D B u ≠ 0) =
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
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
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

private theorem entry_partition_excess_sum
    {p s t d : ℕ} (D : EntryCumulantPartitionData p s t)
    (hd : d ≤ p)
    (hnonsingleton : ∀ B ∈ D.entry.parts, 2 ≤ B.card)
    (hblocks : D.entry.parts.card = p - d) :
    ∑ B ∈ D.entry.parts, (B.card - 2) = 2 * d := by
  rw [Finset.sum_tsub_distrib D.entry.parts hnonsingleton]
  rw [D.entry.sum_card_parts]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const_nat]
  rw [hblocks]
  omega

private theorem largeBlockOccurrences_eq_biUnion
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    largeBlockOccurrences D =
      (D.entry.parts.filter fun B ↦ 3 ≤ B.card).biUnion id := by
  classical
  ext e
  simp only [largeBlockOccurrences, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, id_eq]
  constructor
  · intro he
    exact ⟨D.entry.part e, ⟨D.entry.part_mem.2 (Finset.mem_univ e), he⟩,
      D.entry.mem_part (Finset.mem_univ e)⟩
  · rintro ⟨B, ⟨hB, hBlarge⟩, heB⟩
    have hpart : D.entry.part e = B := D.entry.part_eq_of_mem hB heB
    simpa only [hpart] using hBlarge

theorem largeBlockOccurrences_card_le
    {p s t d : ℕ} (D : EntryCumulantPartitionData p s t)
    (hd : d ≤ p)
    (hnonsingleton : ∀ B ∈ D.entry.parts, 2 ≤ B.card)
    (hblocks : D.entry.parts.card = p - d) :
    (largeBlockOccurrences D).card ≤ 6 * d := by
  classical
  let L := D.entry.parts.filter fun B ↦ 3 ≤ B.card
  have hLsub : L ⊆ D.entry.parts := Finset.filter_subset _ _
  have hexcess := entry_partition_excess_sum D hd hnonsingleton hblocks
  have hsum : (largeBlockOccurrences D).card = ∑ B ∈ L, B.card := by
    rw [largeBlockOccurrences_eq_biUnion]
    apply Finset.card_biUnion
    intro B hB C hC hBC
    exact D.entry.disjoint (hLsub hB) (hLsub hC) hBC
  rw [hsum]
  calc
    (∑ B ∈ L, B.card) ≤ ∑ B ∈ L, 3 * (B.card - 2) := by
      apply Finset.sum_le_sum
      intro B hB
      have hlarge : 3 ≤ B.card := (Finset.mem_filter.mp hB).2
      omega
    _ = 3 * ∑ B ∈ L, (B.card - 2) := by rw [Finset.mul_sum]
    _ ≤ 3 * ∑ B ∈ D.entry.parts, (B.card - 2) := by
      exact Nat.mul_le_mul_left 3
        (Finset.sum_le_sum_of_subset_of_nonneg hLsub
          (fun _ _ _ ↦ Nat.zero_le _))
    _ = 6 * d := by rw [hexcess]; omega

theorem largeTouchedVertices_card_le
    {p s t d : ℕ} (D : EntryCumulantPartitionData p s t)
    (hlarge : (largeBlockOccurrences D).card ≤ 6 * d) :
    (largeTouchedVertices D).card ≤ 12 * d := by
  classical
  let endpoints : Fin (2 * p) → Finset (EqualityVertex D.selector.1) :=
    fun e ↦ {equalityVertexAt D.selector.1 e,
      equalityVertexAt D.selector.1 (cyclicSucc e)}
  have hsub : largeTouchedVertices D ⊆
      (largeBlockOccurrences D).biUnion endpoints := by
    intro u hu
    obtain ⟨_, ⟨e, heLarge, he⟩⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_biUnion.mpr
      ⟨e, heLarge, by simpa [endpoints, eq_comm] using he⟩
  calc
    (largeTouchedVertices D).card ≤
        ((largeBlockOccurrences D).biUnion endpoints).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ e ∈ largeBlockOccurrences D, (endpoints e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ largeBlockOccurrences D, 2 := by
      apply Finset.sum_le_sum
      intro e _
      dsimp only [endpoints]
      rcases Finset.card_pair_eq_one_or_two
          (a := equalityVertexAt D.selector.1 e)
          (b := equalityVertexAt D.selector.1 (cyclicSucc e)) with h | h <;>
        omega
    _ = 2 * (largeBlockOccurrences D).card := by
      simp [Nat.mul_comm]
    _ ≤ 12 * d := by omega

theorem disjointConstraintMatrix_rank_le
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    Matrix.rank (disjointConstraintMatrix D) ≤
      Matrix.rank (entryConstraintMatrix D) := by
  classical
  let mask : Matrix (EntryBlock D) (EntryBlock D) (ZMod 2) :=
    Matrix.diagonal fun B ↦ if B ∈ disjointPairRows D then 1 else 0
  have hfactor : disjointConstraintMatrix D = mask * entryConstraintMatrix D := by
    ext B u
    rw [Matrix.diagonal_mul]
    simp [disjointConstraintMatrix]
  rw [hfactor]
  exact Matrix.rank_mul_le_right mask (entryConstraintMatrix D)

theorem disjointConstraintSupport_card_le_rank
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    (disjointConstraintSupport D).card ≤
      4 * Matrix.rank (disjointConstraintMatrix D) := by
  classical
  let A := disjointConstraintMatrix D
  let rowSupport :
      (EqualityVertex D.selector.1 → ZMod 2) →
        Finset (EqualityVertex D.selector.1) :=
    fun v ↦ Finset.univ.filter fun u ↦ v u ≠ 0
  let S : Set (EqualityVertex D.selector.1 → ZMod 2) := Set.range A.row
  obtain ⟨T, hTsub, hTcard, hTspan, _hTindep⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) S
  let U := T.biUnion rowSupport
  have hsupport : disjointConstraintSupport D ⊆ U := by
    intro u hu
    obtain ⟨B, hBu⟩ := (Finset.mem_filter.mp hu).2
    have hrowmem : A.row B ∈ Submodule.span (ZMod 2) S :=
      Submodule.subset_span (Set.mem_range_self B)
    rw [← hTspan] at hrowmem
    by_contra huU
    have hgen : ∀ v ∈ T, v u = 0 := by
      intro v hv
      by_contra hvu
      apply huU
      exact Finset.mem_biUnion.mpr
        ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hvu⟩⟩
    have hzero : A.row B u = 0 := by
      refine Submodule.span_induction (p := fun v _ ↦ v u = 0)
        ?_ ?_ ?_ ?_ hrowmem
      · intro v hv
        exact hgen v hv
      · rfl
      · intro v w _ _ hv hw
        simp [hv, hw]
      · intro c v _ hv
        simp [hv]
    exact hBu hzero
  have hrowSupport : ∀ v ∈ T, (rowSupport v).card ≤ 4 := by
    intro v hv
    obtain ⟨B, rfl⟩ := hTsub hv
    by_cases hB : B ∈ disjointPairRows D
    · have hcard := (Finset.mem_filter.mp hB).2
      change (Finset.univ.filter fun u ↦
        disjointConstraintMatrix D B u ≠ 0).card ≤ 4
      simpa only [disjointConstraintMatrix, hB, ↓reduceIte] using hcard.le
    · have hzero : A.row B = 0 := by
        funext u
        simp [A, disjointConstraintMatrix, hB]
      simp [rowSupport, hzero]
  calc
    (disjointConstraintSupport D).card ≤ U.card :=
      Finset.card_le_card hsupport
    _ ≤ ∑ v ∈ T, (rowSupport v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ T, 4 := by
      exact Finset.sum_le_sum fun v hv ↦ hrowSupport v hv
    _ = 4 * T.card := by simp [Nat.mul_comm]
    _ = 4 * Matrix.rank A := by
      rw [hTcard, Matrix.rank_eq_finrank_span_row]
    _ = 4 * Matrix.rank (disjointConstraintMatrix D) := by rfl

set_option maxHeartbeats 1000000 in
theorem oddIncidentVertexSet_subset_largeTouched_union_disjointSupport
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (hnonsingleton : ∀ B ∈ D.entry.parts, 2 ≤ B.card)
    (hadmissible : AdmissibleEntryPairBlocks D) :
    oddIncidentVertexSet D ⊆
      largeTouchedVertices D ∪ disjointConstraintSupport D := by
  classical
  intro u hu
  by_cases huLarge : u ∈ largeTouchedVertices D
  · exact Finset.mem_union_left _ huLarge
  by_cases huDisjoint : u ∈ disjointConstraintSupport D
  · exact Finset.mem_union_right _ huDisjoint
  exfalso
  have huOdd : u.1 ∈ equalityOddIncidentVertices D.selector.1 :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨C, hC, huC, hodd⟩ := (Finset.mem_filter.mp huOdd).2
  let v : EqualityVertex D.selector.1 := ⟨C, hC⟩
  have huv : u ≠ v := by
    intro h
    exact huC (Subtype.ext_iff.mp h)
  let S : Finset (Fin (2 * p)) :=
    Finset.univ.filter fun e ↦
      (equalityVertexAt D.selector.1 e = u ∧
        equalityVertexAt D.selector.1 (cyclicSucc e) = v) ∨
      (equalityVertexAt D.selector.1 e = v ∧
        equalityVertexAt D.selector.1 (cyclicSucc e) = u)
  have hScard : S.card = equalityEdgeMultiplicity D.selector.1 u.1 C := by
    unfold S equalityEdgeMultiplicity
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [equalityVertexAt, Subtype.ext_iff, v]
  have hSodd : Odd S.card := by
    rw [hScard]
    exact hodd
  have hblockEven : ∀ B ∈ D.entry.parts, Even (B ∩ S).card := by
    intro B hB
    by_cases hBS : B ∩ S = ∅
    · simp [hBS]
    obtain ⟨e, heInter⟩ := Finset.nonempty_iff_ne_empty.mpr hBS
    have heB : e ∈ B := (Finset.mem_inter.mp heInter).1
    have heS : e ∈ S := (Finset.mem_inter.mp heInter).2
    have heCross := (Finset.mem_filter.mp heS).2
    have heNonloop : equalityVertexAt D.selector.1 e ≠
        equalityVertexAt D.selector.1 (cyclicSucc e) := by
      intro heq
      rcases heCross with ⟨heu, hev⟩ | ⟨hev, heu⟩
      · exact huv (heu.symm.trans (heq.trans hev))
      · exact huv (hev.symm.trans (heq.trans heu)).symm
    have heNotLarge : e ∉ largeBlockOccurrences D := by
      intro heLarge
      apply huLarge
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ u, e, heLarge, ?_⟩
      rcases heCross with ⟨heu, _⟩ | ⟨_, heu⟩
      · exact Or.inl heu
      · exact Or.inr heu
    have hpart : D.entry.part e = B :=
      D.entry.part_eq_of_mem hB heB
    have hnotthree : ¬ 3 ≤ B.card := by
      intro hthree
      apply heNotLarge
      simp only [largeBlockOccurrences, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa only [hpart] using hthree
    have hBcard : B.card = 2 := by
      have := hnonsingleton B hB
      omega
    obtain ⟨f, hfB, hef, hBpair⟩ :=
      exists_other_of_mem_card_two heB hBcard
    have htri := hadmissible B hB hBcard e heB f hfB hef
    have hfS : f ∈ S := by
      rcases htri with hloops | hparallel | hdisjoint
      · exact (heNonloop hloops.1).elim
      · rcases hparallel with ⟨_, _, hparallel⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ f, ?_⟩
        rcases hparallel with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
        · rcases heCross with ⟨heu, hev⟩ | ⟨hev, heu⟩
          · exact Or.inl ⟨hsrc.symm.trans heu, hdst.symm.trans hev⟩
          · exact Or.inr ⟨hsrc.symm.trans hev, hdst.symm.trans heu⟩
        · rcases heCross with ⟨heu, hev⟩ | ⟨hev, heu⟩
          · exact Or.inr ⟨hdst.symm.trans hev, hsrc.symm.trans heu⟩
          · exact Or.inl ⟨hdst.symm.trans heu, hsrc.symm.trans hev⟩
      · rcases hdisjoint with ⟨he', hf', hdisjoint⟩
        let B' : EntryBlock D := ⟨B, hB⟩
        have hrowSupport := disjoint_pair_row_support_eq D B' e f
          (by simpa only [B'] using hBpair) hef he' hf' hdisjoint
        have hfour :
            ({equalityVertexAt D.selector.1 e,
                equalityVertexAt D.selector.1 (cyclicSucc e),
                equalityVertexAt D.selector.1 f,
                equalityVertexAt D.selector.1 (cyclicSucc f)} :
              Finset (EqualityVertex D.selector.1)).card = 4 := by
          rw [show
            ({equalityVertexAt D.selector.1 e,
                equalityVertexAt D.selector.1 (cyclicSucc e),
                equalityVertexAt D.selector.1 f,
                equalityVertexAt D.selector.1 (cyclicSucc f)} :
              Finset (EqualityVertex D.selector.1)) =
              {equalityVertexAt D.selector.1 e,
                  equalityVertexAt D.selector.1 (cyclicSucc e)} ∪
                {equalityVertexAt D.selector.1 f,
                  equalityVertexAt D.selector.1 (cyclicSucc f)} by
                ext z
                simp only [Finset.mem_insert, Finset.mem_singleton,
                  Finset.mem_union]
                tauto]
          rw [Finset.card_union_of_disjoint hdisjoint,
            Finset.card_pair he', Finset.card_pair hf']
        have hrow : B' ∈ disjointPairRows D := by
          simp only [disjointPairRows, Finset.mem_filter,
            Finset.mem_univ, true_and]
          rw [hrowSupport]
          exact hfour
        have huRowSet : u ∈
            ({equalityVertexAt D.selector.1 e,
                equalityVertexAt D.selector.1 (cyclicSucc e),
                equalityVertexAt D.selector.1 f,
                equalityVertexAt D.selector.1 (cyclicSucc f)} :
              Finset (EqualityVertex D.selector.1)) := by
          rcases heCross with ⟨heu, _⟩ | ⟨_, heu⟩
          · exact Finset.mem_insert.mpr (Or.inl heu.symm)
          · exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl heu.symm)))
        have huEntry : entryConstraintMatrix D B' u ≠ 0 := by
          have huFilter : u ∈ Finset.univ.filter fun w ↦
              entryConstraintMatrix D B' w ≠ 0 := by
            rw [hrowSupport]
            exact huRowSet
          exact (Finset.mem_filter.mp huFilter).2
        have huDisjointRow : disjointConstraintMatrix D B' u ≠ 0 := by
          simp only [disjointConstraintMatrix, hrow, if_true]
          exact huEntry
        exfalso
        apply (huDisjoint : ¬ u ∈ disjointConstraintSupport D)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ u, ⟨B', huDisjointRow⟩⟩
    have hBsubS : B ⊆ S := by
      intro z hz
      rw [hBpair] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact heS
      · exact hfS
    have hinter : B ∩ S = B := Finset.inter_eq_left.mpr hBsubS
    rw [hinter, hBcard]
    norm_num
  have hSuniv : S ⊆ (Finset.univ : Finset (Fin (2 * p))) := by simp
  have hsum : (∑ B ∈ D.entry.parts, (B ∩ S).card) = S.card := by
    have hrestrict :=
      D.entry.sum_restrict hSuniv (fun A ↦ A.card) (by simp)
    simpa only [Finset.inf_eq_inter] using
      hrestrict.symm.trans (D.entry.restrict hSuniv).sum_card_parts
  have hSeven : Even S.card := by
    rw [← hsum]
    exact Finset.even_sum (fun B ↦ (B ∩ S).card) hblockEven
  exact (Nat.not_even_iff_odd.mpr hSodd) hSeven

theorem oddIncidentVertexSet_card
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :
    (oddIncidentVertexSet D).card = t := by
  classical
  let emb : EqualityVertex D.selector.1 ↪ Finset (Fin (2 * p)) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (oddIncidentVertexSet D).map emb =
      equalityOddIncidentVertices D.selector.1 := by
    ext B
    constructor
    · intro hB
      obtain ⟨u, hu, hub⟩ := Finset.mem_map.mp hB
      have huOdd := (Finset.mem_filter.mp hu).2
      simpa only [emb, Function.Embedding.coeFn_mk] using hub ▸ huOdd
    · intro hB
      have hBpart : B ∈ D.selector.1.parts :=
        (Finset.mem_filter.mp hB).1
      let u : EqualityVertex D.selector.1 := ⟨B, hBpart⟩
      apply Finset.mem_map.mpr
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hB⟩, rfl⟩
  calc
    (oddIncidentVertexSet D).card =
        ((oddIncidentVertexSet D).map emb).card := (Finset.card_map _).symm
    _ = (equalityOddIncidentVertices D.selector.1).card :=
      congrArg Finset.card hmap
    _ = t := D.selector.2.2.2

theorem large_block_and_support_rank_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (hd : d ≤ p - 1)
    (D : EntryCumulantPartitionData p s t)
    (hnonsingleton : ∀ B ∈ D.entry.parts, 2 ≤ B.card)
    (hadmissible : AdmissibleEntryPairBlocks D)
    (hblocks : D.entry.parts.card = p - d)
    (hrank : Matrix.rank (entryConstraintMatrix D) = h) :
    (largeBlockOccurrences D).card ≤ 6 * d ∧
    (largeTouchedVertices D).card ≤ 12 * d ∧
    oddIncidentVertexSet D ⊆
      largeTouchedVertices D ∪ disjointConstraintSupport D ∧
    Matrix.rank (disjointConstraintMatrix D) ≤ h ∧
    (disjointConstraintSupport D).card ≤ 4 * h ∧
    t ≤ 12 * d + 4 * h := by
  have hd' : d ≤ p := by omega
  have hlarge :=
    largeBlockOccurrences_card_le D hd' hnonsingleton hblocks
  have htouched := largeTouchedVertices_card_le D hlarge
  have hsubset :=
    oddIncidentVertexSet_subset_largeTouched_union_disjointSupport D
      hnonsingleton hadmissible
  have hrank' := disjointConstraintMatrix_rank_le D
  rw [hrank] at hrank'
  have hsupport : (disjointConstraintSupport D).card ≤ 4 * h := by
    calc
      (disjointConstraintSupport D).card ≤
          4 * Matrix.rank (disjointConstraintMatrix D) :=
        disjointConstraintSupport_card_le_rank D
      _ ≤ 4 * h := Nat.mul_le_mul_left 4 hrank'
  refine ⟨hlarge, htouched, hsubset, hrank', hsupport, ?_⟩
  calc
    t = (oddIncidentVertexSet D).card := (oddIncidentVertexSet_card D).symm
    _ ≤ (largeTouchedVertices D ∪ disjointConstraintSupport D).card :=
      Finset.card_le_card hsubset
    _ ≤ (largeTouchedVertices D).card +
        (disjointConstraintSupport D).card :=
      Finset.card_union_le (largeTouchedVertices D)
        (disjointConstraintSupport D)
    _ ≤ 12 * d + 4 * h := Nat.add_le_add htouched hsupport

end Problem56
