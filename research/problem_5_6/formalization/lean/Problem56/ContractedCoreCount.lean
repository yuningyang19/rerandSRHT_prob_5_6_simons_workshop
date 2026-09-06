import Problem56.EncodingCount
import Problem56.EqualityDegreeFour

/-!
The finite-code-space part of the contracted-core interface, together with a
generic construction turning an injective full code into an actual decoder.
-/

namespace Problem56

private theorem equality_odd_vertices_subset_exceptional {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    equalityOddIncidentVertices P ⊆ equalityExceptionalVertices P := by
  exact Finset.subset_union_left

private theorem equality_exceptional_vertices_subset_parts {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    equalityExceptionalVertices P ⊆ P.parts := by
  exact Finset.union_subset (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)

noncomputable def equalityRetainedVertices {p s t : ℕ}
    (Q : SelectorEqualityData p s t) : Finset (EqualityVertex Q.1) := by
  classical
  exact Finset.univ.filter fun u ↦
    u.1 ∈ equalityExceptionalVertices Q.1 ∨
      IsEqualityLoopTerminal Q.1 u.1 ∨ IsEqualityFourEdgeTerminal Q.1 u.1

noncomputable def equalityExceptionalCoreVertices {p s t : ℕ}
    (Q : SelectorEqualityData p s t) : Finset (EqualityVertex Q.1) := by
  classical
  exact Finset.univ.filter fun u ↦
    u.1 ∈ equalityExceptionalVertices Q.1

noncomputable def equalityTerminalVerticesOutsideCore {p s t : ℕ}
    (Q : SelectorEqualityData p s t) : Finset (EqualityVertex Q.1) := by
  classical
  exact Finset.univ.filter fun u ↦
    u.1 ∉ equalityExceptionalVertices Q.1 ∧
      (IsEqualityLoopTerminal Q.1 u.1 ∨
        IsEqualityFourEdgeTerminal Q.1 u.1)

theorem equality_exceptional_core_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (equalityExceptionalCoreVertices Q).card =
      (equalityExceptionalVertices Q.1).card := by
  classical
  let emb : EqualityVertex Q.1 ↪ Finset (Fin (2 * p)) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (equalityExceptionalCoreVertices Q).map emb =
      equalityExceptionalVertices Q.1 := by
    ext B
    constructor
    · intro hB
      obtain ⟨u, hu, hub⟩ := Finset.mem_map.mp hB
      have huExceptional := (Finset.mem_filter.mp hu).2
      simpa only [emb, Function.Embedding.coeFn_mk] using hub ▸ huExceptional
    · intro hB
      have hBpart := equality_exceptional_vertices_subset_parts Q.1 hB
      let u : EqualityVertex Q.1 := ⟨B, hBpart⟩
      apply Finset.mem_map.mpr
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hB⟩, rfl⟩
  calc
    (equalityExceptionalCoreVertices Q).card =
        ((equalityExceptionalCoreVertices Q).map emb).card :=
      (Finset.card_map _).symm
    _ = (equalityExceptionalVertices Q.1).card :=
      congrArg Finset.card hmap

private theorem sum_equality_exceptional_core {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (f : Finset (Fin (2 * p)) → ℕ) :
    (∑ u ∈ equalityExceptionalCoreVertices Q, f u.1) =
      ∑ B ∈ equalityExceptionalVertices Q.1, f B := by
  classical
  apply Finset.sum_bij (fun u _ ↦ u.1)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u₁ hu₁ u₂ hu₂ h
    exact Subtype.ext h
  · intro B hB
    let u : EqualityVertex Q.1 :=
      ⟨B, equality_exceptional_vertices_subset_parts Q.1 hB⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hB⟩, rfl⟩
  · intro u hu
    rfl

private theorem equality_nonexceptional_card_two {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1)
    (hu : u.1 ∉ equalityExceptionalVertices Q.1) :
    u.1.card = 2 := by
  have htwo := Q.2.1 u.1 u.2
  have hnotLarge : ¬2 < u.1.card := by
    intro hlarge
    apply hu
    exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨u.2, hlarge⟩)
  omega

theorem equality_exceptional_core_size_degree_bounds
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (equalityExceptionalCoreVertices Q).card ≤ 2 * (s + t) ∧
      equalityExceptionalDegree Q.1 ≤ 12 * (s + t) := by
  have hbudget := selector_exceptional_vertex_degree_budget hp Q
  constructor
  · rw [equality_exceptional_core_card]
    omega
  · omega

theorem equality_retained_eq_core_union_terminals {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    equalityRetainedVertices Q =
      equalityExceptionalCoreVertices Q ∪
        equalityTerminalVerticesOutsideCore Q := by
  classical
  ext u
  simp only [equalityRetainedVertices, equalityExceptionalCoreVertices,
    equalityTerminalVerticesOutsideCore, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  tauto

theorem equality_retained_card_le_of_terminal_port_budget
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (hports :
      2 * (equalityTerminalVerticesOutsideCore Q).card ≤
        equalityExceptionalDegree Q.1) :
    (equalityRetainedVertices Q).card ≤ 8 * (s + t) := by
  have hbudget := selector_exceptional_vertex_degree_budget hp Q
  have hterminal :
      (equalityTerminalVerticesOutsideCore Q).card ≤ 2 * t + 6 * s := by
    omega
  rw [equality_retained_eq_core_union_terminals]
  calc
    (equalityExceptionalCoreVertices Q ∪
        equalityTerminalVerticesOutsideCore Q).card ≤
        (equalityExceptionalCoreVertices Q).card +
          (equalityTerminalVerticesOutsideCore Q).card :=
      Finset.card_union_le _ _
    _ = (equalityExceptionalVertices Q.1).card +
          (equalityTerminalVerticesOutsideCore Q).card := by
      rw [equality_exceptional_core_card]
    _ ≤ (t + 2 * s) + (2 * t + 6 * s) :=
      Nat.add_le_add hbudget.1 hterminal
    _ ≤ 8 * (s + t) := by omega

theorem equality_retained_degree_le_of_terminal_port_budget
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (hports :
      2 * (equalityTerminalVerticesOutsideCore Q).card ≤
        equalityExceptionalDegree Q.1) :
    (∑ u ∈ equalityRetainedVertices Q, 2 * u.1.card) ≤
      36 * (s + t) := by
  classical
  let E := equalityExceptionalCoreVertices Q
  let T := equalityTerminalVerticesOutsideCore Q
  have hdisjoint : Disjoint E T := by
    rw [Finset.disjoint_left]
    intro u huE huT
    have huExceptional : u.1 ∈ equalityExceptionalVertices Q.1 :=
      (Finset.mem_filter.mp huE).2
    have huNotExceptional : u.1 ∉ equalityExceptionalVertices Q.1 :=
      (Finset.mem_filter.mp huT).2.1
    exact huNotExceptional huExceptional
  have hcoreSum : (∑ u ∈ E, 2 * u.1.card) =
      equalityExceptionalDegree Q.1 := by
    change (∑ u ∈ equalityExceptionalCoreVertices Q, 2 * u.1.card) = _
    exact sum_equality_exceptional_core Q (fun B ↦ 2 * B.card)
  have hterminalSum : (∑ u ∈ T, 2 * u.1.card) = 4 * T.card := by
    calc
      (∑ u ∈ T, 2 * u.1.card) = ∑ _u ∈ T, 4 := by
        apply Finset.sum_congr rfl
        intro u huT
        have huNotExceptional :
            u.1 ∉ equalityExceptionalVertices Q.1 :=
          (Finset.mem_filter.mp huT).2.1
        rw [equality_nonexceptional_card_two Q u huNotExceptional]
      _ = 4 * T.card := by simp [Nat.mul_comm]
  have hbudget := (selector_exceptional_vertex_degree_budget hp Q).2
  rw [equality_retained_eq_core_union_terminals,
    Finset.sum_union hdisjoint]
  change (∑ u ∈ E, 2 * u.1.card) + (∑ u ∈ T, 2 * u.1.card) ≤ _
  rw [hcoreSum, hterminalSum]
  change 2 * T.card ≤ equalityExceptionalDegree Q.1 at hports
  omega

theorem equality_exceptional_nonempty_of_parameter_ne_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (equalityExceptionalVertices Q.1).Nonempty := by
  classical
  by_contra hnonempty
  have hE : equalityExceptionalVertices Q.1 = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have hoddEmpty : equalityOddIncidentVertices Q.1 = ∅ := by
    apply Finset.subset_empty.mp
    intro B hB
    have hBE : B ∈ equalityExceptionalVertices Q.1 :=
      equality_odd_vertices_subset_exceptional Q.1 hB
    rw [hE] at hBE
    exact hBE
  have ht : t = 0 := by
    have hcard := Q.2.2.2
    rw [hoddEmpty] at hcard
    simpa using hcard.symm
  have hcardTwo : ∀ B ∈ Q.1.parts, B.card = 2 := by
    intro B hB
    have hBnot : B ∉ equalityExceptionalVertices Q.1 := by
      intro hmem
      rw [hE] at hmem
      exact Finset.notMem_empty B hmem
    have hnotLarge : ¬2 < B.card := by
      intro hlarge
      apply hBnot
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hB, hlarge⟩
    have htwo := Q.2.1 B hB
    omega
  have hsum := Q.1.sum_card_parts
  have hsumTwo : (∑ B ∈ Q.1.parts, B.card) =
      ∑ _B ∈ Q.1.parts, 2 := by
    apply Finset.sum_congr rfl
    intro B hB
    exact hcardTwo B hB
  have hsumConst : (∑ _B ∈ Q.1.parts, 2) = 2 * Q.1.parts.card := by
    simp [Nat.mul_comm]
  rw [hsumTwo, hsumConst, Q.2.2.1] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hs : s = 0 := by omega
  omega

theorem equality_exceptional_core_nonempty_of_parameter_ne_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (equalityExceptionalCoreVertices Q).Nonempty := by
  classical
  obtain ⟨B, hBExceptional⟩ :=
    equality_exceptional_nonempty_of_parameter_ne_zero hp Q ha
  have hBpart : B ∈ Q.1.parts :=
    equality_exceptional_vertices_subset_parts Q.1 hBExceptional
  let u : EqualityVertex Q.1 := ⟨B, hBpart⟩
  exact ⟨u, Finset.mem_filter.mpr
    ⟨Finset.mem_univ u, hBExceptional⟩⟩

theorem equality_exceptional_empty_of_parameter_eq_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : s + t = 0) :
    equalityExceptionalVertices Q.1 = ∅ := by
  have hcard := (selector_exceptional_vertex_degree_budget hp Q).1
  have hzero : t + 2 * s = 0 := by omega
  rw [hzero] at hcard
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)

theorem equality_exceptional_empty_iff_parameter_eq_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    equalityExceptionalVertices Q.1 = ∅ ↔ s + t = 0 := by
  constructor
  · intro hE
    by_contra ha
    have hapos : 0 < s + t := Nat.pos_of_ne_zero ha
    obtain ⟨B, hB⟩ :=
      equality_exceptional_nonempty_of_parameter_ne_zero hp Q hapos
    rw [hE] at hB
    exact Finset.notMem_empty B hB
  · exact equality_exceptional_empty_of_parameter_eq_zero hp Q

theorem equality_exceptional_or_degree_four_type
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : Finset (Fin (2 * p))) (hB : B ∈ Q.1.parts) :
    B ∈ equalityExceptionalVertices Q.1 ∨
      IsEqualityInternal Q.1 B ∨ IsEqualityLoopTerminal Q.1 B ∨
        IsEqualityFourEdgeTerminal Q.1 B := by
  by_cases hExceptional : B ∈ equalityExceptionalVertices Q.1
  · exact Or.inl hExceptional
  · exact Or.inr
      ((degree_four_classification_and_loop_bound hp Q).1 B hB hExceptional)

theorem equality_retained_vertices_nonempty_of_parameter_ne_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (equalityRetainedVertices Q).Nonempty := by
  classical
  obtain ⟨B, hBExceptional⟩ :=
    equality_exceptional_nonempty_of_parameter_ne_zero hp Q ha
  have hBpart : B ∈ Q.1.parts :=
    equality_exceptional_vertices_subset_parts Q.1 hBExceptional
  let u : EqualityVertex Q.1 := ⟨B, hBpart⟩
  exact ⟨u, Finset.mem_filter.mpr
    ⟨Finset.mem_univ u, Or.inl hBExceptional⟩⟩

theorem equality_internal_of_not_mem_retained
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∉ equalityRetainedVertices Q) :
    IsEqualityInternal Q.1 u.1 := by
  classical
  have hnot :
      ¬(u.1 ∈ equalityExceptionalVertices Q.1 ∨
        IsEqualityLoopTerminal Q.1 u.1 ∨
          IsEqualityFourEdgeTerminal Q.1 u.1) := by
    simpa only [equalityRetainedVertices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hu
  rcases equality_exceptional_or_degree_four_type hp Q u.1 u.2 with
    hExceptional | hInternal | hLoopTerminal | hFourTerminal
  · exact (hnot (Or.inl hExceptional)).elim
  · exact hInternal
  · exact (hnot (Or.inr (Or.inl hLoopTerminal))).elim
  · exact (hnot (Or.inr (Or.inr hFourTerminal))).elim

abbrev FullEqualityCode (p a : ℕ) :=
  Σ c : ContractedCoreCode p a, EulerTransitions c

private noncomputable def fintypeEmbeddingOfCardLE
    {α β : Type*} [Fintype α] [Fintype β]
    (hcard : Fintype.card α ≤ Fintype.card β) : α ↪ β where
  toFun x := (Fintype.equivFin β).symm
    (Fin.castLE hcard (Fintype.equivFin α x))
  inj' := by
    intro x y hxy
    apply (Fintype.equivFin α).injective
    apply Fin.castLE_injective hcard
    exact (Fintype.equivFin β).symm.injective hxy

noncomputable def equalityEncodingOfInjective {p s t : ℕ}
    (f : SelectorEqualityData p s t → FullEqualityCode p (s + t))
    (hf : Function.Injective f) : EqualityEncoding p s t := by
  classical
  by_cases hsource : Nonempty (SelectorEqualityData p s t)
  · letI : Nonempty (SelectorEqualityData p s t) := hsource
    exact
      { encodeCore := fun Q ↦ (f Q).1
        encodeTransition := fun Q ↦ (f Q).2
        decode := fun c e ↦ some (Function.invFun f ⟨c, e⟩)
        decode_encode := fun Q ↦ by
          rw [Function.leftInverse_invFun hf Q] }
  · exact
      { encodeCore := fun Q ↦ (hsource ⟨Q⟩).elim
        encodeTransition := fun Q ↦ (hsource ⟨Q⟩).elim
        decode := fun _ _ ↦ none
        decode_encode := fun Q ↦ (hsource ⟨Q⟩).elim }

private theorem fullEqualityCode_card (p a : ℕ) :
    Fintype.card (FullEqualityCode p a) =
      (4 * p + 1) ^ (72 * a) *
        (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a)) := by
  simp only [FullEqualityCode, Fintype.card_sigma]
  rw [show (∑ _c : ContractedCoreCode p a,
      Fintype.card (EulerTransitionCode p a)) =
      Fintype.card (ContractedCoreCode p a) *
        Fintype.card (EulerTransitionCode p a) by simp]
  rw [contracted_core_code_card, euler_transition_code_card]

private theorem equalityEncoding_of_card_bound (p s t : ℕ)
    (hcard : selectorEqualityCount p s t ≤
      (4 * p + 1) ^ (72 * (s + t)) *
        (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t)))) :
    Nonempty (EqualityEncoding p s t) := by
  change Fintype.card (SelectorEqualityData p s t) ≤ _ at hcard
  rw [← fullEqualityCode_card] at hcard
  let f : SelectorEqualityData p s t ↪ FullEqualityCode p (s + t) :=
    fintypeEmbeddingOfCardLE hcard
  exact ⟨equalityEncodingOfInjective f f.injective⟩

theorem contracted_core_code_card_bound (p s t : ℕ) :
    Fintype.card (ContractedCoreCode p (s + t)) ≤
      (4 * p + 1) ^ (72 * (s + t)) := by
  exact (contracted_core_code_card p (s + t)).le

theorem equality_encoding_nonempty_iff_card_bound (p s t : ℕ) :
    Nonempty (EqualityEncoding p s t) ↔
      selectorEqualityCount p s t ≤
        (4 * p + 1) ^ (72 * (s + t)) *
          (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) := by
  constructor
  · rintro ⟨enc⟩
    exact (euler_transition_count p s t enc).2
  · exact equalityEncoding_of_card_bound p s t

theorem contracted_core_encoding_bound_iff_card_bound (p s t : ℕ) :
    (Fintype.card (ContractedCoreCode p (s + t)) ≤
          (4 * p + 1) ^ (72 * (s + t)) ∧
        Nonempty (EqualityEncoding p s t)) ↔
      selectorEqualityCount p s t ≤
        (4 * p + 1) ^ (72 * (s + t)) *
          (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) := by
  constructor
  · intro h
    exact (equality_encoding_nonempty_iff_card_bound p s t).mp h.2
  · intro h
    exact ⟨contracted_core_code_card_bound p s t,
      (equality_encoding_nonempty_iff_card_bound p s t).mpr h⟩

end Problem56
