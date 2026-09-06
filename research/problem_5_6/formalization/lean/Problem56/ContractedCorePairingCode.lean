import Problem56.Definitions

/-!
# Pairing payload for the contracted-core code

The retained core has at most `36*a` distinguished half-edge ports.  A
pairing is serialized by listing, in increasing order of the lower endpoint
of each pair, the corresponding upper endpoint.  Only one alphabet symbol is
therefore needed per pair, giving exactly the `18*a` slots used by
`ContractedCoreCode.halfEdgePairing`.
-/

namespace Problem56

noncomputable section

private theorem corePairing_existsUnique_mate {α : Type*} [DecidableEq α]
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

private def corePairingMate {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) : α :=
  Finset.choose (fun y ↦ y ≠ x) (P.1.part x)
    (corePairing_existsUnique_mate P x hx)

private theorem corePairingMate_mem {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    corePairingMate P x hx ∈ P.1.part x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (corePairing_existsUnique_mate P x hx)).1

private theorem corePairingMate_ne {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    corePairingMate P x hx ≠ x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (corePairing_existsUnique_mate P x hx)).2

private theorem corePairingMate_mem_support {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    corePairingMate P x hx ∈ S :=
  P.1.part_subset x (corePairingMate_mem P x hx)

private theorem corePairingMate_involutive {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    corePairingMate P (corePairingMate P x hx)
      (corePairingMate_mem_support P x hx) = x := by
  let y := corePairingMate P x hx
  have hyPart : y ∈ P.1.part x := corePairingMate_mem P x hx
  have hyS : y ∈ S := corePairingMate_mem_support P x hx
  have hpart : P.1.part y = P.1.part x :=
    P.1.part_eq_of_mem (P.1.part_mem.2 hx) hyPart
  apply (corePairing_existsUnique_mate P y hyS).unique
  · exact Finset.choose_spec (fun z ↦ z ≠ y) (P.1.part y)
      (corePairing_existsUnique_mate P y hyS)
  · constructor
    · rw [hpart]
      exact P.1.mem_part hx
    · exact (corePairingMate_ne P x hx).symm

private theorem corePairing_part_eq_pair {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    P.1.part x = {x, corePairingMate P x hx} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact P.1.mem_part hx
    · exact corePairingMate_mem P x hx
  · rw [P.2 _ (P.1.part_mem.2 hx)]
    simp [(corePairingMate_ne P x hx).symm]

private def coreFullPairingMate {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell)))
    (x : Fin ell) : Fin ell :=
  corePairingMate P x (Finset.mem_univ x)

private theorem coreFullPairingMate_ne {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) :
    coreFullPairingMate P x ≠ x :=
  corePairingMate_ne P x (Finset.mem_univ x)

private theorem coreFullPairingMate_involutive {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) :
    coreFullPairingMate P (coreFullPairingMate P x) = x := by
  unfold coreFullPairingMate
  exact corePairingMate_involutive P x (Finset.mem_univ x)

private theorem coreFullPairingMate_injective {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) :
    Function.Injective (coreFullPairingMate P) := by
  intro x y hxy
  have h := congrArg (coreFullPairingMate P) hxy
  simpa [coreFullPairingMate_involutive] using h

private def corePairingLowerSet {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) : Finset (Fin ell) :=
  Finset.univ.filter fun x ↦ x < coreFullPairingMate P x

private theorem corePairingLowerSet_mate_not_mem {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) {x : Fin ell}
    (hx : x ∈ corePairingLowerSet P) :
    coreFullPairingMate P x ∉ corePairingLowerSet P := by
  simp only [corePairingLowerSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx ⊢
  rw [coreFullPairingMate_involutive]
  exact not_lt_of_ge hx.le

private theorem corePairingLowerSet_mate_mem_of_not_mem {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) {x : Fin ell}
    (hx : x ∉ corePairingLowerSet P) :
    coreFullPairingMate P x ∈ corePairingLowerSet P := by
  rw [corePairingLowerSet, Finset.mem_filter] at hx ⊢
  simp only [Finset.mem_univ, true_and] at hx ⊢
  rw [coreFullPairingMate_involutive]
  exact lt_of_le_of_ne (le_of_not_gt hx) (coreFullPairingMate_ne P x)

private theorem corePairingLowerSet_card_le {p a ell : ℕ}
    (hellA : ell ≤ 36 * a)
    (P : Pairing (Finset.univ : Finset (Fin ell))) :
    (corePairingLowerSet P).card ≤ 18 * a := by
  classical
  let upper := (corePairingLowerSet P).image (coreFullPairingMate P)
  have hcardUpper : upper.card = (corePairingLowerSet P).card :=
    Finset.card_image_of_injective _ (coreFullPairingMate_injective P)
  have hdisjoint : Disjoint (corePairingLowerSet P) upper := by
    rw [Finset.disjoint_left]
    intro x hx hxu
    rw [Finset.mem_image] at hxu
    obtain ⟨y, hy, rfl⟩ := hxu
    exact corePairingLowerSet_mate_not_mem P hy hx
  have hunion : (corePairingLowerSet P ∪ upper).card ≤ ell := by
    calc
      _ ≤ (Finset.univ : Finset (Fin ell)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = ell := by simp
  rw [Finset.card_union_of_disjoint hdisjoint, hcardUpper] at hunion
  omega

private def corePairingLowerCode (p a ell : ℕ)
    (P : Pairing (Finset.univ : Finset (Fin ell))) :
    Fin (18 * a) → Option (Fin ell) := fun i ↦
  if hi : i.1 < (corePairingLowerSet P).card then
    let j : Fin (corePairingLowerSet P).card := ⟨i.1, hi⟩
    let x : Fin ell := (corePairingLowerSet P).orderEmbOfFin rfl j
    some (coreFullPairingMate P x)
  else
    none

private theorem corePairingLowerCode_complement_support
    (p a ell : ℕ) (hellA : ell ≤ 36 * a)
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) :
    x ∉ corePairingLowerSet P ↔
      ∃ i, corePairingLowerCode p a ell P i = some x := by
  constructor
  · intro hx
    let y := coreFullPairingMate P x
    have hy : y ∈ corePairingLowerSet P :=
      corePairingLowerSet_mate_mem_of_not_mem P hx
    let j : Fin (corePairingLowerSet P).card :=
      ((corePairingLowerSet P).orderIsoOfFin rfl).symm ⟨y, hy⟩
    have hj : j.1 < 18 * a :=
      lt_of_lt_of_le j.2 (corePairingLowerSet_card_le (p := p) hellA P)
    let i : Fin (18 * a) := ⟨j.1, hj⟩
    refine ⟨i, ?_⟩
    have henum : (corePairingLowerSet P).orderEmbOfFin rfl j = y :=
      congrArg Subtype.val
        (((corePairingLowerSet P).orderIsoOfFin rfl).apply_symm_apply ⟨y, hy⟩)
    simp [corePairingLowerCode, i, j, henum, y,
      coreFullPairingMate_involutive]
  · rintro ⟨i, hi⟩
    simp only [corePairingLowerCode] at hi
    split at hi
    · let j : Fin (corePairingLowerSet P).card :=
        ⟨i.1, ‹i.1 < (corePairingLowerSet P).card›⟩
      let y : Fin ell := (corePairingLowerSet P).orderEmbOfFin rfl j
      have hy : y ∈ corePairingLowerSet P :=
        (corePairingLowerSet P).orderEmbOfFin_mem rfl j
      have hnot : coreFullPairingMate P y ∉ corePairingLowerSet P :=
        corePairingLowerSet_mate_not_mem P hy
      have heq : coreFullPairingMate P y = x := Option.some.inj hi
      rwa [heq] at hnot
    · simp at hi

private theorem corePairingLowerCode_injective
    (p a ell : ℕ) (hellA : ell ≤ 36 * a) :
    Function.Injective
      (corePairingLowerCode p a ell :
        Pairing (Finset.univ : Finset (Fin ell)) →
          Fin (18 * a) → Option (Fin ell)) := by
  intro P R hcode
  have hlower : corePairingLowerSet P = corePairingLowerSet R := by
    ext x
    constructor
    · intro hxP
      by_contra hxR
      obtain ⟨i, hi⟩ :=
        (corePairingLowerCode_complement_support p a ell hellA R x).mp hxR
      have hiP : corePairingLowerCode p a ell P i = some x := by
        rw [hcode]
        exact hi
      exact ((corePairingLowerCode_complement_support p a ell hellA P x).mpr
        ⟨i, hiP⟩) hxP
    · intro hxR
      by_contra hxP
      obtain ⟨i, hi⟩ :=
        (corePairingLowerCode_complement_support p a ell hellA P x).mp hxP
      have hiR : corePairingLowerCode p a ell R i = some x := by
        rw [← hcode]
        exact hi
      exact ((corePairingLowerCode_complement_support p a ell hellA R x).mpr
        ⟨i, hiR⟩) hxR
  have hmateLower : ∀ x : Fin ell, x ∈ corePairingLowerSet P →
      coreFullPairingMate P x = coreFullPairingMate R x := by
    intro x hx
    have hxR : x ∈ corePairingLowerSet R := by rw [← hlower]; exact hx
    let j : Fin (corePairingLowerSet P).card :=
      ((corePairingLowerSet P).orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hj : j.1 < 18 * a :=
      lt_of_lt_of_le j.2 (corePairingLowerSet_card_le (p := p) hellA P)
    let i : Fin (18 * a) := ⟨j.1, hj⟩
    have henumP : (corePairingLowerSet P).orderEmbOfFin rfl j = x :=
      congrArg Subtype.val
        (((corePairingLowerSet P).orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    have hi : i.1 < (corePairingLowerSet P).card := j.2
    have hiR : i.1 < (corePairingLowerSet R).card := by
      rw [← hlower]
      exact hi
    have henumR :
        (corePairingLowerSet R).orderEmbOfFin rfl
          (⟨i.1, hiR⟩ : Fin (corePairingLowerSet R).card) = x := by
      simpa [Finset.orderEmbOfFin_apply, hlower, i] using henumP
    have hc := congrFun hcode i
    simpa [corePairingLowerCode, i, j, hi, hiR, henumP, henumR] using hc
  have hmate : ∀ x : Fin ell,
      coreFullPairingMate P x = coreFullPairingMate R x := by
    intro x
    by_cases hx : x ∈ corePairingLowerSet P
    · exact hmateLower x hx
    · let y := coreFullPairingMate P x
      have hy : y ∈ corePairingLowerSet P :=
        corePairingLowerSet_mate_mem_of_not_mem P hx
      have hyMate : coreFullPairingMate R y = x := by
        rw [← hmateLower y hy]
        exact coreFullPairingMate_involutive P x
      calc
        coreFullPairingMate P x = y := rfl
        _ = coreFullPairingMate R (coreFullPairingMate R y) :=
          (coreFullPairingMate_involutive R y).symm
        _ = coreFullPairingMate R x := congrArg (coreFullPairingMate R) hyMate
  have hPR : P.1 = R.1 := by
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      obtain ⟨x, hx⟩ := P.1.nonempty_of_mem_parts hB
      have hPx : P.1.part x = B := P.1.part_eq_of_mem hB hx
      rw [← hPx, corePairing_part_eq_pair P x (Finset.mem_univ x)]
      change {x, coreFullPairingMate P x} ∈ R.1.parts
      rw [hmate x]
      have hpartR : R.1.part x = {x, coreFullPairingMate R x} := by
        simpa [coreFullPairingMate] using
          corePairing_part_eq_pair R x (Finset.mem_univ x)
      rw [← hpartR]
      exact R.1.part_mem.2 (Finset.mem_univ x)
    · intro hB
      obtain ⟨x, hx⟩ := R.1.nonempty_of_mem_parts hB
      have hRx : R.1.part x = B := R.1.part_eq_of_mem hB hx
      rw [← hRx, corePairing_part_eq_pair R x (Finset.mem_univ x)]
      change {x, coreFullPairingMate R x} ∈ P.1.parts
      rw [← hmate x]
      have hpartP : P.1.part x = {x, coreFullPairingMate P x} := by
        simpa [coreFullPairingMate] using
          corePairing_part_eq_pair P x (Finset.mem_univ x)
      rw [← hpartP]
      exact P.1.part_mem.2 (Finset.mem_univ x)
  exact Subtype.ext hPR

def optionFinCoreAlphabetEmbedding (p ell : ℕ)
    (hellP : ell ≤ 4 * p) : Option (Fin ell) ↪ Fin (4 * p + 1) where
  toFun
    | none => ⟨0, by omega⟩
    | some j => ⟨j.1 + 1, by omega⟩
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            have hv := congrArg Fin.val hxy
            simp at hv
    | some i =>
        cases y with
        | none =>
            have hv := congrArg Fin.val hxy
            simp at hv
        | some j =>
            apply congrArg some
            apply Fin.ext
            have hv := congrArg Fin.val hxy
            simpa using hv

private noncomputable def corePairingFinsetOrderIsoOfEquiv
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro S T
    simp only [Equiv.finsetCongr_apply]
    exact Finset.map_subset_map

private noncomputable def corePairingFinpartitionMapEquiv
    {α β : Type*} [Lattice α] [OrderBot α]
    [Lattice β] [OrderBot β]
    (e : α ≃o β) (a : α) : Finpartition a ≃ Finpartition (e a) where
  toFun P := P.map e
  invFun Q := (Q.map e.symm).copy (e.symm_apply_apply a)
  left_inv P := by
    apply Finpartition.ext
    simp only [Finpartition.copy_parts, Finpartition.parts_map]
    ext A
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
      have hCA : C = A := by
        rw [← hBA, ← hCB]
        exact (e.symm_apply_apply C).symm
      exact hCA ▸ hC
    · intro hA
      exact ⟨e A, ⟨A, hA, rfl⟩, e.symm_apply_apply A⟩
  right_inv Q := by
    apply Finpartition.ext
    simp only [Finpartition.parts_map, Finpartition.copy_parts]
    ext B
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨A, ⟨C, hC, hCA⟩, hAB⟩
      have hCB : C = B := by
        rw [← hAB, ← hCA]
        exact (e.apply_symm_apply C).symm
      exact hCB ▸ hC
    · intro hB
      exact ⟨e.symm B, ⟨B, hB, rfl⟩, e.apply_symm_apply B⟩

private noncomputable def corePairingFinpartitionCopyEquiv
    {α : Type*} [Lattice α] [OrderBot α] {a b : α} (h : a = b) :
    Finpartition a ≃ Finpartition b where
  toFun P := P.copy h
  invFun Q := Q.copy h.symm
  left_inv P := by subst b; rfl
  right_inv Q := by subst b; rfl

@[simp] private theorem corePairingFinsetOrderIsoOfEquiv_univ
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    corePairingFinsetOrderIsoOfEquiv e (Finset.univ : Finset α) =
      Finset.univ := by
  ext y
  simp [corePairingFinsetOrderIsoOfEquiv]

private noncomputable def corePairingFinpartitionCongr
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Finpartition (Finset.univ : Finset α) ≃
      Finpartition (Finset.univ : Finset β) :=
  (corePairingFinpartitionMapEquiv
      (corePairingFinsetOrderIsoOfEquiv e) Finset.univ).trans
    (corePairingFinpartitionCopyEquiv
      (corePairingFinsetOrderIsoOfEquiv_univ e))

@[simp] private theorem corePairingFinpartitionCongr_parts
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    (corePairingFinpartitionCongr e P).parts =
      P.parts.map e.finsetCongr.toEmbedding :=
  rfl

private noncomputable def corePairingCongr
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Pairing (Finset.univ : Finset α) ≃
      Pairing (Finset.univ : Finset β) :=
  (corePairingFinpartitionCongr e).subtypeEquiv fun P ↦ by
    constructor
    · intro h B hB
      rw [corePairingFinpartitionCongr_parts] at hB
      obtain ⟨A, hA, hAB⟩ := Finset.mem_map.mp hB
      subst B
      change (A.map e.toEmbedding).card = 2
      rw [Finset.card_map]
      exact h A hA
    · intro h A hA
      have hmap : A.map e.toEmbedding ∈
          (corePairingFinpartitionCongr e P).parts := by
        rw [corePairingFinpartitionCongr_parts]
        exact Finset.mem_map.mpr ⟨A, hA, rfl⟩
      have hc := h (A.map e.toEmbedding) hmap
      simpa using hc

/-- Injectively serialize a pairing of at most `36*a` ports into the
`18*a` pairing digits of a contracted-core code. -/
noncomputable def contractedCorePairingEmbedding
    (p a ell : ℕ) (hellA : ell ≤ 36 * a) (hellP : ell ≤ 4 * p) :
    Pairing (Finset.univ : Finset (Fin ell)) ↪
      (Fin (18 * a) → Fin (4 * p + 1)) where
  toFun P := fun i ↦
    optionFinCoreAlphabetEmbedding p ell hellP
      (corePairingLowerCode p a ell P i)
  inj' := by
    intro P R hcode
    apply corePairingLowerCode_injective p a ell hellA
    funext i
    apply (optionFinCoreAlphabetEmbedding p ell hellP).injective
    exact congrFun hcode i

/-- Type-generic form used for the dependent sigma type of retained ports. -/
noncomputable def contractedCorePairingEmbeddingOfCard
    {α : Type*} [Fintype α] [DecidableEq α]
    (p a : ℕ) (hcardA : Fintype.card α ≤ 36 * a)
    (hcardP : Fintype.card α ≤ 4 * p) :
    Pairing (Finset.univ : Finset α) ↪
      (Fin (18 * a) → Fin (4 * p + 1)) :=
  (corePairingCongr (Fintype.equivFin α)).toEmbedding.trans
    (contractedCorePairingEmbedding p a (Fintype.card α) hcardA hcardP)

#print axioms contractedCorePairingEmbedding
#print axioms contractedCorePairingEmbeddingOfCard

end

end Problem56
