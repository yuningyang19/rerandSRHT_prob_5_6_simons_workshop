import Problem56.ContractedCoreCanonicalRealization
import Problem56.ContractedCoreCanonicalCount

/-!
# Exact cardinality of the source-extracted canonical expansion

This module records the total-cardinality calculation used to upgrade the
explicit canonical-to-source port injection to an equivalence.
-/

namespace Problem56

open scoped BigOperators

noncomputable section

/-- The designated positive-link ports are exactly the range of the stored
link-port embedding. -/
noncomputable def contractedCoreLinkPortRangeEquiv
    {p a : ℕ} (C : AbstractContractedCore p a) :
    ContractedCoreLinkPortIndex C.2.links.linkCount.1 ≃
      {z : ContractedCorePort C.1 // C.2.IsLinkPort z} := by
  let E := Equiv.ofInjective C.2.links.linkPorts C.2.links.linkPorts.injective
  exact E.trans (Equiv.subtypeEquiv (Equiv.refl _) (fun z ↦ by
    rfl))

noncomputable instance contractedCoreLinkPortRangeFintype
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype {z : ContractedCorePort C.1 // C.2.IsLinkPort z} :=
  Fintype.ofFinite _

theorem contractedCoreLinkPortRange_card
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype.card {z : ContractedCorePort C.1 // C.2.IsLinkPort z} =
      4 * C.2.links.linkCount.1 := by
  rw [← Fintype.card_congr (contractedCoreLinkPortRangeEquiv C)]
  exact contractedCoreLinkPortIndex_card _

theorem canonicalDirectPort_card
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype.card (CanonicalDirectPort C) =
      Fintype.card (ContractedCorePort C.1) -
        4 * C.2.links.linkCount.1 := by
  classical
  calc
    Fintype.card (CanonicalDirectPort C) =
        Nat.card (CanonicalDirectPort C) := Fintype.card_eq_nat_card
    _ = Nat.card
        {z : ContractedCorePort C.1 // ¬ C.2.IsLinkPort z} := rfl
    _ = Fintype.card
        {z : ContractedCorePort C.1 // ¬ C.2.IsLinkPort z} :=
      Fintype.card_eq_nat_card.symm
    _ =
        Fintype.card (ContractedCorePort C.1) -
          Fintype.card {z : ContractedCorePort C.1 // C.2.IsLinkPort z} :=
      Fintype.card_subtype_compl _
    _ = _ := by rw [contractedCoreLinkPortRange_card]

theorem canonicalLinkSegmentPort_card
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype.card (CanonicalLinkSegmentPort C) =
      4 * (∑ i, (C.2.links.linkLength i).1) +
        4 * C.2.links.linkCount.1 := by
  simp only [CanonicalLinkSegmentPort, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    add_mul, one_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.sum_mul]
  simp [Nat.mul_comm]

/-- In the source-extracted core, the stored link lengths enumerate exactly
the removed vertices component by component. -/
theorem equalityAbstractContractedCore_linkLength_sum
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (∑ i, ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1) =
      Fintype.card (EqualityRemovedVertex Q) := by
  change (∑ i : Fin (Fintype.card
      (equalityRemovedGraph Q).ConnectedComponent),
      Fintype.card ((Fintype.equivFin
        (equalityRemovedGraph Q).ConnectedComponent).symm i)) = _
  rw [← equalityRemovedComponent_sum_card Q]
  exact Equiv.sum_comp
    (Fintype.equivFin (equalityRemovedGraph Q).ConnectedComponent).symm
    (fun c ↦ Fintype.card c)

/-- The numerical retained-port profile has exactly the number of ports of
the retained source vertices. -/
theorem equalityAbstractContractedCore_port_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Fintype.card
        (ContractedCorePort (equalityAbstractContractedCore hp Q ha).1) =
      Fintype.card (EqualityRetainedPorts Q) := by
  exact (Fintype.card_congr
    (equalityRetainedPortsEquivContractedCorePort hp Q ha)).symm

/-- The canonical expansion extracted from a source equality graph has
exactly all `4p` indexed source half-edge ports. -/
theorem equalityCanonicalExpandedPort_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Fintype.card
        (CanonicalExpandedPort (equalityAbstractContractedCore hp Q ha)) =
      Fintype.card (EqualityHalfEdge p) := by
  let C := equalityAbstractContractedCore hp Q ha
  have hlinkRange : 4 * C.2.links.linkCount.1 ≤
      Fintype.card (ContractedCorePort C.1) := by
    rw [← contractedCoreLinkPortIndex_card]
    exact Fintype.card_le_of_injective C.2.links.linkPorts
      C.2.links.linkPorts.injective
  have hlinkRange' : 4 * C.2.links.linkCount.1 ≤
      Fintype.card (EqualityRetainedPorts Q) := by
    rw [← equalityAbstractContractedCore_port_card hp Q ha]
    exact hlinkRange
  have hsource := equalityRetainedPorts_card_add_four_removed hp Q
  rw [equalityHalfEdge_card]
  change Fintype.card (CanonicalDirectPort C ⊕ CanonicalLinkSegmentPort C) = _
  rw [Fintype.card_sum, canonicalDirectPort_card,
    canonicalLinkSegmentPort_card,
    equalityAbstractContractedCore_port_card hp Q ha,
    equalityAbstractContractedCore_linkLength_sum hp Q ha]
  omega

#print axioms equalityCanonicalExpandedPort_card

end

end Problem56
