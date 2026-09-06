import Problem56.ContractedCoreCanonical

/-!
# Source realization of the canonical contracted core

This file proves that the semantic core extracted from a positive-parameter
equality partition satisfies the link/pairing compatibility required by the
common canonical expansion.
-/

namespace Problem56

noncomputable section

/-- The actual retained port represented by one source link coordinate, before
transport to the numerical profile-port type. -/
noncomputable def equalitySourceLinkBoundaryPort
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (w : ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) :
    EqualityRemovedBoundaryRetainedPort Q :=
  equalityAllComponentBoundaryPortsEquivRemovedBoundary Q
    ((equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha).symm
      (equalityRemovedComponentPortsEquivLinkPortIndex Q w))

noncomputable def equalitySourceLinkRetainedPort
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (w : ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) :
    EqualityRetainedPorts Q :=
  (equalitySourceLinkBoundaryPort hp Q ha w).1

/-- Contracting a source link pairs its two boundary incidences while keeping
the indexed parallel-copy coordinate fixed. -/
theorem equalityContractedRetainedPortOpposite_sourceLink
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (w : ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) :
    equalityContractedRetainedPortOpposite hp Q ha
        (equalitySourceLinkRetainedPort hp Q ha w) =
      equalitySourceLinkRetainedPort hp Q ha
        ⟨w.1, Fin.rev w.2.1, w.2.2⟩ := by
  classical
  let wr : ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) :=
    ⟨w.1, Fin.rev w.2.1, w.2.2⟩
  let b := equalitySourceLinkBoundaryPort hp Q ha w
  let br := equalitySourceLinkBoundaryPort hp Q ha wr
  let S := equalityRetainedPortSplitEquiv Q
  let E := equalityRemovedBoundaryPortEquivComponentFinPairs hp Q ha
  have hcoord :
      equalityRemovedComponentPortsEquivLinkPortIndex Q wr =
        ⟨(equalityRemovedComponentPortsEquivLinkPortIndex Q w).1,
          Fin.rev
            (equalityRemovedComponentPortsEquivLinkPortIndex Q w).2.1,
          (equalityRemovedComponentPortsEquivLinkPortIndex Q w).2.2⟩ := by
    rfl
  have hEb : E b = equalityRemovedComponentPortsEquivLinkPortIndex Q w := by
    simp [E, b, equalitySourceLinkBoundaryPort,
      equalityRemovedBoundaryPortEquivComponentFinPairs]
  have hEbr : E br = equalityRemovedComponentPortsEquivLinkPortIndex Q wr := by
    simp [E, br, equalitySourceLinkBoundaryPort,
      equalityRemovedBoundaryPortEquivComponentFinPairs]
  have hop :
      equalityRemovedBoundaryPortContractedOpposite hp Q ha b = br := by
    apply E.injective
    rw [hEbr, hcoord]
    simp [equalityRemovedBoundaryPortContractedOpposite, E, hEb]
  have hSb : S b.1 = Sum.inr b := by
    simpa [S, equalityRetainedPortSplitEquiv] using
      (Equiv.sumCompl_symm_apply_neg b)
  have hSbr : S br.1 = Sum.inr br := by
    simpa [S, equalityRetainedPortSplitEquiv] using
      (Equiv.sumCompl_symm_apply_neg br)
  change equalityContractedRetainedPortOpposite hp Q ha b.1 = br.1
  apply S.injective
  simp only [equalityContractedRetainedPortOpposite, S,
    Function.comp_apply, Equiv.apply_symm_apply]
  rw [hSb, hSbr]
  change Sum.inr
      (equalityRemovedBoundaryPortContractedOpposite hp Q ha b) = Sum.inr br
  rw [hop]

/-- The numerical retained-port transport preserves the preceding source-link
mate identity. -/
theorem equalityStandardContractedPortOpposite_linkPort
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (w : ContractedCoreLinkPortIndex
      (equalityContractedCoreLinkData hp Q ha).linkCount.1) :
    equalityStandardContractedPortOpposite hp Q ha
        ((equalityContractedCoreLinkData hp Q ha).linkPorts w) =
      (equalityContractedCoreLinkData hp Q ha).linkPorts
        ⟨w.1, Fin.rev w.2.1, w.2.2⟩ := by
  classical
  change ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) at w
  change equalityStandardContractedPortOpposite hp Q ha
      ((equalityRetainedPortsEquivContractedCorePort hp Q ha)
        (equalitySourceLinkRetainedPort hp Q ha w)) = _
  simp only [equalityStandardContractedPortOpposite, Function.comp_apply,
    Equiv.symm_apply_apply]
  rw [equalityContractedRetainedPortOpposite_sourceLink]
  rfl

/-- Every positive-parameter source core is a compatible canonical core. -/
theorem equalityAbstractContractedCore_compatible
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    CanonicalCoreCompatible (equalityAbstractContractedCore hp Q ha) := by
  constructor
  intro w
  change ContractedCoreLinkPortIndex
      (equalityContractedCoreLinkData hp Q ha).linkCount.1 at w
  change pairingMate
      (equalityStandardContractedPortPairing hp Q ha)
      ((equalityContractedCoreLinkData hp Q ha).linkPorts w) (by simp) = _
  change pairingMate
      (pairingOfFixedPointFreeInvolution
        (equalityStandardContractedPortOpposite hp Q ha)
        (fun z ↦ equalityStandardContractedPortOpposite_involutive hp Q ha z)
        (fun z ↦ equalityStandardContractedPortOpposite_ne hp Q ha z))
      ((equalityContractedCoreLinkData hp Q ha).linkPorts w) (by simp) = _
  calc
    pairingMate
        (pairingOfFixedPointFreeInvolution
          (equalityStandardContractedPortOpposite hp Q ha)
          (fun z ↦ equalityStandardContractedPortOpposite_involutive hp Q ha z)
          (fun z ↦ equalityStandardContractedPortOpposite_ne hp Q ha z))
        ((equalityContractedCoreLinkData hp Q ha).linkPorts w) (by simp) =
      equalityStandardContractedPortOpposite hp Q ha
        ((equalityContractedCoreLinkData hp Q ha).linkPorts w) :=
      pairingMate_pairingOfFixedPointFreeInvolution _ _ _ _
    _ = _ := equalityStandardContractedPortOpposite_linkPort hp Q ha w

#print axioms equalityContractedRetainedPortOpposite_sourceLink
#print axioms equalityStandardContractedPortOpposite_linkPort
#print axioms equalityAbstractContractedCore_compatible

end

end Problem56
