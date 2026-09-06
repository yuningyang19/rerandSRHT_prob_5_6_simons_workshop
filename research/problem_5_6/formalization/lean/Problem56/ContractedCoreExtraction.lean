import Problem56.ContractedCoreAbstractCode

/-!
# Extracting the counted contracted core

The preceding files prove that maximal removed components are positive doubled
links with exactly four retained boundary ports.  Here those source objects are
transported to the numerical retained-port labels and packaged as the semantic
core whose fields are counted by `ContractedCoreTopology`.
-/

namespace Problem56

open SimpleGraph

noncomputable section

/-- Enumerate components and their four indexed boundary ports by the exact
domain expected by `ContractedCoreLinkData`. -/
noncomputable def equalityRemovedComponentPortsEquivLinkPortIndex
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    ContractedCoreLinkPortIndex
        (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ≃
      Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2 :=
  (Equiv.prodCongr
      (Fintype.equivFin
        (equalityRemovedGraph Q).ConnectedComponent).symm
      (Equiv.refl (Fin 2 × Fin 2))).trans
    (Equiv.sigmaEquivProd
      (equalityRemovedGraph Q).ConnectedComponent (Fin 2 × Fin 2)).symm

/-- The source maximal removed components, with their four actual retained
ports and positive vertex lengths, form valid counted link data. -/
noncomputable def equalityContractedCoreLinkData
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    ContractedCoreLinkData
      (equalityContractedCoreDegreeProfile hp Q ha) where
  linkCount :=
    ⟨Fintype.card (equalityRemovedGraph Q).ConnectedComponent,
      Nat.lt_succ_of_le
        (equalityRemovedComponent_card_le_nine_parameter hp Q ha)⟩
  linkPorts :=
    (equalityRemovedComponentPortsEquivLinkPortIndex Q).toEmbedding.trans
      ((equalityRemovedComponentFinPortsEmbedding hp Q ha).trans
        (equalityRetainedPortsEquivContractedCorePort hp Q ha).toEmbedding)
  linkLength := fun i ↦
    equalityRemovedComponentLengthCode Q
      ((Fintype.equivFin
        (equalityRemovedGraph Q).ConnectedComponent).symm i)
  linkLength_pos := by
    intro i
    rw [equalityRemovedComponentLengthCode_val]
    let c := (Fintype.equivFin
      (equalityRemovedGraph Q).ConnectedComponent).symm i
    obtain ⟨w, hw⟩ := c.nonempty_supp
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩

/-- The complete semantic contracted topology extracted from an equality-class
graph: contracted port pairing together with all positive doubled links. -/
noncomputable def equalityContractedCoreTopology
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    ContractedCoreTopology
      (equalityContractedCoreDegreeProfile hp Q ha) where
  portPairing := equalityStandardContractedPortPairing hp Q ha
  links := equalityContractedCoreLinkData hp Q ha

/-- Package the extracted profile and topology as one semantic core. -/
noncomputable def equalityAbstractContractedCore
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) : AbstractContractedCore p (s + t) :=
  ⟨equalityContractedCoreDegreeProfile hp Q ha,
    equalityContractedCoreTopology hp Q ha⟩

/-- The positive-parameter source core in the exact public `72(s+t)`-digit
code space.  The Euler transition payload is deliberately kept separate. -/
noncomputable def equalityContractedCoreCode
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) : ContractedCoreCode p (s + t) :=
  abstractContractedCoreEmbedding p (s + t)
    (equalityAbstractContractedCore hp Q ha)

#print axioms equalityRemovedComponentPortsEquivLinkPortIndex
#print axioms equalityContractedCoreLinkData
#print axioms equalityContractedCoreTopology
#print axioms equalityAbstractContractedCore
#print axioms equalityContractedCoreCode

end


end Problem56
