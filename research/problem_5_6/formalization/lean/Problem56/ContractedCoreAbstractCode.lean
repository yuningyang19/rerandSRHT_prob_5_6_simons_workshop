import Problem56.ContractedCoreCount
import Problem56.ContractedCoreTopology

/-!
# Abstract contracted cores and the fixed 72a-digit payload

This file combines the `9a` degree-profile digits with the `63a` topology
digits and embeds the resulting semantic core into the public
`ContractedCoreCode` type.  The embedding is purely finite and introduces no
decoder assumption.
-/

namespace Problem56

noncomputable section

/-- A fully specified finite contracted core before erasing auxiliary labels
into the fixed public payload. -/
abbrev AbstractContractedCore (p a : ℕ) :=
  Σ c : ContractedCoreDegreeProfile p a, ContractedCoreTopology c

theorem abstractContractedCore_card_le (p a : ℕ) :
    Fintype.card (AbstractContractedCore p a) ≤
      (4 * p + 1) ^ (72 * a) := by
  calc
    Fintype.card (AbstractContractedCore p a) =
        ∑ c : ContractedCoreDegreeProfile p a,
          Fintype.card (ContractedCoreTopology c) := by
      simp only [AbstractContractedCore, Fintype.card_sigma]
    _ ≤ ∑ _c : ContractedCoreDegreeProfile p a,
        (4 * p + 1) ^ (63 * a) := by
      apply Finset.sum_le_sum
      intro c _
      exact contractedCoreTopology_card_le c
    _ = Fintype.card (ContractedCoreDegreeProfile p a) *
        (4 * p + 1) ^ (63 * a) := by simp
    _ ≤ (4 * p + 1) ^ (9 * a) * (4 * p + 1) ^ (63 * a) :=
      Nat.mul_le_mul_right _ (contractedCoreDegreeProfile_card_le p a)
    _ = (4 * p + 1) ^ (72 * a) := by
      rw [← pow_add]
      congr 1
      omega

private noncomputable def abstractCoreFintypeEmbeddingOfCardLE
    {α β : Type*} [Fintype α] [Fintype β]
    (hcard : Fintype.card α ≤ Fintype.card β) : α ↪ β where
  toFun x := (Fintype.equivFin β).symm
    (Fin.castLE hcard (Fintype.equivFin α x))
  inj' := by
    intro x y hxy
    apply (Fintype.equivFin α).injective
    apply Fin.castLE_injective hcard
    exact (Fintype.equivFin β).symm.injective hxy

/-- Erase the semantic core into the exact public `72a`-digit code space. -/
noncomputable def abstractContractedCoreEmbedding (p a : ℕ) :
    AbstractContractedCore p a ↪ ContractedCoreCode p a := by
  apply abstractCoreFintypeEmbeddingOfCardLE
  rw [contracted_core_code_card]
  exact abstractContractedCore_card_le p a

#print axioms abstractContractedCore_card_le
#print axioms abstractContractedCoreEmbedding

end

end Problem56
