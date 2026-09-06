import Problem56.ContractedCorePairingCode

/-!
# Padded function payloads for the contracted-core code

These embeddings implement the source's remaining elementary serialization
steps: one optional named mate per retained port and one bounded value per
positive-length contracted link.  Active entries are enumerated canonically;
the remaining fixed-size slots are padding.
-/

namespace Problem56

noncomputable section

/-- Pad a function on an arbitrary finite domain into a fixed prefix. -/
noncomputable def contractedCorePaddedFunctionEmbeddingOfCard
    {α β : Type*} [Fintype α] [DecidableEq α] [Inhabited β]
    (slots : ℕ) (hcard : Fintype.card α ≤ slots) :
    (α → β) ↪ (Fin slots → β) where
  toFun f := fun i ↦
    if hi : i.1 < Fintype.card α then
      f ((Fintype.equivFin α).symm ⟨i.1, hi⟩)
    else default
  inj' := by
    intro f g hfg
    funext x
    let i : Fin slots :=
      ⟨(Fintype.equivFin α x).1,
        lt_of_lt_of_le (Fintype.equivFin α x).2 hcard⟩
    have hi : i.1 < Fintype.card α := (Fintype.equivFin α x).2
    have h := congrFun hfg i
    simpa [i, hi] using h

/-- Serialize an optional named port in each of at most `36*a` active slots.
The reserved zero alphabet symbol means `none`; positive symbols name a port.
-/
noncomputable def contractedCoreOptionalPortMapEmbeddingOfCard
    {α : Type*} [Fintype α] [DecidableEq α]
    (p a : ℕ) (hcardA : Fintype.card α ≤ 36 * a)
    (hcardP : Fintype.card α ≤ 4 * p) :
    (α → Option α) ↪ (Fin (36 * a) → Fin (4 * p + 1)) where
  toFun f := fun i ↦
    if hi : i.1 < Fintype.card α then
      optionFinCoreAlphabetEmbedding p (Fintype.card α) hcardP
        ((Fintype.equivFin α).optionCongr
          (f ((Fintype.equivFin α).symm ⟨i.1, hi⟩)))
    else 0
  inj' := by
    intro f g hfg
    funext x
    let i : Fin (36 * a) :=
      ⟨(Fintype.equivFin α x).1,
        lt_of_lt_of_le (Fintype.equivFin α x).2 hcardA⟩
    have hi : i.1 < Fintype.card α := (Fintype.equivFin α x).2
    have h := congrFun hfg i
    have hoption :
        (Fintype.equivFin α).optionCongr (f x) =
          (Fintype.equivFin α).optionCongr (g x) := by
      apply (optionFinCoreAlphabetEmbedding p (Fintype.card α) hcardP).injective
      simpa [i, hi] using h
    exact (Fintype.equivFin α).optionCongr.injective hoption

#print axioms contractedCorePaddedFunctionEmbeddingOfCard
#print axioms contractedCoreOptionalPortMapEmbeddingOfCard

end

end Problem56
