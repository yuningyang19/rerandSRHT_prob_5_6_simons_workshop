import Problem56.Definitions

/-!
The characteristic-two cancellation used to classify the pair blocks that can
survive pointwise Walsh-label averaging.
-/

namespace Problem56

theorem walsh_label_vanishing_pair_classification_of_injective
    {α : Type*} [DecidableEq α] (m : ℕ)
    (label : α → WalshIndex m) (hinj : Function.Injective label) :
    ∀ u₁ v₁ u₂ v₂ : α,
      label u₁ + label v₁ + label u₂ + label v₂ = 0 →
      (u₁ = v₁ ∧ u₂ = v₂) ∨
      ((u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂)) ∨
      (u₁ ≠ v₁ ∧ u₂ ≠ v₂ ∧
        Disjoint ({u₁, v₁} : Finset α) ({u₂, v₂} : Finset α)) := by
  classical
  intro u₁ v₁ u₂ v₂ hzero
  have remaining_of_first : ∀ {a b c d : α},
      a = c → label a + label b + label c + label d = 0 → b = d := by
    intro a b c d hac hz
    subst c
    have hreorder :
        label a + label b + label a + label d =
          (label a + label a) + (label b + label d) := by
      abel
    rw [hreorder, ZModModule.add_self, zero_add] at hz
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hz
    exact hinj hz
  have remaining_of_outer : ∀ {a b c d : α},
      a = d → label a + label b + label c + label d = 0 → b = c := by
    intro a b c d had hz
    subst d
    have hreorder :
        label a + label b + label c + label a =
          (label a + label a) + (label b + label c) := by
      abel
    rw [hreorder, ZModModule.add_self, zero_add] at hz
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hz
    exact hinj hz
  by_cases hloop₁ : u₁ = v₁
  · left
    refine ⟨hloop₁, ?_⟩
    subst v₁
    have hreorder :
        label u₁ + label u₁ + label u₂ + label v₂ =
          (label u₁ + label u₁) + (label u₂ + label v₂) := by
      abel
    rw [hreorder, ZModModule.add_self, zero_add] at hzero
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hzero
    exact hinj hzero
  · by_cases hloop₂ : u₂ = v₂
    · exfalso
      subst v₂
      have hreorder :
          label u₁ + label v₁ + label u₂ + label u₂ =
            (label u₂ + label u₂) + (label u₁ + label v₁) := by
        abel
      rw [hreorder, ZModModule.add_self, zero_add] at hzero
      rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hzero
      exact hloop₁ (hinj hzero)
    · by_cases hsame : u₁ = u₂
      · right
        left
        left
        exact ⟨hsame, remaining_of_first hsame hzero⟩
      · by_cases hreverse : u₁ = v₂
        · right
          left
          right
          exact ⟨hreverse, remaining_of_outer hreverse hzero⟩
        · right
          right
          refine ⟨hloop₁, hloop₂, Finset.disjoint_left.2 ?_⟩
          intro x hx₁ hx₂
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
          rcases hx₁ with hx₁ | hx₁
          · rcases hx₂ with hx | hx
            · exact hsame (hx₁.symm.trans hx)
            · exact hreverse (hx₁.symm.trans hx)
          · rcases hx₂ with hx | hx
            · have hz' :
                  label v₁ + label u₁ + label u₂ + label v₂ = 0 := by
                calc
                  _ = label u₁ + label v₁ + label u₂ + label v₂ := by abel
                  _ = 0 := hzero
              exact hreverse
                (remaining_of_first (hx₁.symm.trans hx) hz')
            · have hz' :
                  label v₁ + label u₁ + label v₂ + label u₂ = 0 := by
                calc
                  _ = label u₁ + label v₁ + label u₂ + label v₂ := by abel
                  _ = 0 := hzero
              exact hsame
                (remaining_of_first (hx₁.symm.trans hx) hz')

theorem walsh_label_vanishing_pair_classification
    (m v : ℕ) (label : Fin v → WalshIndex m) (hinj : Function.Injective label) :
    ∀ u₁ v₁ u₂ v₂ : Fin v,
      label u₁ + label v₁ + label u₂ + label v₂ = 0 →
      (u₁ = v₁ ∧ u₂ = v₂) ∨
      ((u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂)) ∨
      (u₁ ≠ v₁ ∧ u₂ ≠ v₂ ∧
        Disjoint ({u₁, v₁} : Finset (Fin v)) ({u₂, v₂} : Finset (Fin v))) :=
  walsh_label_vanishing_pair_classification_of_injective m label hinj

theorem pointwise_vanishing_pair_blocks_admissible
    (m : ℕ) :
    ∀ (p s t : ℕ) (D : EntryCumulantPartitionData p s t)
      (lab : EqualityVertex D.selector.1 → WalshIndex m), Function.Injective lab →
      (∀ B ∈ D.entry.parts, B.card = 2 →
        (∑ e ∈ B,
          (lab (equalityVertexAt D.selector.1 e) +
            lab (equalityVertexAt D.selector.1 (cyclicSucc e)))) = 0) →
      AdmissibleEntryPairBlocks D := by
  classical
  intro p s t D lab hlab hvan B hB hcard e he f hf hef
  have hpair : ({e, f} : Finset (Fin (2 * p))) = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact he
      · exact hf
    · rw [hcard]
      simp [hef]
  have hsum := hvan B hB hcard
  rw [← hpair] at hsum
  rw [Finset.sum_pair hef] at hsum
  dsimp only
  rcases walsh_label_vanishing_pair_classification_of_injective m lab hlab
      (equalityVertexAt D.selector.1 e)
      (equalityVertexAt D.selector.1 (cyclicSucc e))
      (equalityVertexAt D.selector.1 f)
      (equalityVertexAt D.selector.1 (cyclicSucc f))
      (by simpa only [add_assoc] using hsum) with hloop | hmatch | hdisjoint
  · exact Or.inl hloop
  · by_cases hne : equalityVertexAt D.selector.1 e =
        equalityVertexAt D.selector.1 (cyclicSucc e)
    · left
      refine ⟨hne, ?_⟩
      rcases hmatch with hsame | hreverse
      · exact hsame.1 ▸ hsame.2 ▸ hne
      · exact hreverse.2.symm.trans (hne.symm.trans hreverse.1)
    · right
      left
      refine ⟨hne, ?_, hmatch⟩
      intro hfloop
      rcases hmatch with hsame | hreverse
      · exact hne (hsame.1.trans (hfloop.trans hsame.2.symm))
      · exact hne (hreverse.1.trans (hfloop.symm.trans hreverse.2.symm))
  · exact Or.inr (Or.inr hdisjoint)

#print axioms walsh_label_vanishing_pair_classification
#print axioms pointwise_vanishing_pair_blocks_admissible

end Problem56
