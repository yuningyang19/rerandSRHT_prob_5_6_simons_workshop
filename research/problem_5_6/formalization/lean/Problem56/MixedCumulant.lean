import Problem56.ProductCumulant
import Problem56.ProjectionMean

/-!
Finite combinatorics for the independent-families mixed-cumulant identity in
I10.
-/

open scoped BigOperators

namespace Problem56

private theorem finpartition_eq_indiscrete_of_two_parts_joined
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a b : κ) (hab : a ≠ b)
    (huniv : (Finset.univ : Finset κ) = {a, b})
    (P : Finpartition (Finset.univ : Finset κ))
    (hpart : P.part a = P.part b) :
    P = Finpartition.indiscrete Finset.univ_nonempty.ne_empty := by
  classical
  apply finpartition_eq_indiscrete_of_card_parts_eq_one
    Finset.univ_nonempty.ne_empty
  apply Finset.card_eq_one.mpr
  refine ⟨Finset.univ, ?_⟩
  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
  constructor
  · exact P.parts_nonempty Finset.univ_nonempty.ne_empty
  · intro B hB
    apply Finset.Subset.antisymm (P.subset hB)
    intro y _
    obtain ⟨x, hxB⟩ := P.nonempty_of_mem_parts hB
    have hx : x = a ∨ x = b := by
      have : x ∈ ({a, b} : Finset κ) := by
        rw [← huniv]
        exact Finset.mem_univ x
      simpa [hab] using this
    have hy : y = a ∨ y = b := by
      have : y ∈ ({a, b} : Finset κ) := by
        rw [← huniv]
        exact Finset.mem_univ y
      simpa [hab] using this
    rcases hx with hxa | hxb
    · subst x
      have hBa : P.part a = B := P.part_eq_of_mem hB hxB
      rcases hy with hya | hyb
      · subst y
        exact hxB
      · subst y
        rw [← hBa, hpart]
        exact P.mem_part (Finset.mem_univ b)
    · subst x
      have hBb : P.part b = B := P.part_eq_of_mem hB hxB
      rcases hy with hya | hyb
      · subst y
        rw [← hBb, ← hpart]
        exact P.mem_part (Finset.mem_univ a)
      · subst y
        exact hxB

private theorem finpartition_eq_bot_of_two_parts_separated
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a b : κ) (hab : a ≠ b)
    (huniv : (Finset.univ : Finset κ) = {a, b})
    (P : Finpartition (Finset.univ : Finset κ))
    (hpart : P.part a ≠ P.part b) :
    P = ⊥ := by
  classical
  apply le_antisymm
  · intro B hB
    obtain ⟨x, hxB⟩ := P.nonempty_of_mem_parts hB
    have hx : x = a ∨ x = b := by
      have : x ∈ ({a, b} : Finset κ) := by
        rw [← huniv]
        exact Finset.mem_univ x
      simpa [hab] using this
    rcases hx with hxa | hxb
    · subst x
      refine ⟨{a}, Finpartition.mem_bot_iff.mpr
        ⟨a, Finset.mem_univ a, rfl⟩, ?_⟩
      intro y hyB
      have hy : y = a ∨ y = b := by
        have : y ∈ ({a, b} : Finset κ) := by
          rw [← huniv]
          exact Finset.mem_univ y
        simpa [hab] using this
      rcases hy with hya | hyb
      · subst y
        exact Finset.mem_singleton_self a
      · subst y
        exfalso
        apply hpart
        exact (P.part_eq_of_mem hB hxB).trans
          (P.part_eq_of_mem hB hyB).symm
    · subst x
      refine ⟨{b}, Finpartition.mem_bot_iff.mpr
        ⟨b, Finset.mem_univ b, rfl⟩, ?_⟩
      intro y hyB
      have hy : y = a ∨ y = b := by
        have : y ∈ ({a, b} : Finset κ) := by
          rw [← huniv]
          exact Finset.mem_univ y
        simpa [hab] using this
      rcases hy with hya | hyb
      · subst y
        exfalso
        apply hpart
        exact (P.part_eq_of_mem hB hyB).trans
          (P.part_eq_of_mem hB hxB).symm
      · subst y
        exact Finset.mem_singleton_self b
  · exact bot_le

private theorem all_finpartitions_of_pair
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a b : κ) (hab : a ≠ b)
    (huniv : (Finset.univ : Finset κ) = {a, b}) :
    (Finset.univ : Finset
      (Finpartition (Finset.univ : Finset κ))) =
      {Finpartition.indiscrete Finset.univ_nonempty.ne_empty, ⊥} := by
  classical
  ext P
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_iff]
  by_cases hpart : P.part a = P.part b
  · exact Or.inl
      (finpartition_eq_indiscrete_of_two_parts_joined
        a b hab huniv P hpart)
  · exact Or.inr
      (finpartition_eq_bot_of_two_parts_separated
        a b hab huniv P hpart)

private theorem indiscrete_ne_bot_of_pair
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a b : κ) (hab : a ≠ b) :
    Finpartition.indiscrete
      (Finset.univ_nonempty.ne_empty : (Finset.univ : Finset κ) ≠ ∅) ≠
      (⊥ : Finpartition (Finset.univ : Finset κ)) := by
  intro h
  have hbtop : b ∈ (Finpartition.indiscrete
      (Finset.univ_nonempty.ne_empty : (Finset.univ : Finset κ) ≠ ∅)).part a := by
    have hparts := Finpartition.indiscrete_parts
      (Finset.univ_nonempty.ne_empty : (Finset.univ : Finset κ) ≠ ∅)
    have hunivmem : (Finset.univ : Finset κ) ∈
        (Finpartition.indiscrete
          (Finset.univ_nonempty.ne_empty : (Finset.univ : Finset κ) ≠ ∅)).parts := by
      rw [hparts]
      exact Finset.mem_singleton_self _
    have hpartuniv := (Finpartition.indiscrete
      (Finset.univ_nonempty.ne_empty : (Finset.univ : Finset κ) ≠ ∅)).part_eq_of_mem
        hunivmem (Finset.mem_univ a)
    rw [hpartuniv]
    exact Finset.mem_univ b
  have hbbot : b ∈ (⊥ : Finpartition (Finset.univ : Finset κ)).part a := by
    rw [← h]
    exact hbtop
  have hpartsEq := ((⊥ : Finpartition
    (Finset.univ : Finset κ)).part_eq_of_mem
      (Finpartition.mem_bot_iff.mpr ⟨a, Finset.mem_univ a, rfl⟩)
      (Finset.mem_singleton_self a))
  rw [hpartsEq] at hbbot
  exact hab (Finset.mem_singleton.mp hbbot).symm

private theorem uniformExpectation_fst
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] (F : Ω₁ → ℝ) :
    uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1) =
      uniformExpectation F := by
  calc
    _ = uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1 * (1 : ℝ)) := by
      apply congrArg uniformExpectation
      funext z
      rw [mul_one]
    _ = uniformExpectation F * uniformExpectation (fun _ : Ω₂ ↦ (1 : ℝ)) :=
      uniformExpectation_prod_factor F (fun _ : Ω₂ ↦ (1 : ℝ))
    _ = _ := by rw [uniformExpectation_one_of_nonempty, mul_one]

private theorem uniformExpectation_snd
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] (G : Ω₂ → ℝ) :
    uniformExpectation (fun z : Ω₁ × Ω₂ ↦ G z.2) =
      uniformExpectation G := by
  calc
    _ = uniformExpectation (fun z : Ω₁ × Ω₂ ↦ (1 : ℝ) * G z.2) := by
      apply congrArg uniformExpectation
      funext z
      rw [one_mul]
    _ = uniformExpectation (fun _ : Ω₁ ↦ (1 : ℝ)) * uniformExpectation G :=
      uniformExpectation_prod_factor (fun _ : Ω₁ ↦ (1 : ℝ)) G
    _ = _ := by rw [uniformExpectation_one_of_nonempty, one_mul]

private theorem jointCumulantOn_two_coordinate_factors_zero
    {Ω₁ Ω₂ κ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a b : κ) (hab : a ≠ b)
    (huniv : (Finset.univ : Finset κ) = {a, b})
    (F : Ω₁ → ℝ) (G : Ω₂ → ℝ) :
    jointCumulantOn (fun k ↦
      if k = a then (fun z : Ω₁ × Ω₂ ↦ G z.2)
      else (fun z : Ω₁ × Ω₂ ↦ F z.1)) = 0 := by
  classical
  let Ptop : Finpartition (Finset.univ : Finset κ) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  let Pbot : Finpartition (Finset.univ : Finset κ) := ⊥
  have hne : Ptop ≠ Pbot := indiscrete_ne_bot_of_pair a b hab
  have htopParts : Ptop.parts = {Finset.univ} :=
    Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty
  have hbotParts : Pbot.parts = {{a}, {b}} := by
    rw [show Pbot.parts = (Finset.univ : Finset κ).map
      (⟨singleton, Finset.singleton_injective⟩ : κ ↪ Finset κ) from rfl]
    rw [huniv]
    simp [hab]
  have htopMoment :
      (∏ C ∈ Ptop.parts,
        uniformExpectation (fun z : Ω₁ × Ω₂ ↦
          ∏ k ∈ C,
            (if k = a then G z.2 else F z.1))) =
        uniformExpectation F * uniformExpectation G := by
    rw [htopParts]
    simp only [Finset.prod_singleton]
    calc
      _ = uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1 * G z.2) := by
        apply congrArg uniformExpectation
        funext z
        rw [huniv]
        simp [hab, hab.symm, mul_comm]
      _ = _ := uniformExpectation_prod_factor F G
  have hbotMoment :
      (∏ C ∈ Pbot.parts,
        uniformExpectation (fun z : Ω₁ × Ω₂ ↦
          ∏ k ∈ C,
            (if k = a then G z.2 else F z.1))) =
        uniformExpectation G * uniformExpectation F := by
    rw [hbotParts]
    simp [hab, hab.symm, uniformExpectation_snd, uniformExpectation_fst]
  rw [jointCumulantOn]
  simp only [ite_apply]
  change (∑ P : Finpartition (Finset.univ : Finset κ),
    ((-1 : ℝ) ^ (P.parts.card - 1) *
      (Nat.factorial (P.parts.card - 1) : ℝ)) *
      ∏ C ∈ P.parts,
        uniformExpectation (fun z : Ω₁ × Ω₂ ↦
          ∏ k ∈ C, (if k = a then G z.2 else F z.1))) = 0
  rw [all_finpartitions_of_pair a b hab huniv]
  rw [Finset.sum_insert (by simpa [Ptop, Pbot] using hne),
    Finset.sum_singleton]
  rw [htopMoment, hbotMoment]
  rw [htopParts, hbotParts]
  norm_num [hab]
  ring

noncomputable def twoFamilyPartition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    Finpartition (Finset.univ : Finset ι) := by
  classical
  exact Finpartition.ofExistsUnique
    {A, B}
    (by
      intro C hC x hxC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · rw [← hcover]
        exact Finset.mem_union_left B hxC
      · rw [← hcover]
        exact Finset.mem_union_right A hxC)
    (by
      intro x _
      have hx : x ∈ A ∨ x ∈ B := by
        rw [← Finset.mem_union, hcover]
        exact Finset.mem_univ x
      rcases hx with hxA | hxB
      · refine ⟨A, ⟨Finset.mem_insert_self A {B}, hxA⟩, ?_⟩
        intro C hC
        have hCAor : C = A ∨ C = B := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hC.1
        rcases hCAor with hCA | hCB
        · exact hCA
        · have hxB' : x ∈ B := hCB ▸ hC.2
          exact False.elim ((Finset.disjoint_left.mp hdisjoint) hxA hxB')
      · refine ⟨B, ⟨Finset.mem_insert.mpr (Or.inr
          (Finset.mem_singleton_self B)), hxB⟩, ?_⟩
        intro C hC
        have hCAor : C = A ∨ C = B := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hC.1
        rcases hCAor with hCA | hCB
        · have hxA' : x ∈ A := hCA ▸ hC.2
          exact False.elim ((Finset.disjoint_left.mp hdisjoint) hxA' hxB)
        · exact hCB)
    (by
      intro hempty
      simp only [Finset.mem_insert, Finset.mem_singleton] at hempty
      rcases hempty with h | h
      · exact hA.ne_empty h.symm
      · exact hB.ne_empty h.symm)

@[simp]
theorem twoFamilyPartition_parts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (twoFamilyPartition A B hcover hdisjoint hA hB).parts = {A, B} :=
  rfl

private theorem twoFamilyPartition_left_ne_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) : A ≠ B := by
  intro hAB
  obtain ⟨x, hxA⟩ := hA
  have hxB : x ∈ B := hAB ▸ hxA
  exact (Finset.disjoint_left.mp hdisjoint) hxA hxB

private theorem jointCumulantOn_twoFamily_blockProducts_zero
    {Ω₁ Ω₂ ι : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂]
    [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω₁ × Ω₂ → ℝ)
    (A B : Finset ι)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hfirst : ∀ j ∈ A, ∀ a b c, Y j (a, c) = Y j (b, c))
    (hsecond : ∀ j ∈ B, ∀ a b c, Y j (c, a) = Y j (c, b))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    jointCumulantOn (fun C : (twoFamilyPartition A B hcover hdisjoint hA hB).parts ↦
      fun z ↦ ∏ j ∈ C.1, Y j z) = 0 := by
  classical
  let τ := twoFamilyPartition A B hcover hdisjoint hA hB
  let left : τ.parts := ⟨A, by simp [τ]⟩
  let right : τ.parts := ⟨B, by simp [τ]⟩
  letI : Nonempty τ.parts := ⟨left⟩
  have hlr : left ≠ right := by
    intro h
    apply twoFamilyPartition_left_ne_right A B hdisjoint hA hB
    exact congrArg Subtype.val h
  have huniv : (Finset.univ : Finset τ.parts) = {left, right} := by
    ext C
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hC : C.1 = A ∨ C.1 = B := by
      simpa only [τ, twoFamilyPartition_parts,
        Finset.mem_insert, Finset.mem_singleton] using C.2
    rcases hC with hC | hC
    · exact Or.inl (Subtype.ext hC)
    · exact Or.inr (Subtype.ext hC)
  let base₁ : Ω₁ := Classical.choice (inferInstance : Nonempty Ω₁)
  let base₂ : Ω₂ := Classical.choice (inferInstance : Nonempty Ω₂)
  let F : Ω₁ → ℝ := fun a ↦ ∏ j ∈ B, Y j (a, base₂)
  let G : Ω₂ → ℝ := fun c ↦ ∏ j ∈ A, Y j (base₁, c)
  have hfunctions :
      (fun C : τ.parts ↦ fun z ↦ ∏ j ∈ C.1, Y j z) =
        (fun C ↦ if C = left
          then (fun z : Ω₁ × Ω₂ ↦ G z.2)
          else (fun z : Ω₁ × Ω₂ ↦ F z.1)) := by
    funext C z
    by_cases hCleft : C = left
    · subst C
      simp only [if_pos, left, G]
      apply Finset.prod_congr rfl
      intro j hj
      exact hfirst j hj z.1 base₁ z.2
    · have hCright : C = right := by
        have hmem : C ∈ ({left, right} : Finset τ.parts) := by
          rw [← huniv]
          exact Finset.mem_univ C
        rcases Finset.mem_insert.mp hmem with h | h
        · exact False.elim (hCleft h)
        · exact Finset.mem_singleton.mp h
      subst C
      simp only [if_neg hlr.symm, right, F]
      apply Finset.prod_congr rfl
      intro j hj
      exact hsecond j hj z.2 base₂ z.1
  change jointCumulantOn (fun C : τ.parts ↦
    fun z ↦ ∏ j ∈ C.1, Y j z) = 0
  rw [hfunctions]
  exact jointCumulantOn_two_coordinate_factors_zero
    left right hlr huniv F G

/-! ### Reindexing the indiscrete term -/

private noncomputable def mixedFinsetOrderIsoOfEquiv
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro s t
    simp only [Equiv.finsetCongr_apply]
    exact Finset.map_subset_map

@[simp]
private theorem mixedFinsetOrderIsoOfEquiv_apply
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset α) :
    mixedFinsetOrderIsoOfEquiv e s = s.map e.toEmbedding :=
  rfl

private noncomputable def mixedFinpartitionMapEquiv
    {α β : Type*} [Lattice α] [OrderBot α]
    [Lattice β] [OrderBot β]
    (e : α ≃o β) (a : α) :
    Finpartition a ≃ Finpartition (e a) where
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
      refine ⟨e A, ⟨A, hA, rfl⟩, e.symm_apply_apply A⟩
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
      refine ⟨e.symm B, ⟨B, hB, rfl⟩, e.apply_symm_apply B⟩

private noncomputable def mixedFinpartitionCopyEquiv
    {α : Type*} [Lattice α] [OrderBot α] {a b : α} (h : a = b) :
    Finpartition a ≃ Finpartition b where
  toFun P := P.copy h
  invFun Q := Q.copy h.symm
  left_inv P := by subst b; rfl
  right_inv Q := by subst b; rfl

@[simp]
private theorem mixedFinsetOrderIsoOfEquiv_univ
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    mixedFinsetOrderIsoOfEquiv e (Finset.univ : Finset α) = Finset.univ := by
  ext y
  simp

private noncomputable def mixedFinpartitionCongr
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Finpartition (Finset.univ : Finset α) ≃
      Finpartition (Finset.univ : Finset β) :=
  (mixedFinpartitionMapEquiv
      (mixedFinsetOrderIsoOfEquiv e) Finset.univ).trans
    (mixedFinpartitionCopyEquiv
      (mixedFinsetOrderIsoOfEquiv_univ e))

@[simp]
private theorem mixedFinpartitionCongr_parts
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    (mixedFinpartitionCongr e P).parts =
      P.parts.map (mixedFinsetOrderIsoOfEquiv e).toEmbedding :=
  rfl

theorem jointCumulantOn_equiv_index
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (Y : β → Ω → ℝ) :
    jointCumulantOn (fun a ↦ Y (e a)) = jointCumulantOn Y := by
  classical
  rw [jointCumulantOn, jointCumulantOn]
  apply Fintype.sum_equiv (mixedFinpartitionCongr e)
  intro P
  have hcard : (mixedFinpartitionCongr e P).parts.card =
      P.parts.card := by
    rw [mixedFinpartitionCongr_parts, Finset.card_map]
  rw [hcard]
  congr 1
  rw [mixedFinpartitionCongr_parts, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro A _
  apply congrArg uniformExpectation
  funext ω
  change (∏ j ∈ A, Y (e j) ω) =
    ∏ j ∈ A.map e.toEmbedding, Y j ω
  rw [Finset.prod_map]
  rfl

private noncomputable def subtypeUnivEquiv
    {ι : Type*} [Fintype ι] :
    {j : ι // j ∈ (Finset.univ : Finset ι)} ≃ ι where
  toFun j := j.1
  invFun j := ⟨j, Finset.mem_univ j⟩
  left_inv j := Subtype.ext rfl
  right_inv _ := rfl

theorem jointCumulantOn_subtype_univ
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ) :
    jointCumulantOn (fun j : {j // j ∈ (Finset.univ : Finset ι)} ↦ Y j.1) =
      jointCumulantOn Y := by
  exact jointCumulantOn_equiv_index subtypeUnivEquiv Y

/-! ### A connected proper partition contains a smaller mixed block -/

private theorem reflTransGen_preserves_finset
    {ι : Type*} [DecidableEq ι] (A : Finset ι)
    {r : ι → ι → Prop}
    (hstep : ∀ {x y}, x ∈ A → r x y → y ∈ A)
    {x y : ι} (hx : x ∈ A) (hpath : Relation.ReflTransGen r x y) :
    y ∈ A := by
  induction hpath with
  | refl => exact hx
  | tail hpath hxy ih => exact hstep ih hxy

private theorem connected_partition_has_mixed_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (σ : Finpartition (Finset.univ : Finset ι))
    (hconn : ProductPartitionConnected σ
      (twoFamilyPartition A B hcover hdisjoint hA hB)) :
    ∃ C ∈ σ.parts, (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty := by
  classical
  by_contra hnone
  have hnomix : ∀ C ∈ σ.parts,
      ¬((C ∩ A).Nonempty ∧ (C ∩ B).Nonempty) := by
    intro C hC hmixed
    exact hnone ⟨C, hC, hmixed⟩
  let τ := twoFamilyPartition A B hcover hdisjoint hA hB
  have hApart : A ∈ τ.parts := by simp [τ]
  let a := Classical.choose hA
  have haA : a ∈ A := Classical.choose_spec hA
  let b := Classical.choose hB
  have hbB : b ∈ B := Classical.choose_spec hB
  have hpreserve {x y : ι} (hxA : x ∈ A)
      (hstep : σ.part x = σ.part y ∨ τ.part x = τ.part y) :
      y ∈ A := by
    rcases hstep with hσ | hτ
    · have hσpart : σ.part x ∈ σ.parts :=
        σ.part_mem.mpr (Finset.mem_univ x)
      have hxpart : x ∈ σ.part x := σ.mem_part (Finset.mem_univ x)
      have hypart : y ∈ σ.part x := by
        rw [hσ]
        exact σ.mem_part (Finset.mem_univ y)
      by_contra hyA
      have hyB : y ∈ B := by
        have hyAB : y ∈ A ∨ y ∈ B := by
          rw [← Finset.mem_union, hcover]
          exact Finset.mem_univ y
        exact hyAB.resolve_left hyA
      apply hnomix (σ.part x) hσpart
      exact ⟨⟨x, Finset.mem_inter.mpr ⟨hxpart, hxA⟩⟩,
        ⟨y, Finset.mem_inter.mpr ⟨hypart, hyB⟩⟩⟩
    · have hyPart : y ∈ τ.part y := τ.mem_part (Finset.mem_univ y)
      rw [← hτ] at hyPart
      have hxPartA : τ.part x = A := τ.part_eq_of_mem hApart hxA
      rw [hxPartA] at hyPart
      exact hyPart
  have hpath := hconn a b
  have hbA : b ∈ A :=
    reflTransGen_preserves_finset A hpreserve haA hpath
  exact (Finset.disjoint_left.mp hdisjoint) hbA hbB

private theorem finpartition_eq_indiscrete_of_univ_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (hU : (Finset.univ : Finset ι) ∈ P.parts) :
    P = Finpartition.indiscrete Finset.univ_nonempty.ne_empty := by
  apply finpartition_eq_indiscrete_of_card_parts_eq_one
    Finset.univ_nonempty.ne_empty
  apply Finset.card_eq_one.mpr
  refine ⟨Finset.univ, ?_⟩
  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
  constructor
  · exact P.parts_nonempty Finset.univ_nonempty.ne_empty
  · intro C hC
    obtain ⟨x, hxC⟩ := P.nonempty_of_mem_parts hC
    exact P.eq_of_mem_parts hC hU hxC (Finset.mem_univ x)

/-- Mixed cumulants of two nonempty independent coordinate families vanish.
The index type is arbitrary so the theorem can recurse on a proper partition
block. -/
theorem independent_families_mixed_cumulant_vanish_on
    {Ω₁ Ω₂ ι : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂]
    [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω₁ × Ω₂ → ℝ)
    (A B : Finset ι)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hfirst : ∀ j ∈ A, ∀ a b c, Y j (a, c) = Y j (b, c))
    (hsecond : ∀ j ∈ B, ∀ a b c, Y j (c, a) = Y j (c, b))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    jointCumulantOn Y = 0 := by
  classical
  letI : Nonempty ι := ⟨Classical.choose hA⟩
  let τ := twoFamilyPartition A B hcover hdisjoint hA hB
  let Ptop : Finpartition (Finset.univ : Finset ι) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  have houter : jointCumulantOn (fun C : τ.parts ↦
      fun z ↦ ∏ j ∈ C.1, Y j z) = 0 := by
    exact jointCumulantOn_twoFamily_blockProducts_zero
      Y A B hcover hdisjoint hfirst hsecond hA hB
  have hsum : connectedPartitionCumulantSum Y τ = 0 := by
    calc
      _ = jointCumulantOn (fun C : τ.parts ↦
          fun z ↦ ∏ j ∈ C.1, Y j z) :=
        (product_cumulant_connected_identity Y τ).symm
      _ = 0 := houter
  have htopconn : ProductPartitionConnected Ptop τ := by
    intro i j
    apply Relation.ReflTransGen.single
    left
    have hi : Ptop.part i = Finset.univ := by
      apply Ptop.part_eq_of_mem
        (by simp [Ptop])
      exact Finset.mem_univ i
    have hj : Ptop.part j = Finset.univ := by
      apply Ptop.part_eq_of_mem
        (by simp [Ptop])
      exact Finset.mem_univ j
    exact hi.trans hj.symm
  have hproperzero (σ : Finpartition (Finset.univ : Finset ι))
      (hσtop : σ ≠ Ptop) (hconn : ProductPartitionConnected σ τ) :
      partitionCumulantProduct Y σ = 0 := by
    obtain ⟨C, hC, hCA, hCB⟩ :=
      connected_partition_has_mixed_block
        A B hcover hdisjoint hA hB σ hconn
    have hCne : C ≠ (Finset.univ : Finset ι) := by
      intro hCU
      apply hσtop
      apply finpartition_eq_indiscrete_of_univ_mem σ
      exact hCU ▸ hC
    have hCss : C ⊂ (Finset.univ : Finset ι) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨σ.subset hC, hCne⟩
    have hcardC : Fintype.card C < Fintype.card ι := by
      rw [Fintype.card_coe]
      exact Finset.card_lt_card hCss
    let AC : Finset C := Finset.univ.filter (fun j ↦ j.1 ∈ A)
    let BC : Finset C := Finset.univ.filter (fun j ↦ j.1 ∈ B)
    have hcoverC : AC ∪ BC = Finset.univ := by
      ext j
      simp only [AC, BC, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      have hj : j.1 ∈ (Finset.univ : Finset ι) := Finset.mem_univ j.1
      rw [← hcover] at hj
      exact Finset.mem_union.mp hj
    have hdisjointC : Disjoint AC BC := by
      rw [Finset.disjoint_left]
      intro j hjA hjB
      exact (Finset.disjoint_left.mp hdisjoint)
        (Finset.mem_filter.mp hjA).2 (Finset.mem_filter.mp hjB).2
    have hAC : AC.Nonempty := by
      let x := Classical.choose hCA
      have hx := Classical.choose_spec hCA
      refine ⟨⟨x, (Finset.mem_inter.mp hx).1⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_inter.mp hx).2⟩
    have hBC : BC.Nonempty := by
      let x := Classical.choose hCB
      have hx := Classical.choose_spec hCB
      refine ⟨⟨x, (Finset.mem_inter.mp hx).1⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_inter.mp hx).2⟩
    have hfirstC : ∀ j ∈ AC, ∀ a b c,
        Y j.1 (a, c) = Y j.1 (b, c) := by
      intro j hj
      exact hfirst j.1 (Finset.mem_filter.mp hj).2
    have hsecondC : ∀ j ∈ BC, ∀ a b c,
        Y j.1 (c, a) = Y j.1 (c, b) := by
      intro j hj
      exact hsecond j.1 (Finset.mem_filter.mp hj).2
    have hcumulant : jointCumulantOn (fun j : C ↦ Y j.1) = 0 :=
      independent_families_mixed_cumulant_vanish_on
        (fun j : C ↦ Y j.1) AC BC hcoverC hdisjointC
        hfirstC hsecondC hAC hBC
    rw [partitionCumulantProduct]
    exact Finset.prod_eq_zero hC hcumulant
  rw [connectedPartitionCumulantSum] at hsum
  have hsumSingle :
      (∑ σ : Finpartition (Finset.univ : Finset ι),
        if ProductPartitionConnected σ τ
          then partitionCumulantProduct Y σ else 0) =
        partitionCumulantProduct Y Ptop := by
    rw [Fintype.sum_eq_single Ptop]
    · simp [htopconn]
    · intro σ hσtop
      by_cases hconn : ProductPartitionConnected σ τ
      · simp [hconn, hproperzero σ hσtop hconn]
      · simp [hconn]
  rw [hsumSingle] at hsum
  have htopProduct : partitionCumulantProduct Y Ptop =
      jointCumulantOn Y := by
    rw [partitionCumulantProduct]
    have hparts : Ptop.parts = {Finset.univ} :=
      Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty
    rw [hparts]
    simp only [Finset.prod_singleton]
    exact jointCumulantOn_subtype_univ Y
  rw [htopProduct] at hsum
  exact hsum
termination_by Fintype.card ι
decreasing_by exact hcardC

/-- The exact frozen I10 signature. -/
theorem independent_families_mixed_cumulant_vanish
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂]
    {q : ℕ} (Y : Fin q → Ω₁ × Ω₂ → ℝ)
    (usesFirst usesSecond : Finset (Fin q))
    (hcover : usesFirst ∪ usesSecond = Finset.univ)
    (hdisjoint : Disjoint usesFirst usesSecond)
    (hfirst : ∀ j ∈ usesFirst, ∀ a b c,
      Y j (a, c) = Y j (b, c))
    (hsecond : ∀ j ∈ usesSecond, ∀ a b c,
      Y j (c, a) = Y j (c, b))
    (hnonempty₁ : usesFirst.Nonempty)
    (hnonempty₂ : usesSecond.Nonempty) :
    jointCumulant Y = 0 := by
  exact independent_families_mixed_cumulant_vanish_on
    Y usesFirst usesSecond hcover hdisjoint hfirst hsecond
    hnonempty₁ hnonempty₂

end Problem56
