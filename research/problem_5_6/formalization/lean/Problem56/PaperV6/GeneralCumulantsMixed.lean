import Problem56.PaperV6.GeneralCumulantsProduct
import Problem56.MixedCumulant

/-! General independent-family vanishing, retaining real integrable moments. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

private theorem measure_finpartition_eq_indiscrete_of_two_parts_joined
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

private theorem measure_finpartition_eq_bot_of_two_parts_separated
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

private theorem measure_all_finpartitions_of_pair
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
      (measure_finpartition_eq_indiscrete_of_two_parts_joined
        a b hab huniv P hpart)
  · exact Or.inr
      (measure_finpartition_eq_bot_of_two_parts_separated
        a b hab huniv P hpart)

private theorem measure_indiscrete_ne_bot_of_pair
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

private theorem measure_twoFamilyPartition_left_ne_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) : A ≠ B := by
  intro hAB
  obtain ⟨x, hxA⟩ := hA
  have hxB : x ∈ B := hAB ▸ hxA
  exact (Finset.disjoint_left.mp hdisjoint) hxA hxB

private theorem measure_reflTransGen_preserves_finset
    {ι : Type*} [DecidableEq ι] (A : Finset ι)
    {r : ι → ι → Prop}
    (hstep : ∀ {x y}, x ∈ A → r x y → y ∈ A)
    {x y : ι} (hx : x ∈ A) (hpath : Relation.ReflTransGen r x y) :
    y ∈ A := by
  induction hpath with
  | refl => exact hx
  | tail hpath hxy ih => exact hstep ih hxy

private theorem measure_connected_partition_has_mixed_block
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
    measure_reflTransGen_preserves_finset A hpreserve haA hpath
  exact (Finset.disjoint_left.mp hdisjoint) hbA hbB

private theorem measure_finpartition_eq_indiscrete_of_univ_mem
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

theorem measure_jointCumulant_two_factors_zero
    {Ω κ : Type*} [MeasurableSpace Ω]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a b : κ) (hab : a ≠ b)
    (huniv : (Finset.univ : Finset κ) = {a, b})
    (μ : Measure Ω) (F G : Ω → ℝ)
    (hFG : (∫ ω, F ω * G ω ∂μ) = (∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) :
    measureJointCumulant μ (fun k ↦
      if k = a then (fun z : Ω ↦ G z)
      else (fun z : Ω ↦ F z)) = 0 := by
  classical
  let Ptop : Finpartition (Finset.univ : Finset κ) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  let Pbot : Finpartition (Finset.univ : Finset κ) := ⊥
  have hne : Ptop ≠ Pbot := measure_indiscrete_ne_bot_of_pair a b hab
  have htopParts : Ptop.parts = {Finset.univ} :=
    Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty
  have hbotParts : Pbot.parts = {{a}, {b}} := by
    rw [show Pbot.parts = (Finset.univ : Finset κ).map
      (⟨singleton, Finset.singleton_injective⟩ : κ ↪ Finset κ) from rfl]
    rw [huniv]
    simp [hab]
  have htopMoment :
      (∏ C ∈ Ptop.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun z : Ω ↦
          ∏ k ∈ C,
            (if k = a then G z else F z))) =
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) F * (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) G := by
    rw [htopParts]
    simp only [Finset.prod_singleton]
    calc
      _ = (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun z : Ω ↦ F z * G z) := by
        apply congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ)
        funext z
        rw [huniv]
        simp [hab, hab.symm, mul_comm]
      _ = _ := hFG
  have hbotMoment :
      (∏ C ∈ Pbot.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun z : Ω ↦
          ∏ k ∈ C,
            (if k = a then G z else F z))) =
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) G * (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) F := by
    rw [hbotParts]
    simp [hab, hab.symm]
  rw [measureJointCumulant]
  simp only [ite_apply]
  change (∑ P : Finpartition (Finset.univ : Finset κ),
    ((-1 : ℝ) ^ (P.parts.card - 1) *
      (Nat.factorial (P.parts.card - 1) : ℝ)) *
      ∏ C ∈ P.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun z : Ω ↦
          ∏ k ∈ C, (if k = a then G z else F z))) = 0
  rw [measure_all_finpartitions_of_pair a b hab huniv]
  rw [Finset.sum_insert (by simpa [Ptop, Pbot] using hne),
    Finset.sum_singleton]
  rw [htopMoment, hbotMoment]
  rw [htopParts, hbotParts]
  norm_num [hab]
  ring


theorem measure_jointCumulant_twoFamily_blockProducts_zero
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (A B : Finset ι)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hFG : (∫ ω, (∏ j ∈ B, Y j ω) * (∏ j ∈ A, Y j ω) ∂μ) =
      (∫ ω, (∏ j ∈ B, Y j ω) ∂μ) * ∫ ω, (∏ j ∈ A, Y j ω) ∂μ)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    measureJointCumulant μ (fun C : (twoFamilyPartition A B hcover hdisjoint hA hB).parts ↦
      fun z ↦ ∏ j ∈ C.1, Y j z) = 0 := by
  classical
  let τ := twoFamilyPartition A B hcover hdisjoint hA hB
  let left : τ.parts := ⟨A, by simp [τ]⟩
  let right : τ.parts := ⟨B, by simp [τ]⟩
  letI : Nonempty τ.parts := ⟨left⟩
  have hlr : left ≠ right := by
    intro h
    apply measure_twoFamilyPartition_left_ne_right A B hdisjoint hA hB
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
  let F : Ω → ℝ := fun ω ↦ ∏ j ∈ B, Y j ω
  let G : Ω → ℝ := fun ω ↦ ∏ j ∈ A, Y j ω
  have hfunctions :
      (fun C : τ.parts ↦ fun z ↦ ∏ j ∈ C.1, Y j z) =
        (fun C ↦ if C = left
          then (fun z : Ω ↦ G z)
          else (fun z : Ω ↦ F z)) := by
    funext C z
    by_cases hCleft : C = left
    · subst C
      simp only [if_pos, left, G]
    · have hCright : C = right := by
        have hmem : C ∈ ({left, right} : Finset τ.parts) := by
          rw [← huniv]
          exact Finset.mem_univ C
        rcases Finset.mem_insert.mp hmem with h | h
        · exact False.elim (hCleft h)
        · exact Finset.mem_singleton.mp h
      subst C
      simp only [if_neg hlr.symm, right, F]
  change measureJointCumulant μ (fun C : τ.parts ↦
    fun z ↦ ∏ j ∈ C.1, Y j z) = 0
  rw [hfunctions]
  exact measure_jointCumulant_two_factors_zero
    left right hlr huniv μ F G hFG


theorem finiteJointMoments_subtype
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (C : Finset ι)
    (hY : FiniteJointMoments μ Y) :
    FiniteJointMoments μ (fun j : C ↦ Y j.1) := by
  intro D
  simpa only [Finset.prod_map, Function.Embedding.coeFn_mk] using
    hY (D.map (⟨Subtype.val, Subtype.val_injective⟩ : C ↪ ι))

theorem measure_indep_family_products
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (A B : Finset ι)
    (hIndep : IndepFun (fun ω ↦ fun j : A ↦ Y j.1 ω)
      (fun ω ↦ fun j : B ↦ Y j.1 ω) μ) :
    IndepFun (fun ω ↦ ∏ j ∈ A, Y j ω) (fun ω ↦ ∏ j ∈ B, Y j ω) μ := by
  have hA : Measurable (fun z : A → ℝ ↦ ∏ j, z j) := by fun_prop
  have hB : Measurable (fun z : B → ℝ ↦ ∏ j, z j) := by fun_prop
  have hAe : (fun ω ↦ ∏ j : A, Y j.1 ω) =
      (fun ω ↦ ∏ j ∈ A, Y j ω) := by
    funext ω
    exact Finset.prod_coe_sort A (fun j ↦ Y j ω)
  have hBe : (fun ω ↦ ∏ j : B, Y j.1 ω) =
      (fun ω ↦ ∏ j ∈ B, Y j ω) := by
    funext ω
    exact Finset.prod_coe_sort B (fun j ↦ Y j ω)
  have hh := hIndep.comp hA hB
  change IndepFun (fun ω ↦ ∏ j : A, Y j.1 ω)
    (fun ω ↦ ∏ j : B, Y j.1 ω) μ at hh
  rw [hAe, hBe] at hh
  exact hh

private noncomputable def measure_subtypeUnivEquiv
    {ι : Type*} [Fintype ι] :
    {j : ι // j ∈ (Finset.univ : Finset ι)} ≃ ι where
  toFun j := j.1
  invFun j := ⟨j, Finset.mem_univ j⟩
  left_inv j := Subtype.ext rfl
  right_inv _ := rfl

theorem measure_jointCumulant_subtype_univ
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) :
    measureJointCumulant μ (fun j : {j // j ∈ (Finset.univ : Finset ι)} ↦ Y j.1) =
      measureJointCumulant μ Y := by
  exact measure_jointCumulantOn_equiv measure_subtypeUnivEquiv μ Y


theorem measure_independent_families_mixed_cumulant_vanish
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (hY : FiniteJointMoments μ Y)
    (A B : Finset ι)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hIndep : IndepFun (fun ω ↦ fun j : A ↦ Y j.1 ω)
      (fun ω ↦ fun j : B ↦ Y j.1 ω) μ)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    measureJointCumulant μ Y = 0 := by
  classical
  letI : Nonempty ι := ⟨Classical.choose hA⟩
  let τ := twoFamilyPartition A B hcover hdisjoint hA hB
  let Ptop : Finpartition (Finset.univ : Finset ι) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  have houter : measureJointCumulant μ (fun C : τ.parts ↦
      fun z ↦ ∏ j ∈ C.1, Y j z) = 0 := by
    exact measure_jointCumulant_twoFamily_blockProducts_zero μ
      Y A B hcover hdisjoint
      ((measure_indep_family_products μ Y A B hIndep).symm.integral_fun_mul_eq_mul_integral
        (hY B).aestronglyMeasurable (hY A).aestronglyMeasurable) hA hB
  have hsum : measureConnectedPartitionCumulantSum μ Y τ = 0 := by
    calc
      _ = measureJointCumulant μ (fun C : τ.parts ↦
          fun z ↦ ∏ j ∈ C.1, Y j z) :=
        (measure_product_cumulant_connected_identity_nonempty μ Y τ).symm
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
      measurePartitionCumulantProduct μ Y σ = 0 := by
    obtain ⟨C, hC, hCA, hCB⟩ :=
      measure_connected_partition_has_mixed_block
        A B hcover hdisjoint hA hB σ hconn
    have hCne : C ≠ (Finset.univ : Finset ι) := by
      intro hCU
      apply hσtop
      apply measure_finpartition_eq_indiscrete_of_univ_mem σ
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
    have hIndepC : IndepFun (fun ω ↦ fun j : AC ↦ Y j.1.1 ω)
        (fun ω ↦ fun j : BC ↦ Y j.1.1 ω) μ := by
      let f : (A → ℝ) → AC → ℝ := fun x j ↦
        x ⟨j.1.1, (Finset.mem_filter.mp j.2).2⟩
      let g : (B → ℝ) → BC → ℝ := fun x j ↦
        x ⟨j.1.1, (Finset.mem_filter.mp j.2).2⟩
      have hf : Measurable f := by fun_prop
      have hg : Measurable g := by fun_prop
      exact hIndep.comp hf hg
    have hcumulant : measureJointCumulant μ (fun j : C ↦ Y j.1) = 0 :=
      measure_independent_families_mixed_cumulant_vanish μ
        (fun j : C ↦ Y j.1) (finiteJointMoments_subtype μ Y C hY)
        AC BC hcoverC hdisjointC hIndepC hAC hBC
    rw [measurePartitionCumulantProduct]
    exact Finset.prod_eq_zero hC hcumulant
  rw [measureConnectedPartitionCumulantSum] at hsum
  have hsumSingle :
      (∑ σ : Finpartition (Finset.univ : Finset ι),
        if ProductPartitionConnected σ τ
          then measurePartitionCumulantProduct μ Y σ else 0) =
        measurePartitionCumulantProduct μ Y Ptop := by
    rw [Fintype.sum_eq_single Ptop]
    · simp [htopconn]
    · intro σ hσtop
      by_cases hconn : ProductPartitionConnected σ τ
      · simp [hconn, hproperzero σ hσtop hconn]
      · simp [hconn]
  rw [hsumSingle] at hsum
  have htopProduct : measurePartitionCumulantProduct μ Y Ptop =
      measureJointCumulant μ Y := by
    rw [measurePartitionCumulantProduct]
    have hparts : Ptop.parts = {Finset.univ} :=
      Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty
    rw [hparts]
    simp only [Finset.prod_singleton]
    exact measure_jointCumulant_subtype_univ μ Y
  rw [htopProduct] at hsum
  exact hsum
termination_by Fintype.card ι
decreasing_by exact hcardC


theorem generalMixedIndependence : GeneralMixedIndependenceExpected := by
  intro Ω ι _ _ _ μ _ Y hY A B hA hB hdisjoint hcover hIndep
  exact measure_independent_families_mixed_cumulant_vanish μ Y hY A B
    hcover hdisjoint hIndep hA hB

end Problem56.PaperV6
