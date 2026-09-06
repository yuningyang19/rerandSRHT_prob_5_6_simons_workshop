import Problem56.Definitions

/-!
Finite combinatorial infrastructure for the moment--cumulant inverse in I08.

The full inverse is a partition-lattice Möbius inversion.  This file records the
exact finite expansion immediately before the reindexing by global refinements,
and closes the empty and singleton endpoint cases.  The `Nonempty Ω` assumption
is used at the empty endpoint: the uniform expectation of the empty product is
one only when the finite sample space is nonempty.
-/

open scoped BigOperators

namespace Problem56

theorem uniformExpectation_one_of_nonempty
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformExpectation (fun _ : Ω ↦ (1 : ℝ)) = 1 := by
  simp [uniformExpectation, Fintype.card_ne_zero]

private theorem finpartition_empty_subsingleton
    {α : Type*} [DecidableEq α] :
    Subsingleton (Finpartition (∅ : Finset α)) := by
  constructor
  intro P Q
  ext
  have hP : P.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr rfl
  have hQ : Q.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr rfl
  rw [hP, hQ]

/-- The exact I08 identity at the empty-index endpoint.  This is the endpoint
that fails for an empty probability space under the repository's normalized
finite-sum definition of `uniformExpectation`. -/
theorem moment_cumulant_inverse_fin_zero
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Y : Fin 0 → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∏ j, Y j ω) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin 0)),
        ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ Y j.1) := by
  classical
  have huniv : (Finset.univ : Finset (Fin 0)) = ∅ := by
    ext i
    exact Fin.elim0 i
  letI : Subsingleton (Finpartition (Finset.univ : Finset (Fin 0))) := by
    rw [huniv]
    exact finpartition_empty_subsingleton
  let P0 : Finpartition (Finset.univ : Finset (Fin 0)) :=
    (Finpartition.empty (Finset (Fin 0))).copy huniv.symm
  rw [Fintype.sum_subsingleton _ P0]
  have hp : P0.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr huniv
  simp [hp, uniformExpectation, Fintype.card_ne_zero]

private theorem finpartition_univ_subsingleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Subsingleton ι] :
    Subsingleton (Finpartition (Finset.univ : Finset ι)) := by
  constructor
  intro P Q
  ext
  have hparts : ∀ R : Finpartition (Finset.univ : Finset ι),
      R.parts = {Finset.univ} := by
    intro R
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    constructor
    · exact R.parts_nonempty Finset.univ_nonempty.ne_empty
    · intro B hB
      apply Finset.Subset.antisymm (R.le hB)
      intro x _
      obtain ⟨y, hy⟩ := R.nonempty_of_mem_parts hB
      simpa only [Subsingleton.elim x y] using hy
  rw [hparts P, hparts Q]

private theorem jointCumulantOn_unique
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Unique ι] (Y : ι → Ω → ℝ) :
    jointCumulantOn Y = uniformExpectation (Y default) := by
  classical
  letI : Subsingleton (Finpartition (Finset.univ : Finset ι)) :=
    finpartition_univ_subsingleton
  have huniv : (Finset.univ : Finset ι) ≠ ∅ :=
    Finset.univ_nonempty.ne_empty
  let P1 : Finpartition (Finset.univ : Finset ι) :=
    Finpartition.indiscrete huniv
  rw [jointCumulantOn, Fintype.sum_subsingleton _ P1]
  have hp : P1.parts = {Finset.univ} :=
    Finpartition.indiscrete_parts huniv
  rw [hp]
  simp only [Finset.card_singleton, Nat.reduceSub, pow_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one, Finset.prod_singleton]
  rw [one_mul]
  apply congrArg uniformExpectation
  funext ω
  rw [Fintype.prod_unique]

/-- The exact I08 identity for one indexed variable. -/
theorem moment_cumulant_inverse_fin_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Y : Fin 1 → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∏ j, Y j ω) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin 1)),
        ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ Y j.1) := by
  classical
  letI : Subsingleton (Finpartition (Finset.univ : Finset (Fin 1))) :=
    finpartition_univ_subsingleton
  have huniv : (Finset.univ : Finset (Fin 1)) ≠ ∅ :=
    Finset.univ_nonempty.ne_empty
  let P1 : Finpartition (Finset.univ : Finset (Fin 1)) :=
    Finpartition.indiscrete huniv
  rw [Fintype.sum_subsingleton _ P1]
  have hp : P1.parts = {Finset.univ} :=
    Finpartition.indiscrete_parts huniv
  rw [hp]
  simp only [Finset.prod_singleton]
  letI : Unique {j : Fin 1 // j ∈ (Finset.univ : Finset (Fin 1))} :=
    { default := ⟨default, Finset.mem_univ _⟩
      uniq := fun x ↦ Subtype.ext (Subsingleton.elim _ _) }
  rw [jointCumulantOn_unique]
  apply congrArg uniformExpectation
  funext ω
  rw [Fintype.prod_unique]
  congr 1

/-- Exact distributive expansion of the product of block cumulants.  Its right
side is the nested-partition expression that must next be reindexed by the
global refinement obtained by binding the inner partitions to `P`. -/
theorem product_jointCumulantOn_expansion
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∏ B : P.parts, jointCumulantOn (fun j : B.1 ↦ Y j.1)) =
      ∑ Q : ∀ B : P.parts,
          Finpartition (Finset.univ : Finset B.1),
        ∏ B : P.parts,
          (((-1 : ℝ) ^ ((Q B).parts.card - 1) *
            (Nat.factorial ((Q B).parts.card - 1) : ℝ)) *
            ∏ C ∈ (Q B).parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j.1 ω)) := by
  simp only [jointCumulantOn]
  rw [Fintype.prod_sum]

/-! ### Nested block partitions and their global refinement -/

/-- Regard a finite subset of a block as a finite subset of the ambient index
type.  Keeping this map explicit makes the later reindexing insensitive to
dependent-subtype coercions. -/
private def blockSubsetEmbedding {ι : Type*} [DecidableEq ι]
    (B : Finset ι) : Finset B ↪ Finset ι :=
  (Finset.mapEmbedding ⟨Subtype.val, Subtype.val_injective⟩).toEmbedding

/-- Lift a partition of the subtype carried by one outer block to a partition
of that block in the ambient finite-set lattice. -/
noncomputable def liftBlockPartition
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (Q : Finpartition (Finset.univ : Finset B)) : Finpartition B := by
  classical
  let e := blockSubsetEmbedding B
  exact Finpartition.ofExistsUnique
    (Q.parts.image e)
    (by
      intro C hC x hx
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property)
    (by
      intro x hx
      let xb : B := ⟨x, hx⟩
      obtain ⟨C, ⟨hC, hxbC⟩, huniq⟩ :=
        Q.existsUnique_mem (Finset.mem_univ xb)
      refine ⟨e C, ⟨Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩, ?_⟩
      · exact Finset.mem_map.mpr ⟨xb, hxbC, rfl⟩
      · intro D hD
        obtain ⟨hDparts, hxD⟩ := hD
        obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hDparts
        have hxbE : xb ∈ E := by
          obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hxD
          have : y = xb := Subtype.ext hyx
          simpa [this] using hy
        exact congrArg e (huniq E ⟨hE, hxbE⟩))
    (by
      intro h
      obtain ⟨C, hC, hCempty⟩ := Finset.mem_image.mp h
      apply Q.ne_empty hC
      apply e.injective
      rw [hCempty]
      simp [e, blockSubsetEmbedding])

@[simp]
theorem liftBlockPartition_parts
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (Q : Finpartition (Finset.univ : Finset B)) :
    (liftBlockPartition B Q).parts =
      Q.parts.image (blockSubsetEmbedding B) :=
  rfl

/-- Pull a partition of an ambient block back to the corresponding subtype.
This is the inverse representation needed to recover nested data from a global
refinement. -/
noncomputable def lowerBlockPartition
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (S : Finpartition B) :
    Finpartition (Finset.univ : Finset B) := by
  classical
  let v : B ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let pull : Finset ι → Finset B :=
    fun C ↦ C.preimage v v.injective.injOn
  exact Finpartition.ofExistsUnique
    (S.parts.image pull)
    (by
      intro C _ x _
      exact Finset.mem_univ x)
    (by
      intro x _
      obtain ⟨C, ⟨hC, hxC⟩, huniq⟩ := S.existsUnique_mem x.property
      refine ⟨pull C, ⟨Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩, ?_⟩
      · exact Finset.mem_preimage.mpr hxC
      · intro D hD
        obtain ⟨hDparts, hxD⟩ := hD
        obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hDparts
        have hxE : x.1 ∈ E := Finset.mem_preimage.mp hxD
        exact congrArg pull (huniq E ⟨hE, hxE⟩))
    (by
      intro h
      obtain ⟨C, hC, hCempty⟩ := Finset.mem_image.mp h
      apply S.ne_empty hC
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hxC
      let xb : B := ⟨x, S.subset hC hxC⟩
      have hxb : xb ∈ pull C := Finset.mem_preimage.mpr hxC
      rw [hCempty] at hxb
      simpa using hxb)

@[simp]
theorem lowerBlockPartition_parts
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (S : Finpartition B) :
    (lowerBlockPartition B S).parts =
      S.parts.image (fun C ↦ C.preimage
        (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι)
        Subtype.val_injective.injOn) :=
  rfl

private theorem blockSubsetEmbedding_preimage_of_subset
    {ι : Type*} [DecidableEq ι] (B C : Finset ι) (hCB : C ⊆ B) :
    blockSubsetEmbedding B
        (C.preimage
          (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι)
          Subtype.val_injective.injOn) = C := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    exact hyx ▸ Finset.mem_preimage.mp hy
  · intro hx
    let xb : B := ⟨x, hCB hx⟩
    exact Finset.mem_map.mpr
      ⟨xb, Finset.mem_preimage.mpr hx, rfl⟩

private theorem preimage_blockSubsetEmbedding
    {ι : Type*} [DecidableEq ι] (B : Finset ι) (C : Finset B) :
    (blockSubsetEmbedding B C).preimage
        (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι)
        Subtype.val_injective.injOn = C := by
  classical
  ext x
  simp [blockSubsetEmbedding]

/-- Pulling back and then lifting a block partition is the identity. -/
theorem liftBlockPartition_lowerBlockPartition
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (S : Finpartition B) :
    liftBlockPartition B (lowerBlockPartition B S) = S := by
  classical
  ext C
  simp only [liftBlockPartition_parts, lowerBlockPartition_parts,
    Finset.mem_image]
  constructor
  · rintro ⟨D, ⟨E, hE, rfl⟩, rfl⟩
    simpa only [blockSubsetEmbedding_preimage_of_subset B E (S.subset hE)] using hE
  · intro hC
    refine ⟨C.preimage
      (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι)
      Subtype.val_injective.injOn, ⟨C, hC, rfl⟩, ?_⟩
    exact blockSubsetEmbedding_preimage_of_subset B C (S.subset hC)

/-- Lifting and then pulling back a subtype partition is the identity. -/
theorem lowerBlockPartition_liftBlockPartition
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (Q : Finpartition (Finset.univ : Finset B)) :
    lowerBlockPartition B (liftBlockPartition B Q) = Q := by
  classical
  ext C
  simp only [lowerBlockPartition_parts, liftBlockPartition_parts,
    Finset.mem_image]
  constructor
  · rintro ⟨D, ⟨E, hE, rfl⟩, rfl⟩
    simpa only [preimage_blockSubsetEmbedding B E] using hE
  · intro hC
    refine ⟨blockSubsetEmbedding B C, ⟨C, hC, rfl⟩, ?_⟩
    exact preimage_blockSubsetEmbedding B C

/-- Inside one outer block, restricting a global refinement retains exactly
the global blocks contained in that outer block. -/
theorem mem_restrict_iff_of_finpartition_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P R : Finpartition (Finset.univ : Finset ι)} (hRP : R ≤ P)
    {B : Finset ι} (hB : B ∈ P.parts) {C : Finset ι} :
    C ∈ (R.restrict (P.le hB)).parts ↔ C ∈ R.parts ∧ C ⊆ B := by
  classical
  change C ∈ (R.parts.image (fun D ↦ D ∩ B)).erase ∅ ↔ _
  constructor
  · intro hC
    have hCne : C ≠ ∅ := (Finset.mem_erase.mp hC).1
    obtain ⟨D, hD, hDC⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hC)
    obtain ⟨E, hE, hDE⟩ := hRP hD
    have hDB : D ⊆ B := by
      obtain ⟨x, hxC⟩ := Finset.nonempty_iff_ne_empty.mpr hCne
      have hxDB : x ∈ D ∩ B := hDC ▸ hxC
      obtain ⟨hxD, hxB⟩ := Finset.mem_inter.mp hxDB
      have hEB : E = B := P.eq_of_mem_parts hE hB (hDE hxD) hxB
      simpa only [hEB] using hDE
    have hDinter : D ∩ B = D := Finset.inter_eq_left.mpr hDB
    have hDC' : D = C := hDinter ▸ hDC
    exact ⟨hDC' ▸ hD, hDC' ▸ hDB⟩
  · rintro ⟨hC, hCB⟩
    apply Finset.mem_erase.mpr
    refine ⟨R.ne_empty hC, Finset.mem_image.mpr ⟨C, hC, ?_⟩⟩
    exact Finset.inter_eq_left.mpr hCB

/-- The global refinement obtained by binding all inner block partitions to
their outer partition. -/
noncomputable def nestedGlobalRefinement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    Finpartition (Finset.univ : Finset ι) :=
  P.bind (fun B hB ↦ liftBlockPartition B (Q ⟨B, hB⟩))

/-- Binding inner partitions really produces a refinement of the outer
partition. -/
theorem nestedGlobalRefinement_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    nestedGlobalRefinement P Q ≤ P := by
  classical
  intro C hC
  obtain ⟨B, hB, hCB⟩ := Finpartition.mem_bind.mp hC
  exact ⟨B, hB, (liftBlockPartition B (Q ⟨B, hB⟩)).le hCB⟩

/-- Recover, from a global refinement of `P`, the inner partition carried by
each block of `P`. -/
noncomputable def nestedPartitionsOfGlobalRefinement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P}) :
    ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1) :=
  fun B ↦ lowerBlockPartition B.1 (R.1.restrict (P.le B.2))

/-- Binding all blockwise restrictions of a global refinement recovers that
global refinement. -/
theorem nestedGlobalRefinement_of_global
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P}) :
    nestedGlobalRefinement P (nestedPartitionsOfGlobalRefinement P R) = R.1 := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨B, hB, hCin⟩ := Finpartition.mem_bind.mp hC
    have hCin' : C ∈ (R.1.restrict (P.le hB)).parts := by
      simpa only [nestedPartitionsOfGlobalRefinement,
        liftBlockPartition_lowerBlockPartition] using hCin
    exact (mem_restrict_iff_of_finpartition_le R.2 hB).mp hCin' |>.1
  · intro hC
    obtain ⟨B, hB, hCB⟩ := R.2 hC
    apply Finpartition.mem_bind.mpr
    refine ⟨B, hB, ?_⟩
    simpa only [nestedPartitionsOfGlobalRefinement,
      liftBlockPartition_lowerBlockPartition] using
        (mem_restrict_iff_of_finpartition_le R.2 hB).mpr ⟨hC, hCB⟩

/-- Restricting the bound global partition to an outer block recovers the
lifted inner partition on that block. -/
theorem restrict_nestedGlobalRefinement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1))
    {B : Finset ι} (hB : B ∈ P.parts) :
    (nestedGlobalRefinement P Q).restrict (P.le hB) =
      liftBlockPartition B (Q ⟨B, hB⟩) := by
  classical
  ext C
  rw [mem_restrict_iff_of_finpartition_le
    (nestedGlobalRefinement_le P Q) hB]
  constructor
  · rintro ⟨hCglobal, hCB⟩
    obtain ⟨D, hD, hCD⟩ := Finpartition.mem_bind.mp hCglobal
    have hCDsub : C ⊆ D :=
      (liftBlockPartition D (Q ⟨D, hD⟩)).subset hCD
    obtain ⟨x, hxC⟩ :=
      (liftBlockPartition D (Q ⟨D, hD⟩)).nonempty_of_mem_parts hCD
    have hDB : D = B := P.eq_of_mem_parts hD hB (hCDsub hxC) (hCB hxC)
    subst D
    simpa only [Subsingleton.elim hD hB] using hCD
  · intro hC
    refine ⟨Finpartition.mem_bind.mpr ⟨B, hB, hC⟩, ?_⟩
    exact (liftBlockPartition B (Q ⟨B, hB⟩)).subset hC

/-- Recovering nested partitions from their bound global refinement is the
identity. -/
theorem nestedPartitionsOfGlobalRefinement_nested
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    nestedPartitionsOfGlobalRefinement P
      ⟨nestedGlobalRefinement P Q, nestedGlobalRefinement_le P Q⟩ = Q := by
  classical
  funext B
  change lowerBlockPartition B.1
      ((nestedGlobalRefinement P Q).restrict (P.le B.2)) = Q B
  rw [restrict_nestedGlobalRefinement P Q B.2]
  exact lowerBlockPartition_liftBlockPartition B.1 (Q B)

/-- Finite equivalence between nested block-partition data and a global
refinement of the outer partition. -/
noncomputable def nestedPartitionsEquivGlobalRefinements
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) ≃
      {R : Finpartition (Finset.univ : Finset ι) // R ≤ P} where
  toFun Q := ⟨nestedGlobalRefinement P Q, nestedGlobalRefinement_le P Q⟩
  invFun := nestedPartitionsOfGlobalRefinement P
  left_inv := nestedPartitionsOfGlobalRefinement_nested P
  right_inv := fun R ↦ Subtype.ext (nestedGlobalRefinement_of_global P R)

/-- Lifting a block partition preserves its number of parts. -/
theorem card_liftBlockPartition_parts
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (Q : Finpartition (Finset.univ : Finset B)) :
    (liftBlockPartition B Q).parts.card = Q.parts.card := by
  classical
  rw [liftBlockPartition_parts, Finset.card_image_of_injective]
  exact (blockSubsetEmbedding B).injective

/-- Pulling a block partition back to the subtype also preserves its number
of parts. -/
theorem card_lowerBlockPartition_parts
    {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (S : Finpartition B) :
    (lowerBlockPartition B S).parts.card = S.parts.card := by
  classical
  rw [lowerBlockPartition_parts, Finset.card_image_iff]
  intro C hC D hD hCD
  have h := congrArg (blockSubsetEmbedding B) hCD
  simpa only [blockSubsetEmbedding_preimage_of_subset B C (S.subset hC),
    blockSubsetEmbedding_preimage_of_subset B D (S.subset hD)] using h

/-- Product form of `Finpartition.bind`: the global product factors into the
products over the inner partitions. -/
theorem prod_bind_finpartition
    {α M : Type*} [Lattice α] [OrderBot α] [IsModularLattice α]
    [DecidableEq α] [CommMonoid M] {a : α}
    (P : Finpartition a) (Q : ∀ B : P.parts, Finpartition B.1)
    (f : α → M) :
    (∏ C ∈ (P.bind (fun B hB ↦ Q ⟨B, hB⟩)).parts, f C) =
      ∏ B : P.parts, ∏ C ∈ (Q B).parts, f C := by
  classical
  rw [Finpartition.bind_parts, Finset.prod_biUnion]
  · rfl
  · rintro ⟨B, hB⟩ - ⟨D, hD⟩ - hBD
    rw [Function.onFun, Finset.disjoint_left]
    intro C hCB hCD
    have hdisj : Disjoint B D := P.disjoint hB hD (by
      intro h
      apply hBD
      exact Subtype.ext h)
    exact (Q ⟨B, hB⟩).ne_bot hCB
      (disjoint_self.mp <| hdisj.mono
        ((Q ⟨B, hB⟩).le hCB)
        ((Q ⟨D, hD⟩).le hCD))

/-- The number of parts of the global refinement is the sum of the numbers of
inner parts. -/
theorem card_nestedGlobalRefinement_parts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    (nestedGlobalRefinement P Q).parts.card =
      ∑ B : P.parts, (Q B).parts.card := by
  classical
  rw [nestedGlobalRefinement, Finpartition.card_bind]
  simp only [card_liftBlockPartition_parts]
  change (∑ B ∈ P.parts.attach, (Q B).parts.card) =
    ∑ B ∈ (Finset.univ : Finset P.parts), (Q B).parts.card
  rw [Finset.univ_eq_attach]

/-- Product of block moments associated with a finite partition. -/
noncomputable def partitionMomentProduct
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ)
    (R : Finpartition (Finset.univ : Finset ι)) : ℝ :=
  ∏ C ∈ R.parts,
    uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω)

/-- Passing a block partition between the subtype and ambient
representations preserves its product of block moments. -/
theorem blockMomentProduct_liftBlockPartition
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (Y : ι → Ω → ℝ) (B : Finset ι)
    (Q : Finpartition (Finset.univ : Finset B)) :
    (∏ C ∈ Q.parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j.1 ω)) =
      ∏ D ∈ (liftBlockPartition B Q).parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ D, Y j ω) := by
  classical
  rw [liftBlockPartition_parts,
    Finset.prod_image (blockSubsetEmbedding B).injective.injOn]
  apply Finset.prod_congr rfl
  intro C _
  apply congrArg uniformExpectation
  funext ω
  change (∏ j ∈ C, Y j.1 ω) =
    ∏ j ∈ C.map (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι), Y j ω
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  rfl

/-- The moment factors in nested data are exactly the moment factors indexed
by the associated global refinement. -/
theorem nested_blockMomentProduct_eq_global
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    (∏ B : P.parts, ∏ C ∈ (Q B).parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j.1 ω)) =
      partitionMomentProduct Y (nestedGlobalRefinement P Q) := by
  classical
  rw [partitionMomentProduct, nestedGlobalRefinement]
  rw [prod_bind_finpartition P
    (fun B : P.parts ↦ liftBlockPartition B.1 (Q B))]
  apply Fintype.prod_congr
  intro B
  exact blockMomentProduct_liftBlockPartition Y B.1 (Q B)

/-- The standard partition-lattice Möbius weight used in the joint-cumulant
definition. -/
noncomputable def finpartitionMobiusWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι)) : ℝ :=
  (-1 : ℝ) ^ (P.parts.card - 1) *
    (Nat.factorial (P.parts.card - 1) : ℝ)

/-- Möbius weight of a refinement interval, expressed blockwise over the
coarser endpoint. -/
noncomputable def refinementMobiusWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P}) : ℝ :=
  ∏ B : P.parts,
    finpartitionMobiusWeight (nestedPartitionsOfGlobalRefinement P R B)

/-- In a refinement interval, the restricted partition over an outer block is
the finset of fine blocks contained in it. -/
theorem restrict_parts_eq_filter_of_finpartition_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P R : Finpartition (Finset.univ : Finset ι)} (hRP : R ≤ P)
    {B : Finset ι} (hB : B ∈ P.parts) :
    (R.restrict (P.le hB)).parts = R.parts.filter (· ⊆ B) := by
  classical
  ext C
  simp only [mem_restrict_iff_of_finpartition_le hRP hB,
    Finset.mem_filter]

/-- Explicit coefficient computation: the interval weight is a product over
outer blocks, and each factor depends only on the number of fine blocks it
contains. -/
theorem refinementMobiusWeight_eq_blockCounts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P}) :
    refinementMobiusWeight P R =
      ∏ B : P.parts,
        ((-1 : ℝ) ^ ((R.1.parts.filter (· ⊆ B.1)).card - 1) *
          (Nat.factorial ((R.1.parts.filter (· ⊆ B.1)).card - 1) : ℝ)) := by
  classical
  rw [refinementMobiusWeight]
  apply Fintype.prod_congr
  intro B
  rw [finpartitionMobiusWeight,
    nestedPartitionsOfGlobalRefinement, card_lowerBlockPartition_parts,
    restrict_parts_eq_filter_of_finpartition_le R.2 B.2]

/-- Under the nested/global equivalence, the interval weight is exactly the
product of the inner Möbius weights. -/
theorem refinementMobiusWeight_nestedGlobalRefinement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    refinementMobiusWeight P
        ⟨nestedGlobalRefinement P Q, nestedGlobalRefinement_le P Q⟩ =
      ∏ B : P.parts, finpartitionMobiusWeight (Q B) := by
  rw [refinementMobiusWeight,
    nestedPartitionsOfGlobalRefinement_nested P Q]

/-- The finite sum over global refinements.  It is packaged as a
noncomputable definition so the decidability of the refinement predicate stays
an implementation detail rather than an extra theorem hypothesis. -/
noncomputable def globalRefinementExpansionSum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) : ℝ := by
  classical
  exact ∑ R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P},
    refinementMobiusWeight P R * partitionMomentProduct Y R.1

/-- Reindex the product of block cumulants by global refinements of the outer
partition.  This is the exact finite reindexing immediately before the
Möbius-interval cancellation. -/
theorem product_jointCumulantOn_expansion_global
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∏ B : P.parts, jointCumulantOn (fun j : B.1 ↦ Y j.1)) =
      globalRefinementExpansionSum Y P := by
  classical
  rw [globalRefinementExpansionSum]
  rw [product_jointCumulantOn_expansion]
  let e := nestedPartitionsEquivGlobalRefinements P
  apply Fintype.sum_equiv e
  intro Q
  change
    (∏ B : P.parts,
      (finpartitionMobiusWeight (Q B) *
        ∏ C ∈ (Q B).parts,
          uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j.1 ω))) = _
  rw [Finset.prod_mul_distrib]
  rw [← refinementMobiusWeight_nestedGlobalRefinement P Q,
    nested_blockMomentProduct_eq_global Y P Q]
  rfl

/-! ### Finite Möbius cancellation by adjoining one point -/

/-- Add one fresh point to a finite partition.  The `none` choice makes the
new point a singleton block; `some B` inserts it into the existing block `B`.
This representation is the finite recurrence behind the Möbius coefficient. -/
noncomputable def finpartitionInsertPoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (choice : Option Q.parts) :
    Finpartition (insert a s) := by
  classical
  cases choice with
  | none =>
      exact Q.extend
        (b := {a}) (c := insert a s)
        (by simp)
        (by
          rw [Finset.disjoint_left]
          intro x hxs hxa
          have hxa' : x = a := by simpa using hxa
          subst x
          exact ha hxs)
        (by
          change s ∪ {a} = insert a s
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton,
            Finset.mem_insert]
          tauto)
  | some B =>
      let rest := Q.avoid B.1
      exact rest.extend
        (b := insert a B.1) (c := insert a s)
        (by simp)
        (by
          rw [Finset.disjoint_left]
          intro x hxrest hxnew
          have hxrest' : x ∈ s ∧ x ∉ B.1 := by simpa [rest] using hxrest
          have hxnew' : x = a ∨ x ∈ B.1 := by simpa using hxnew
          rcases hxnew' with rfl | hxB
          · exact ha hxrest'.1
          · exact hxrest'.2 hxB)
        (by
          change (s \ B.1) ∪ insert a B.1 = insert a s
          ext x
          simp only [Finset.mem_union, Finset.mem_sdiff,
            Finset.mem_insert]
          constructor
          · rintro (⟨hxs, -⟩ | rfl | hxB)
            · exact Or.inr hxs
            · exact Or.inl rfl
            · exact Or.inr (Q.subset B.2 hxB)
          · rintro (rfl | hxs)
            · exact Or.inr (Or.inl rfl)
            · by_cases hxB : x ∈ B.1
              · exact Or.inr (Or.inr hxB)
              · exact Or.inl ⟨hxs, hxB⟩)

private theorem mem_avoid_partition_part_iff
    {α : Type*} [DecidableEq α] {s : Finset α}
    (Q : Finpartition s) {B C : Finset α} (hB : B ∈ Q.parts) :
    C ∈ (Q.avoid B).parts ↔ C ∈ Q.parts ∧ C ≠ B := by
  classical
  constructor
  · intro hC
    obtain ⟨D, hD, hnDB, hdiff⟩ := (Finpartition.mem_avoid Q).mp hC
    have hDB : D ≠ B := by
      intro h
      exact hnDB (h ▸ le_rfl)
    have hdisj : Disjoint D B := Q.disjoint hD hB hDB
    have hdiff' : D \ B = D := Finset.sdiff_eq_self_of_disjoint hdisj
    have hDC : D = C := hdiff' ▸ hdiff
    exact ⟨hDC ▸ hD, hDC ▸ hDB⟩
  · rintro ⟨hC, hCB⟩
    have hdisj : Disjoint C B := Q.disjoint hC hB hCB
    refine (Finpartition.mem_avoid Q).mpr ⟨C, hC, ?_, ?_⟩
    · intro hle
      exact Q.ne_empty hC
        (disjoint_self.mp <| hdisj.mono le_rfl hle)
    · exact Finset.sdiff_eq_self_of_disjoint hdisj

private theorem parts_avoid_partition_part
    {α : Type*} [DecidableEq α] {s : Finset α}
    (Q : Finpartition s) {B : Finset α} (hB : B ∈ Q.parts) :
    (Q.avoid B).parts = Q.parts.erase B := by
  classical
  ext C
  simp only [mem_avoid_partition_part_iff Q hB, Finset.mem_erase]
  tauto

@[simp]
theorem finpartitionInsertPoint_parts_none
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    (finpartitionInsertPoint ha Q none).parts = insert {a} Q.parts := by
  classical
  simp [finpartitionInsertPoint]

@[simp]
theorem finpartitionInsertPoint_parts_some
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (B : Q.parts) :
    (finpartitionInsertPoint ha Q (some B)).parts =
      insert (insert a B.1) (Q.parts.erase B.1) := by
  classical
  simp [finpartitionInsertPoint, parts_avoid_partition_part Q B.2]

@[simp]
theorem finpartitionInsertPoint_part_none
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    (finpartitionInsertPoint ha Q none).part a = {a} := by
  classical
  apply (finpartitionInsertPoint ha Q none).part_eq_of_mem
  · rw [finpartitionInsertPoint_parts_none]
    exact Finset.mem_insert_self _ _
  · simp

@[simp]
theorem finpartitionInsertPoint_part_some
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (B : Q.parts) :
    (finpartitionInsertPoint ha Q (some B)).part a = insert a B.1 := by
  classical
  apply (finpartitionInsertPoint ha Q (some B)).part_eq_of_mem
  · rw [finpartitionInsertPoint_parts_some]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_self _ _

theorem insert_fresh_inter
    {α : Type*} [DecidableEq α] {s B : Finset α} {a : α}
    (ha : a ∉ s) (hBs : B ⊆ s) :
    insert a B ∩ s = B := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hxB, hxs⟩
    · exact False.elim (ha hxs)
    · exact hxB
  · intro hxB
    exact ⟨Or.inr hxB, hBs hxB⟩

/-- Removing the freshly adjoined point recovers the original partition,
regardless of whether it was adjoined as a singleton or inserted in a block. -/
theorem restrict_finpartitionInsertPoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (choice : Option Q.parts) :
    (finpartitionInsertPoint ha Q choice).restrict
        (by exact Finset.subset_insert a s) = Q := by
  classical
  cases choice with
  | none =>
      ext C
      change C ∈ (((insert {a} Q.parts).image (fun D ↦ D ∩ s)).erase ∅) ↔
        C ∈ Q.parts
      constructor
      · intro hC
        obtain ⟨hCne, hCimage⟩ := Finset.mem_erase.mp hC
        obtain ⟨D, hD, hDC⟩ := Finset.mem_image.mp hCimage
        rcases Finset.mem_insert.mp hD with rfl | hD
        · have hempty : ({a} : Finset α) ∩ s = ∅ := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_singleton,
              Finset.notMem_empty, iff_false]
            rintro ⟨rfl, has⟩
            exact ha has
          exact False.elim (hCne (hDC.symm.trans hempty))
        · have hDs : D ∩ s = D := Finset.inter_eq_left.mpr (Q.subset hD)
          exact (hDC.symm.trans hDs) ▸ hD
      · intro hC
        apply Finset.mem_erase.mpr
        refine ⟨Q.ne_empty hC, Finset.mem_image.mpr ⟨C, ?_, ?_⟩⟩
        · exact Finset.mem_insert_of_mem hC
        · exact Finset.inter_eq_left.mpr (Q.subset hC)
  | some B =>
      have hnew : insert a B.1 ∩ s = B.1 :=
        insert_fresh_inter ha (Q.subset B.2)
      ext C
      change C ∈ (((finpartitionInsertPoint ha Q (some B)).parts.image
        (fun D ↦ D ∩ s)).erase ∅) ↔ C ∈ Q.parts
      rw [finpartitionInsertPoint_parts_some]
      constructor
      · intro hC
        obtain ⟨-, hCimage⟩ := Finset.mem_erase.mp hC
        obtain ⟨D, hD, hDC⟩ := Finset.mem_image.mp hCimage
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact (hDC.symm.trans hnew) ▸ B.2
        · have hDparts : D ∈ Q.parts := (Finset.mem_erase.mp hD).2
          have hDs : D ∩ s = D := Finset.inter_eq_left.mpr (Q.subset hDparts)
          exact (hDC.symm.trans hDs) ▸ hDparts
      · intro hC
        apply Finset.mem_erase.mpr
        refine ⟨Q.ne_empty hC, ?_⟩
        by_cases hCB : C = B.1
        · refine Finset.mem_image.mpr ⟨insert a B.1,
            Finset.mem_insert_self _ _, ?_⟩
          simpa only [hnew, hCB]
        · refine Finset.mem_image.mpr ⟨C,
            Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCB, hC⟩), ?_⟩
          exact Finset.inter_eq_left.mpr (Q.subset hC)

/-- Remove a distinguished fresh point.  The dependent optional block records
whether the point was a singleton or belonged to a block meeting `s`. -/
noncomputable def finpartitionErasePoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (P : Finpartition (insert a s)) :
    Σ Q : Finpartition s, Option Q.parts := by
  classical
  let hs : s ⊆ insert a s := Finset.subset_insert a s
  let Q := P.restrict hs
  let A := P.part a
  let D := A ∩ s
  have hA : A ∈ P.parts := P.part_mem.mpr (Finset.mem_insert_self a s)
  by_cases hD : D = ∅
  · exact ⟨Q, none⟩
  · have hDparts : D ∈ Q.parts := by
      change D ∈ (P.parts.image (fun C ↦ C ∩ s)).erase ∅
      exact Finset.mem_erase.mpr
        ⟨hD, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩
    exact ⟨Q, some ⟨D, hDparts⟩⟩

theorem finpartitionErasePoint_fst_insertPoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (choice : Option Q.parts) :
    (finpartitionErasePoint ha (finpartitionInsertPoint ha Q choice)).1 = Q := by
  classical
  rw [finpartitionErasePoint]
  split_ifs <;>
    exact restrict_finpartitionInsertPoint ha Q choice

private theorem option_none_heq_of_finset_eq
    {α : Type*} {S T : Finset α} (hST : S = T) :
    (none : Option S) ≍ (none : Option T) := by
  subst T
  rfl

private theorem option_some_subtype_heq_of_finset_eq
    {α : Type*} {S T : Finset α} (hST : S = T)
    {x : S} {y : T} (hxy : x.1 = y.1) :
    (some x : Option S) ≍ (some y : Option T) := by
  subst T
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Erasing immediately after adjoining a point recovers both the partition
and the dependent optional-block datum. -/
theorem finpartitionErasePoint_insertPoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (data : Σ Q : Finpartition s, Option Q.parts) :
    finpartitionErasePoint ha
      (finpartitionInsertPoint ha data.1 data.2) = data := by
  classical
  rcases data with ⟨Q, choice⟩
  cases choice with
  | none =>
      rw [finpartitionErasePoint]
      have hD : (finpartitionInsertPoint ha Q none).part a ∩ s = ∅ := by
        rw [finpartitionInsertPoint_part_none]
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hxs⟩
        exact ha hxs
      rw [dif_pos hD]
      have hfst := restrict_finpartitionInsertPoint ha Q none
      exact Sigma.ext hfst (option_none_heq_of_finset_eq <|
        congrArg Finpartition.parts hfst)
  | some B =>
      rw [finpartitionErasePoint]
      have hDval : (finpartitionInsertPoint ha Q (some B)).part a ∩ s = B.1 := by
        rw [finpartitionInsertPoint_part_some]
        exact insert_fresh_inter ha (Q.subset B.2)
      have hDne :
          (finpartitionInsertPoint ha Q (some B)).part a ∩ s ≠ ∅ :=
        hDval.trans_ne (Q.ne_empty B.2)
      rw [dif_neg hDne]
      have hfst := restrict_finpartitionInsertPoint ha Q (some B)
      apply Sigma.ext hfst
      apply option_some_subtype_heq_of_finset_eq
        (congrArg Finpartition.parts hfst)
      exact hDval

private theorem insert_part_inter_fresh_eq_part
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (P : Finpartition (insert a s)) :
    insert a (P.part a ∩ s) = P.part a := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with hxa | hx
    · subst x
      exact P.mem_part (Finset.mem_insert_self a s)
    · exact (Finset.mem_inter.mp hx).1
  · intro hx
    rcases Finset.mem_insert.mp (P.part_subset a hx) with rfl | hxs
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hx, hxs⟩)

private theorem partition_part_subset_fresh_base_of_ne
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (P : Finpartition (insert a s)) {C : Finset α}
    (hC : C ∈ P.parts) (hCne : C ≠ P.part a) :
    C ⊆ s := by
  intro x hxC
  rcases Finset.mem_insert.mp (P.subset hC hxC) with hxa | hxs
  · subst x
    exact False.elim (hCne <| P.eq_of_mem_parts hC
      (P.part_mem.mpr (Finset.mem_insert_self a s)) hxC
      (P.mem_part (Finset.mem_insert_self a s)))
  · exact hxs

private theorem restrict_fresh_parts_of_part_inter_eq_empty
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (P : Finpartition (insert a s))
    (hD : P.part a ∩ s = ∅) :
    (P.restrict (Finset.subset_insert a s)).parts =
      P.parts.erase (P.part a) := by
  classical
  ext C
  change C ∈ (P.parts.image (fun E ↦ E ∩ s)).erase ∅ ↔
    C ∈ P.parts.erase (P.part a)
  constructor
  · intro hC
    obtain ⟨hCempty, hCimage⟩ := Finset.mem_erase.mp hC
    obtain ⟨E, hE, hEC⟩ := Finset.mem_image.mp hCimage
    by_cases hEA : E = P.part a
    · subst E
      exact False.elim (hCempty (hEC.symm.trans hD))
    · have hEs : E ⊆ s :=
        partition_part_subset_fresh_base_of_ne ha P hE hEA
      have hEinter : E ∩ s = E := Finset.inter_eq_left.mpr hEs
      have hCE : C = E := hEC.symm.trans hEinter
      exact Finset.mem_erase.mpr ⟨hCE.trans_ne hEA, hCE ▸ hE⟩
  · intro hC
    obtain ⟨hCA, hCparts⟩ := Finset.mem_erase.mp hC
    apply Finset.mem_erase.mpr
    refine ⟨P.ne_empty hCparts, Finset.mem_image.mpr ⟨C, hCparts, ?_⟩⟩
    exact Finset.inter_eq_left.mpr
      (partition_part_subset_fresh_base_of_ne ha P hCparts hCA)

private theorem restrict_fresh_parts_of_part_inter_ne_empty
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (P : Finpartition (insert a s))
    (hD : P.part a ∩ s ≠ ∅) :
    (P.restrict (Finset.subset_insert a s)).parts =
      insert (P.part a ∩ s) (P.parts.erase (P.part a)) := by
  classical
  ext C
  change C ∈ (P.parts.image (fun E ↦ E ∩ s)).erase ∅ ↔
    C ∈ insert (P.part a ∩ s) (P.parts.erase (P.part a))
  constructor
  · intro hC
    obtain ⟨-, hCimage⟩ := Finset.mem_erase.mp hC
    obtain ⟨E, hE, hEC⟩ := Finset.mem_image.mp hCimage
    by_cases hEA : E = P.part a
    · subst E
      exact Finset.mem_insert.mpr (Or.inl hEC.symm)
    · have hEs : E ⊆ s :=
        partition_part_subset_fresh_base_of_ne ha P hE hEA
      have hEinter : E ∩ s = E := Finset.inter_eq_left.mpr hEs
      have hCE : C = E := hEC.symm.trans hEinter
      exact Finset.mem_insert.mpr (Or.inr <|
        Finset.mem_erase.mpr ⟨hCE.trans_ne hEA, hCE ▸ hE⟩)
  · intro hC
    rcases Finset.mem_insert.mp hC with hCD | hC
    · apply Finset.mem_erase.mpr
      refine ⟨hCD.trans_ne hD, Finset.mem_image.mpr
        ⟨P.part a, P.part_mem.mpr (Finset.mem_insert_self a s), ?_⟩⟩
      exact hCD.symm
    · obtain ⟨hCA, hCparts⟩ := Finset.mem_erase.mp hC
      apply Finset.mem_erase.mpr
      refine ⟨P.ne_empty hCparts, Finset.mem_image.mpr ⟨C, hCparts, ?_⟩⟩
      exact Finset.inter_eq_left.mpr
        (partition_part_subset_fresh_base_of_ne ha P hCparts hCA)

/-- Adjoining the point after erasing it reconstructs the original
partition. -/
theorem finpartitionInsertPoint_erasePoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (P : Finpartition (insert a s)) :
    finpartitionInsertPoint ha
      (finpartitionErasePoint ha P).1 (finpartitionErasePoint ha P).2 = P := by
  classical
  by_cases hD : P.part a ∩ s = ∅
  · have hErase : finpartitionErasePoint ha P =
        ⟨P.restrict (Finset.subset_insert a s), none⟩ := by
      rw [finpartitionErasePoint]
      exact dif_pos hD
    rw [hErase]
    ext C
    rw [finpartitionInsertPoint_parts_none,
      restrict_fresh_parts_of_part_inter_eq_empty ha P hD]
    have hA : P.part a = {a} := by
      have hins := insert_part_inter_fresh_eq_part ha P
      simpa only [hD, Finset.insert_empty] using hins.symm
    rw [hA]
    have hAparts : {a} ∈ P.parts := by
      rw [← hA]
      exact P.part_mem.mpr (Finset.mem_insert_self a s)
    constructor
    · intro hC
      rcases Finset.mem_insert.mp hC with hC | hC
      · exact hC ▸ hAparts
      · exact (Finset.mem_erase.mp hC).2
    · intro hC
      by_cases hCa : C = {a}
      · exact Finset.mem_insert.mpr (Or.inl hCa)
      · exact Finset.mem_insert.mpr (Or.inr <|
          Finset.mem_erase.mpr ⟨hCa, hC⟩)
  · have hDparts : P.part a ∩ s ∈
        (P.restrict (Finset.subset_insert a s)).parts := by
      change P.part a ∩ s ∈
        (P.parts.image (fun C ↦ C ∩ s)).erase ∅
      exact Finset.mem_erase.mpr ⟨hD, Finset.mem_image.mpr
        ⟨P.part a, P.part_mem.mpr (Finset.mem_insert_self a s), rfl⟩⟩
    have hErase : finpartitionErasePoint ha P =
        ⟨P.restrict (Finset.subset_insert a s),
          some ⟨P.part a ∩ s, hDparts⟩⟩ := by
      rw [finpartitionErasePoint]
      exact dif_neg hD
    rw [hErase]
    ext C
    rw [finpartitionInsertPoint_parts_some]
    have hAparts : P.part a ∈ P.parts :=
      P.part_mem.mpr (Finset.mem_insert_self a s)
    have hDA : P.part a ∩ s ≠ P.part a := by
      intro hEq
      have haA : a ∈ P.part a :=
        P.mem_part (Finset.mem_insert_self a s)
      have haD : a ∈ P.part a ∩ s := hEq.symm ▸ haA
      exact ha (Finset.mem_inter.mp haD).2
    have hDnot : P.part a ∩ s ∉ P.parts.erase (P.part a) := by
      intro hmem
      obtain ⟨hDA, hDparts⟩ := Finset.mem_erase.mp hmem
      have hdisj : Disjoint (P.part a ∩ s) (P.part a) :=
        P.disjoint hDparts hAparts hDA
      exact hD (disjoint_self.mp <| hdisj.mono le_rfl Finset.inter_subset_left)
    have hQmem : C ∈ (P.restrict (Finset.subset_insert a s)).parts ↔
        C = P.part a ∩ s ∨ C ∈ P.parts.erase (P.part a) := by
      rw [restrict_fresh_parts_of_part_inter_ne_empty ha P hD]
      exact Finset.mem_insert
    have hInsert : insert a (P.part a ∩ s) = P.part a :=
      insert_part_inter_fresh_eq_part ha P
    constructor
    · intro hC
      rcases Finset.mem_insert.mp hC with hC | hC
      · rw [hC, hInsert]
        exact hAparts
      · obtain ⟨hCD, hCQ⟩ := Finset.mem_erase.mp hC
        rcases hQmem.mp hCQ with hCD' | hCP
        · exact False.elim (hCD hCD')
        · exact (Finset.mem_erase.mp hCP).2
    · intro hCP
      by_cases hCA : C = P.part a
      · exact Finset.mem_insert.mpr (Or.inl <| hCA.trans hInsert.symm)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        apply Finset.mem_erase.mpr
        refine ⟨?_, hQmem.mpr (Or.inr <|
          Finset.mem_erase.mpr ⟨hCA, hCP⟩)⟩
        intro hCD
        apply hDnot
        apply Finset.mem_erase.mpr
        rw [hCD] at hCP
        exact ⟨hDA, hCP⟩

/-- Finite partitions after adjoining one fresh point are equivalently a
partition of the old set together with the choice of either a new singleton
or one old block in which to place the point. -/
noncomputable def finpartitionInsertPointEquiv
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) :
    (Σ Q : Finpartition s, Option Q.parts) ≃
      Finpartition (insert a s) where
  toFun data := finpartitionInsertPoint ha data.1 data.2
  invFun := finpartitionErasePoint ha
  left_inv := finpartitionErasePoint_insertPoint ha
  right_inv := finpartitionInsertPoint_erasePoint ha

/-- The block-count Möbius weight, for a partition of an arbitrary finite
set rather than only the universe of a finite type. -/
noncomputable def finpartitionWeight
    {α : Type*} [DecidableEq α] {s : Finset α}
    (P : Finpartition s) : ℝ :=
  (-1 : ℝ) ^ (P.parts.card - 1) *
    (Nat.factorial (P.parts.card - 1) : ℝ)

@[simp]
theorem card_finpartitionInsertPoint_parts_none
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    (finpartitionInsertPoint ha Q none).parts.card = Q.parts.card + 1 := by
  classical
  rw [finpartitionInsertPoint_parts_none,
    Finset.card_insert_of_notMem]
  intro haBlock
  exact ha (Q.subset haBlock (Finset.mem_singleton_self a))

@[simp]
theorem card_finpartitionInsertPoint_parts_some
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (B : Q.parts) :
    (finpartitionInsertPoint ha Q (some B)).parts.card = Q.parts.card := by
  classical
  rw [finpartitionInsertPoint_parts_some,
    Finset.card_insert_of_notMem]
  · rw [Finset.card_erase_of_mem B.2]
    have hpos : 0 < Q.parts.card := Finset.card_pos.mpr ⟨B.1, B.2⟩
    omega
  · intro hnew
    have hnewParts : insert a B.1 ∈ Q.parts :=
      (Finset.mem_erase.mp hnew).2
    exact ha (Q.subset hnewParts (Finset.mem_insert_self a B.1))

@[simp]
theorem finpartitionWeight_insertPoint_none
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    finpartitionWeight (finpartitionInsertPoint ha Q none) =
      (-1 : ℝ) ^ Q.parts.card *
        (Nat.factorial Q.parts.card : ℝ) := by
  rw [finpartitionWeight, card_finpartitionInsertPoint_parts_none]
  simp only [Nat.add_sub_cancel]

@[simp]
theorem finpartitionWeight_insertPoint_some
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (B : Q.parts) :
    finpartitionWeight (finpartitionInsertPoint ha Q (some B)) =
      finpartitionWeight Q := by
  rw [finpartitionWeight, card_finpartitionInsertPoint_parts_some]
  rfl

private theorem mobius_weight_successor_cancellation (n : ℕ) :
    (-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ) +
      ((n + 1 : ℕ) : ℝ) *
        ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ)) = 0 := by
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  ring

/-- For a fixed old partition, the singleton choice and all choices of an old
block have total Möbius weight one only for the empty old partition, and zero
otherwise. -/
theorem sum_finpartitionWeight_insertPoint_choices
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    (∑ choice : Option Q.parts,
        finpartitionWeight (finpartitionInsertPoint ha Q choice)) =
      if Q.parts.card = 0 then 1 else 0 := by
  classical
  rw [Fintype.sum_option, finpartitionWeight_insertPoint_none]
  simp_rw [finpartitionWeight_insertPoint_some]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_coe]
  by_cases hk : Q.parts.card = 0
  · simp only [hk, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, Nat.cast_zero, zero_mul, add_zero, if_pos]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp only [finpartitionWeight]
    rw [hn]
    simp only [Nat.succ_sub_one, Nat.succ_ne_zero, if_false]
    simpa only [Nat.succ_eq_add_one] using
      mobius_weight_successor_cancellation n

/-- Summing the Möbius weights of all partitions after adjoining one point
gives one for a singleton underlying set and zero once the old set is
nonempty. -/
theorem sum_finpartitionWeight_insertPoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) :
    (∑ P : Finpartition (insert a s), finpartitionWeight P) =
      if s = ∅ then 1 else 0 := by
  classical
  have hreindex :
      (∑ P : Finpartition (insert a s), finpartitionWeight P) =
        ∑ Q : Finpartition s, ∑ choice : Option Q.parts,
          finpartitionWeight (finpartitionInsertPoint ha Q choice) := by
    calc
      _ = ∑ data : Σ Q : Finpartition s, Option Q.parts,
          finpartitionWeight
            (finpartitionInsertPoint ha data.1 data.2) :=
        (Fintype.sum_equiv (finpartitionInsertPointEquiv ha)
          (fun data ↦ finpartitionWeight
            (finpartitionInsertPoint ha data.1 data.2))
          finpartitionWeight (fun _ ↦ rfl)).symm
      _ = _ := Fintype.sum_sigma _
  rw [hreindex]
  by_cases hs : s = ∅
  · subst s
    letI : Subsingleton (Finpartition (∅ : Finset α)) :=
      finpartition_empty_subsingleton
    let Q0 : Finpartition (∅ : Finset α) := Finpartition.empty (Finset α)
    rw [Fintype.sum_subsingleton _ Q0]
    rw [sum_finpartitionWeight_insertPoint_choices]
    have hparts : Q0.parts = ∅ :=
      Finpartition.parts_eq_empty_iff.mpr rfl
    simp only [hparts, Finset.card_empty, if_pos]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro Q _
    rw [sum_finpartitionWeight_insertPoint_choices, if_neg]
    intro hcard
    apply hs
    exact Finpartition.parts_eq_empty_iff.mp
      (Finset.card_eq_zero.mp hcard)

/-- Scalar partition-lattice cancellation.  On a nonempty finite type, the
sum of the standard top-interval Möbius weights is one for one point and zero
for more than one point. -/
theorem sum_finpartitionMobiusWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (∑ P : Finpartition (Finset.univ : Finset ι),
        finpartitionMobiusWeight P) =
      if Fintype.card ι = 1 then 1 else 0 := by
  classical
  let a : ι := Classical.choice (inferInstance : Nonempty ι)
  have ha : a ∉ (Finset.univ : Finset ι).erase a :=
    Finset.notMem_erase a _
  have hsum := sum_finpartitionWeight_insertPoint ha
  rw [Finset.insert_erase (Finset.mem_univ a)] at hsum
  have herase : (Finset.univ : Finset ι).erase a = ∅ ↔
      Fintype.card ι = 1 := by
    constructor
    · intro h
      have hc := Finset.card_erase_of_mem (Finset.mem_univ a)
      rw [h, Finset.card_empty, Finset.card_univ] at hc
      have hpos : 0 < Fintype.card ι := Fintype.card_pos
      omega
    · intro h
      apply Finset.card_eq_zero.mp
      rw [Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, h]
  by_cases hc : Fintype.card ι = 1
  · rw [if_pos (herase.mpr hc)] at hsum
    rw [if_pos hc]
    simpa only [finpartitionWeight, finpartitionMobiusWeight] using hsum
  · have he : (Finset.univ : Finset ι).erase a ≠ ∅ :=
      fun h ↦ hc (herase.mp h)
    rw [if_neg he] at hsum
    rw [if_neg hc]
    simpa only [finpartitionWeight, finpartitionMobiusWeight] using hsum

/-! ### Block-product Möbius cancellation -/

/-- Möbius weight attached to one nonempty block of a set partition. -/
noncomputable def partitionBlockMobiusWeight
    {α : Type*} [DecidableEq α] (B : Finset α) : ℝ :=
  (-1 : ℝ) ^ (B.card - 1) *
    (Nat.factorial (B.card - 1) : ℝ)

/-- Product of the one-block Möbius weights over a finite partition. -/
noncomputable def partitionBlockMobiusProduct
    {α : Type*} [DecidableEq α] {s : Finset α}
    (P : Finpartition s) : ℝ :=
  ∏ B ∈ P.parts, partitionBlockMobiusWeight B

@[simp]
theorem partitionBlockMobiusWeight_singleton
    {α : Type*} [DecidableEq α] (a : α) :
    partitionBlockMobiusWeight ({a} : Finset α) = 1 := by
  simp [partitionBlockMobiusWeight]

theorem partitionBlockMobiusWeight_insert
    {α : Type*} [DecidableEq α] {B : Finset α} {a : α}
    (ha : a ∉ B) (hB : B ≠ ∅) :
    partitionBlockMobiusWeight (insert a B) =
      -(B.card : ℝ) * partitionBlockMobiusWeight B := by
  have hpos : 0 < B.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hB)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [partitionBlockMobiusWeight, partitionBlockMobiusWeight,
    Finset.card_insert_of_notMem ha, hn]
  simp only [Nat.add_sub_cancel, Nat.succ_sub_one, pow_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_succ]
  ring

@[simp]
theorem partitionBlockMobiusProduct_insertPoint_none
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    partitionBlockMobiusProduct (finpartitionInsertPoint ha Q none) =
      partitionBlockMobiusProduct Q := by
  classical
  rw [partitionBlockMobiusProduct, finpartitionInsertPoint_parts_none]
  rw [Finset.prod_insert]
  · simp only [partitionBlockMobiusWeight_singleton, one_mul]
    rfl
  · intro haBlock
    exact ha (Q.subset haBlock (Finset.mem_singleton_self a))

@[simp]
theorem partitionBlockMobiusProduct_insertPoint_some
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) (B : Q.parts) :
    partitionBlockMobiusProduct (finpartitionInsertPoint ha Q (some B)) =
      -(B.1.card : ℝ) * partitionBlockMobiusProduct Q := by
  classical
  have haB : a ∉ B.1 := fun haB ↦ ha (Q.subset B.2 haB)
  have hnew : insert a B.1 ∉ Q.parts.erase B.1 := by
    intro h
    have hpart : insert a B.1 ∈ Q.parts := (Finset.mem_erase.mp h).2
    exact ha (Q.subset hpart (Finset.mem_insert_self a B.1))
  rw [partitionBlockMobiusProduct, finpartitionInsertPoint_parts_some,
    Finset.prod_insert hnew,
    partitionBlockMobiusWeight_insert haB (Q.ne_empty B.2)]
  change (-(B.1.card : ℝ) * partitionBlockMobiusWeight B.1) *
      (∏ C ∈ Q.parts.erase B.1, partitionBlockMobiusWeight C) =
    -(B.1.card : ℝ) *
      (∏ C ∈ Q.parts, partitionBlockMobiusWeight C)
  rw [mul_assoc]
  rw [Finset.mul_prod_erase Q.parts partitionBlockMobiusWeight B.2]

/-- The fresh-point choices satisfy the block-product recurrence.  The
singleton choice contributes the old product; inserting the point in block
`B` contributes `-#B` times that product. -/
theorem sum_partitionBlockMobiusProduct_insertPoint_choices
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (Q : Finpartition s) :
    (∑ choice : Option Q.parts,
        partitionBlockMobiusProduct
          (finpartitionInsertPoint ha Q choice)) =
      (1 - (s.card : ℝ)) * partitionBlockMobiusProduct Q := by
  classical
  rw [Fintype.sum_option,
    partitionBlockMobiusProduct_insertPoint_none]
  simp_rw [partitionBlockMobiusProduct_insertPoint_some]
  change partitionBlockMobiusProduct Q +
      (∑ B : Q.parts,
        -(B.1.card : ℝ) * partitionBlockMobiusProduct Q) = _
  have hattach :
      (∑ B : Q.parts,
          -(B.1.card : ℝ) * partitionBlockMobiusProduct Q) =
        ∑ B ∈ Q.parts,
          -(B.card : ℝ) * partitionBlockMobiusProduct Q := by
    change (∑ B ∈ Q.parts.attach,
        -(B.1.card : ℝ) * partitionBlockMobiusProduct Q) = _
    exact Finset.sum_attach Q.parts
      (fun B ↦ -(B.card : ℝ) * partitionBlockMobiusProduct Q)
  rw [hattach]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  have hcard : (∑ B ∈ Q.parts, (B.card : ℝ)) = (s.card : ℝ) := by
    exact_mod_cast Q.sum_card_parts
  rw [hcard]
  ring

/-- Recurrence for the total block-product Möbius weight after adjoining one
fresh point. -/
theorem sum_partitionBlockMobiusProduct_insertPoint
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) :
    (∑ P : Finpartition (insert a s), partitionBlockMobiusProduct P) =
      (1 - (s.card : ℝ)) *
        ∑ Q : Finpartition s, partitionBlockMobiusProduct Q := by
  classical
  calc
    _ = ∑ data : Σ Q : Finpartition s, Option Q.parts,
        partitionBlockMobiusProduct
          (finpartitionInsertPoint ha data.1 data.2) :=
      (Fintype.sum_equiv (finpartitionInsertPointEquiv ha)
        (fun data ↦ partitionBlockMobiusProduct
          (finpartitionInsertPoint ha data.1 data.2))
        partitionBlockMobiusProduct (fun _ ↦ rfl)).symm
    _ = ∑ Q : Finpartition s, ∑ choice : Option Q.parts,
        partitionBlockMobiusProduct
          (finpartitionInsertPoint ha Q choice) := Fintype.sum_sigma _
    _ = ∑ Q : Finpartition s,
        (1 - (s.card : ℝ)) * partitionBlockMobiusProduct Q := by
      apply Finset.sum_congr rfl
      intro Q _
      exact sum_partitionBlockMobiusProduct_insertPoint_choices ha Q
    _ = _ := by rw [Finset.mul_sum]

private theorem sum_partitionBlockMobiusProduct_empty
    {α : Type*} [DecidableEq α] :
    (∑ P : Finpartition (∅ : Finset α), partitionBlockMobiusProduct P) = 1 := by
  classical
  letI : Subsingleton (Finpartition (∅ : Finset α)) :=
    finpartition_empty_subsingleton
  let P0 : Finpartition (∅ : Finset α) := Finpartition.empty (Finset α)
  rw [Fintype.sum_subsingleton _ P0]
  have hparts : P0.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr rfl
  simp [partitionBlockMobiusProduct, hparts]

/-- Total block-product cancellation on an arbitrary finite set. -/
theorem sum_partitionBlockMobiusProduct
    {α : Type*} [DecidableEq α] (s : Finset α) :
    (∑ P : Finpartition s, partitionBlockMobiusProduct P) =
      if s.card ≤ 1 then 1 else 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [sum_partitionBlockMobiusProduct_empty]
      simp
  | @insert a s ha ih =>
      rw [sum_partitionBlockMobiusProduct_insertPoint ha, ih,
        Finset.card_insert_of_notMem ha]
      by_cases hk0 : s.card = 0
      · simp [hk0]
      · by_cases hk1 : s.card = 1
        · simp [hk1]
        · have hkgt : 1 < s.card := by omega
          simp [show ¬s.card ≤ 1 by omega,
            show ¬(s.card + 1 ≤ 1) by omega]

/-- For a nonempty finite type, the total block-product weight singles out
the one-element case. -/
theorem sum_partitionBlockMobiusProduct_univ
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (∑ P : Finpartition (Finset.univ : Finset ι),
        partitionBlockMobiusProduct P) =
      if Fintype.card ι = 1 then 1 else 0 := by
  rw [sum_partitionBlockMobiusProduct, Finset.card_univ]
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  by_cases h : Fintype.card ι = 1
  · simp [h]
  · have hgt : 1 < Fintype.card ι := by omega
    simp [h, show ¬Fintype.card ι ≤ 1 by omega]

/-! ### Coarsenings as partitions of the fine blocks -/

/-- Union, in the ambient type, of a finite collection of blocks of `R`. -/
noncomputable def unionPartitionBlocks
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (G : Finset R.parts) : Finset α :=
  G.biUnion (fun B ↦ B.1)

@[simp]
theorem mem_unionPartitionBlocks
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (G : Finset R.parts) (x : α) :
    x ∈ unionPartitionBlocks R G ↔ ∃ B ∈ G, x ∈ B.1 := by
  simp [unionPartitionBlocks]

theorem unionPartitionBlocks_subset
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (G : Finset R.parts) :
    unionPartitionBlocks R G ⊆ s := by
  intro x hx
  obtain ⟨B, -, hxB⟩ := (mem_unionPartitionBlocks R G x).mp hx
  exact R.subset B.2 hxB

/-- A fine block is contained in the union of a collection of fine blocks
exactly when it belongs to that collection. -/
theorem block_subset_unionPartitionBlocks_iff
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (G : Finset R.parts) (B : R.parts) :
    B.1 ⊆ unionPartitionBlocks R G ↔ B ∈ G := by
  classical
  constructor
  · intro hsub
    obtain ⟨x, hxB⟩ := R.nonempty_of_mem_parts B.2
    obtain ⟨C, hCG, hxC⟩ :=
      (mem_unionPartitionBlocks R G x).mp (hsub hxB)
    have hBC : B.1 = C.1 := R.eq_of_mem_parts B.2 C.2 hxB hxC
    have hBCsub : B = C := Subtype.ext hBC
    exact hBCsub ▸ hCG
  · intro hBG x hxB
    exact (mem_unionPartitionBlocks R G x).mpr ⟨B, hBG, hxB⟩

/-- Coarsen `R` by grouping its blocks according to a partition `S` of the
finite type of `R`-blocks. -/
noncomputable def coarsenFromBlockPartition
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (S : Finpartition (Finset.univ : Finset R.parts)) : Finpartition s := by
  classical
  exact Finpartition.ofExistsUnique
    (S.parts.image (unionPartitionBlocks R))
    (by
      intro U hU
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hU
      exact unionPartitionBlocks_subset R G)
    (by
      intro x hx
      obtain ⟨B, ⟨hB, hxB⟩, hBuniq⟩ := R.existsUnique_mem hx
      let b : R.parts := ⟨B, hB⟩
      obtain ⟨G, ⟨hG, hbG⟩, hGuniq⟩ :=
        S.existsUnique_mem (Finset.mem_univ b)
      refine ⟨unionPartitionBlocks R G,
        ⟨Finset.mem_image.mpr ⟨G, hG, rfl⟩,
          (mem_unionPartitionBlocks R G x).mpr ⟨b, hbG, hxB⟩⟩, ?_⟩
      intro U hU
      obtain ⟨hUparts, hxU⟩ := hU
      obtain ⟨H, hH, hHU⟩ := Finset.mem_image.mp hUparts
      obtain ⟨C, hCH, hxC⟩ :=
        (mem_unionPartitionBlocks R H x).mp (hHU.symm ▸ hxU)
      have hBC : B = C.1 := (hBuniq C.1 ⟨C.2, hxC⟩).symm
      have hbC : b = C := Subtype.ext hBC
      have hbH : b ∈ H := hbC ▸ hCH
      have hHG : H = G := hGuniq H ⟨hH, hbH⟩
      exact hHU.symm.trans (congrArg (unionPartitionBlocks R) hHG))
    (by
      intro hEmpty
      obtain ⟨G, hG, hGU⟩ := Finset.mem_image.mp hEmpty
      obtain ⟨B, hBG⟩ := S.nonempty_of_mem_parts hG
      obtain ⟨x, hxB⟩ := R.nonempty_of_mem_parts B.2
      have hxU : x ∈ unionPartitionBlocks R G :=
        (mem_unionPartitionBlocks R G x).mpr ⟨B, hBG, hxB⟩
      rw [hGU] at hxU
      simpa using hxU)

@[simp]
theorem coarsenFromBlockPartition_parts
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (S : Finpartition (Finset.univ : Finset R.parts)) :
    (coarsenFromBlockPartition R S).parts =
      S.parts.image (unionPartitionBlocks R) :=
  rfl

theorem fine_le_coarsenFromBlockPartition
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (S : Finpartition (Finset.univ : Finset R.parts)) :
    R ≤ coarsenFromBlockPartition R S := by
  classical
  intro B hB
  let b : R.parts := ⟨B, hB⟩
  obtain ⟨G, ⟨hG, hbG⟩, -⟩ :=
    S.existsUnique_mem (Finset.mem_univ b)
  refine ⟨unionPartitionBlocks R G,
    Finset.mem_image.mpr ⟨G, hG, rfl⟩, ?_⟩
  exact (block_subset_unionPartitionBlocks_iff R G b).mpr hbG

/-- Fine blocks of `R` that lie inside one ambient block `D`. -/
noncomputable def fineBlocksInOuter
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (D : Finset α) : Finset R.parts :=
  R.parts.attach.filter (fun B ↦ B.1 ⊆ D)

@[simp]
theorem mem_fineBlocksInOuter
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (D : Finset α) (B : R.parts) :
    B ∈ fineBlocksInOuter R D ↔ B.1 ⊆ D := by
  simp [fineBlocksInOuter]

/-- If `R` refines `P`, the union of the fine blocks contained in an outer
block of `P` is exactly that outer block. -/
theorem union_fineBlocksInOuter_eq
    {α : Type*} [DecidableEq α] {s : Finset α}
    {R P : Finpartition s} (hRP : R ≤ P)
    {D : Finset α} (hD : D ∈ P.parts) :
    unionPartitionBlocks R (fineBlocksInOuter R D) = D := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨B, hBgroup, hxB⟩ :=
      (mem_unionPartitionBlocks R (fineBlocksInOuter R D) x).mp hx
    exact (mem_fineBlocksInOuter R D B).mp hBgroup hxB
  · intro hxD
    have hxs : x ∈ s := P.subset hD hxD
    obtain ⟨C, hC, hxC⟩ := R.exists_mem hxs
    obtain ⟨E, hE, hCE⟩ := hRP hC
    have hED : E = D := P.eq_of_mem_parts hE hD (hCE hxC) hxD
    let B : R.parts := ⟨C, hC⟩
    apply (mem_unionPartitionBlocks R (fineBlocksInOuter R D) x).mpr
    refine ⟨B, (mem_fineBlocksInOuter R D B).mpr ?_, hxC⟩
    simpa only [hED] using hCE

/-- Recover the grouping of the fine blocks from a coarsening. -/
noncomputable def blockPartitionOfCoarsening
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (P : {P : Finpartition s // R ≤ P}) :
    Finpartition (Finset.univ : Finset R.parts) := by
  classical
  exact Finpartition.ofExistsUnique
    (P.1.parts.image (fineBlocksInOuter R))
    (by
      intro G _ B _
      exact Finset.mem_univ B)
    (by
      intro B _
      obtain ⟨D, hD, hBD⟩ := P.2 B.2
      refine ⟨fineBlocksInOuter R D,
        ⟨Finset.mem_image.mpr ⟨D, hD, rfl⟩,
          (mem_fineBlocksInOuter R D B).mpr hBD⟩, ?_⟩
      intro G hG
      obtain ⟨hGparts, hBG⟩ := hG
      obtain ⟨E, hE, hEG⟩ := Finset.mem_image.mp hGparts
      have hBE : B.1 ⊆ E :=
        (mem_fineBlocksInOuter R E B).mp (hEG.symm ▸ hBG)
      obtain ⟨x, hxB⟩ := R.nonempty_of_mem_parts B.2
      have hDE : D = E := P.1.eq_of_mem_parts hD hE (hBD hxB) (hBE hxB)
      exact hEG.symm.trans (congrArg (fineBlocksInOuter R) hDE.symm))
    (by
      intro hEmpty
      obtain ⟨D, hD, hDG⟩ := Finset.mem_image.mp hEmpty
      obtain ⟨x, hxD⟩ := P.1.nonempty_of_mem_parts hD
      have hxs : x ∈ s := P.1.subset hD hxD
      obtain ⟨C, hC, hxC⟩ := R.exists_mem hxs
      obtain ⟨E, hE, hCE⟩ := P.2 hC
      have hED : E = D := P.1.eq_of_mem_parts hE hD (hCE hxC) hxD
      let B : R.parts := ⟨C, hC⟩
      have hBG : B ∈ fineBlocksInOuter R D :=
        (mem_fineBlocksInOuter R D B).mpr (by simpa only [hED] using hCE)
      rw [hDG] at hBG
      simpa using hBG)

@[simp]
theorem blockPartitionOfCoarsening_parts
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (P : {P : Finpartition s // R ≤ P}) :
    (blockPartitionOfCoarsening R P).parts =
      P.1.parts.image (fineBlocksInOuter R) :=
  rfl

@[simp]
theorem fineBlocksInOuter_unionPartitionBlocks
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (G : Finset R.parts) :
    fineBlocksInOuter R (unionPartitionBlocks R G) = G := by
  classical
  ext B
  rw [mem_fineBlocksInOuter,
    block_subset_unionPartitionBlocks_iff]

/-- Recovering the grouping after coarsening is the identity. -/
theorem blockPartitionOfCoarsening_coarsenFromBlockPartition
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (S : Finpartition (Finset.univ : Finset R.parts)) :
    blockPartitionOfCoarsening R
        ⟨coarsenFromBlockPartition R S,
          fine_le_coarsenFromBlockPartition R S⟩ = S := by
  classical
  ext G
  rw [blockPartitionOfCoarsening_parts,
    coarsenFromBlockPartition_parts]
  constructor
  · intro hG
    obtain ⟨U, hU, hUG⟩ := Finset.mem_image.mp hG
    obtain ⟨H, hH, hHU⟩ := Finset.mem_image.mp hU
    have hGH : G = H := by
      rw [← hUG, ← hHU, fineBlocksInOuter_unionPartitionBlocks]
    exact hGH ▸ hH
  · intro hG
    apply Finset.mem_image.mpr
    refine ⟨unionPartitionBlocks R G,
      Finset.mem_image.mpr ⟨G, hG, rfl⟩, ?_⟩
    exact fineBlocksInOuter_unionPartitionBlocks R G

/-- Coarsening the grouping recovered from `P` reconstructs `P`. -/
theorem coarsenFromBlockPartition_blockPartitionOfCoarsening
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (P : {P : Finpartition s // R ≤ P}) :
    coarsenFromBlockPartition R (blockPartitionOfCoarsening R P) = P.1 := by
  classical
  ext D
  rw [coarsenFromBlockPartition_parts,
    blockPartitionOfCoarsening_parts]
  constructor
  · intro hD
    obtain ⟨G, hG, hGD⟩ := Finset.mem_image.mp hD
    obtain ⟨E, hE, hEG⟩ := Finset.mem_image.mp hG
    have hDE : D = E := by
      rw [← hGD, ← hEG, union_fineBlocksInOuter_eq P.2 hE]
    exact hDE ▸ hE
  · intro hD
    apply Finset.mem_image.mpr
    refine ⟨fineBlocksInOuter R D,
      Finset.mem_image.mpr ⟨D, hD, rfl⟩, ?_⟩
    exact union_fineBlocksInOuter_eq P.2 hD

/-- Coarsenings of a fixed fine partition are exactly set partitions of its
finite type of blocks. -/
noncomputable def coarseningsEquivBlockPartitions
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s) :
    {P : Finpartition s // R ≤ P} ≃
      Finpartition (Finset.univ : Finset R.parts) where
  toFun := blockPartitionOfCoarsening R
  invFun S := ⟨coarsenFromBlockPartition R S,
    fine_le_coarsenFromBlockPartition R S⟩
  left_inv := fun P ↦ Subtype.ext
    (coarsenFromBlockPartition_blockPartitionOfCoarsening R P)
  right_inv := blockPartitionOfCoarsening_coarsenFromBlockPartition R

theorem card_fineBlocksInOuter
    {α : Type*} [DecidableEq α] {s : Finset α} (R : Finpartition s)
    (D : Finset α) :
    (fineBlocksInOuter R D).card =
      (R.parts.filter (fun B ↦ B ⊆ D)).card := by
  classical
  apply Finset.card_bij (fun B _ ↦ B.1)
  · intro B hB
    exact Finset.mem_filter.mpr
      ⟨B.2, (mem_fineBlocksInOuter R D B).mp hB⟩
  · intro B _ C _ hBC
    exact Subtype.ext hBC
  · intro C hC
    obtain ⟨hCparts, hCD⟩ := Finset.mem_filter.mp hC
    let B : R.parts := ⟨C, hCparts⟩
    exact ⟨B, ⟨(mem_fineBlocksInOuter R D B).mpr hCD, rfl⟩⟩

/-- Under the coarsening equivalence, the interval coefficient is the
block-product Möbius weight of the induced partition of fine blocks. -/
theorem refinementMobiusWeight_eq_partitionBlockMobiusProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finpartition (Finset.univ : Finset ι))
    (P : {P : Finpartition (Finset.univ : Finset ι) // R ≤ P}) :
    refinementMobiusWeight P.1 ⟨R, P.2⟩ =
      partitionBlockMobiusProduct (blockPartitionOfCoarsening R P) := by
  classical
  rw [refinementMobiusWeight_eq_blockCounts]
  rw [partitionBlockMobiusProduct, blockPartitionOfCoarsening_parts]
  have hinj : Set.InjOn (fineBlocksInOuter R) P.1.parts := by
    intro D hD E hE hDE
    have h := congrArg (unionPartitionBlocks R) hDE
    simpa only [union_fineBlocksInOuter_eq P.2 hD,
      union_fineBlocksInOuter_eq P.2 hE] using h
  rw [Finset.prod_image hinj]
  have hattach :
      (∏ B : P.1.parts,
        ((-1 : ℝ) ^ ((R.parts.filter (fun C ↦ C ⊆ B.1)).card - 1) *
          (Nat.factorial
            ((R.parts.filter (fun C ↦ C ⊆ B.1)).card - 1) : ℝ))) =
      ∏ D ∈ P.1.parts,
        ((-1 : ℝ) ^ ((R.parts.filter (fun C ↦ C ⊆ D)).card - 1) *
          (Nat.factorial
            ((R.parts.filter (fun C ↦ C ⊆ D)).card - 1) : ℝ)) := by
    change (∏ B ∈ P.1.parts.attach,
        ((-1 : ℝ) ^ ((R.parts.filter (fun C ↦ C ⊆ B.1)).card - 1) *
          (Nat.factorial
            ((R.parts.filter (fun C ↦ C ⊆ B.1)).card - 1) : ℝ))) = _
    exact Finset.prod_attach P.1.parts (fun D ↦
      ((-1 : ℝ) ^ ((R.parts.filter (fun C ↦ C ⊆ D)).card - 1) *
        (Nat.factorial
          ((R.parts.filter (fun C ↦ C ⊆ D)).card - 1) : ℝ)))
  rw [hattach]
  apply Finset.prod_congr rfl
  intro D hD
  rw [partitionBlockMobiusWeight, card_fineBlocksInOuter]

noncomputable def coarseningRefinementMobiusSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finpartition (Finset.univ : Finset ι)) : ℝ := by
  classical
  exact ∑ P : {P : Finpartition (Finset.univ : Finset ι) // R ≤ P},
    refinementMobiusWeight P.1 ⟨R, P.2⟩

/-- The sum of interval weights over all coarsenings cancels unless the fixed
fine partition has exactly one block. -/
theorem sum_refinementMobiusWeight_over_coarsenings
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R : Finpartition (Finset.univ : Finset ι)) :
    coarseningRefinementMobiusSum R =
      if R.parts.card = 1 then 1 else 0 := by
  classical
  rw [coarseningRefinementMobiusSum]
  letI : Nonempty R.parts := Finset.nonempty_coe_sort.mpr
    (R.parts_nonempty Finset.univ_nonempty.ne_empty)
  calc
    _ = ∑ S : Finpartition (Finset.univ : Finset R.parts),
        partitionBlockMobiusProduct S :=
      Fintype.sum_equiv (coarseningsEquivBlockPartitions R)
        (fun P ↦ refinementMobiusWeight P.1 ⟨R, P.2⟩)
        partitionBlockMobiusProduct
        (refinementMobiusWeight_eq_partitionBlockMobiusProduct R)
    _ = if Fintype.card R.parts = 1 then 1 else 0 :=
      sum_partitionBlockMobiusProduct_univ
    _ = _ := by rw [Fintype.card_coe]

/-- Swap the two descriptions of a comparable pair in the finite partition
lattice. -/
noncomputable def refinementPairsSwap
    {α : Type*} [DecidableEq α] (s : Finset α) :
    (Σ P : Finpartition s, {R : Finpartition s // R ≤ P}) ≃
      (Σ R : Finpartition s, {P : Finpartition s // R ≤ P}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv := by rintro ⟨P, R, h⟩; rfl
  right_inv := by rintro ⟨R, P, h⟩; rfl

/-- Swap the outer-partition and global-refinement sums. -/
theorem sum_globalRefinementExpansionSum_reindex
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ) :
    (∑ P : Finpartition (Finset.univ : Finset ι),
        globalRefinementExpansionSum Y P) =
      ∑ R : Finpartition (Finset.univ : Finset ι),
        coarseningRefinementMobiusSum R * partitionMomentProduct Y R := by
  classical
  simp only [globalRefinementExpansionSum]
  calc
    _ = ∑ z : Σ P : Finpartition (Finset.univ : Finset ι),
          {R : Finpartition (Finset.univ : Finset ι) // R ≤ P},
        refinementMobiusWeight z.1 z.2 *
          partitionMomentProduct Y z.2.1 :=
      (Fintype.sum_sigma _).symm
    _ = ∑ z : Σ R : Finpartition (Finset.univ : Finset ι),
          {P : Finpartition (Finset.univ : Finset ι) // R ≤ P},
        refinementMobiusWeight z.2.1 ⟨z.1, z.2.2⟩ *
          partitionMomentProduct Y z.1 := by
      apply Fintype.sum_equiv
        (refinementPairsSwap (Finset.univ : Finset ι))
      intro z
      rfl
    _ = ∑ R : Finpartition (Finset.univ : Finset ι),
        ∑ P : {P : Finpartition (Finset.univ : Finset ι) // R ≤ P},
          refinementMobiusWeight P.1 ⟨R, P.2⟩ *
            partitionMomentProduct Y R := Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R _
      rw [coarseningRefinementMobiusSum, Finset.sum_mul]

theorem finpartition_eq_indiscrete_of_card_parts_eq_one
    {α : Type*} [DecidableEq α] {s : Finset α} (hs : s ≠ ∅)
    (R : Finpartition s) (hcard : R.parts.card = 1) :
    R = Finpartition.indiscrete hs := by
  classical
  obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hcard
  have hB : B = s := by
    have hsup := R.sup_parts
    rw [hparts, Finset.sup_singleton] at hsup
    exact hsup
  ext C
  rw [hparts, Finpartition.indiscrete_parts hs, hB]

/-- After summing over every outer partition, interval cancellation leaves
only the indiscrete global refinement. -/
theorem sum_globalRefinementExpansionSum_eq_indiscrete
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Y : ι → Ω → ℝ) :
    (∑ P : Finpartition (Finset.univ : Finset ι),
        globalRefinementExpansionSum Y P) =
      partitionMomentProduct Y
        (Finpartition.indiscrete Finset.univ_nonempty.ne_empty) := by
  classical
  rw [sum_globalRefinementExpansionSum_reindex]
  simp_rw [sum_refinementMobiusWeight_over_coarsenings]
  let Ptop : Finpartition (Finset.univ : Finset ι) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  change (∑ R : Finpartition (Finset.univ : Finset ι),
      (if R.parts.card = 1 then 1 else 0) * partitionMomentProduct Y R) =
    partitionMomentProduct Y Ptop
  rw [Fintype.sum_eq_single Ptop]
  · have hparts : Ptop.parts = {Finset.univ} :=
      Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty
    simp [hparts]
  · intro R hR
    have hcard : R.parts.card ≠ 1 := by
      intro hc
      apply hR
      exact finpartition_eq_indiscrete_of_card_parts_eq_one
        Finset.univ_nonempty.ne_empty R hc
    simp [hcard]

theorem partitionMomentProduct_indiscrete
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Y : ι → Ω → ℝ) :
    partitionMomentProduct Y
        (Finpartition.indiscrete Finset.univ_nonempty.ne_empty) =
      uniformExpectation (fun ω ↦ ∏ j, Y j ω) := by
  rw [partitionMomentProduct,
    Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty]
  simp

/-- Moment--cumulant inversion for a nonempty finite index type. -/
theorem moment_cumulant_inverse_nonempty_index
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Nonempty Ω] [Nonempty ι] (Y : ι → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∏ j, Y j ω) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ Y j.1) := by
  classical
  calc
    _ = partitionMomentProduct Y
        (Finpartition.indiscrete Finset.univ_nonempty.ne_empty) :=
      (partitionMomentProduct_indiscrete Y).symm
    _ = ∑ P : Finpartition (Finset.univ : Finset ι),
        globalRefinementExpansionSum Y P :=
      (sum_globalRefinementExpansionSum_eq_indiscrete Y).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      calc
        globalRefinementExpansionSum Y P =
            ∏ B : P.parts,
              jointCumulantOn (fun j : B.1 ↦ Y j.1) :=
          (product_jointCumulantOn_expansion_global Y P).symm
        _ = ∏ B ∈ P.parts,
              jointCumulantOn (fun j : B ↦ Y j.1) := by
          change (∏ B ∈ P.parts.attach,
              jointCumulantOn (fun j : B.1 ↦ Y j.1)) = _
          exact Finset.prod_attach P.parts (fun B ↦
            jointCumulantOn (fun j : B ↦ Y j.1))

/-- Full arbitrary-order identity matching the corrected I08 interface. -/
theorem moment_cumulant_inverse_fin
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ}
    (Y : Fin q → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∏ j, Y j ω) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin q)),
        ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ Y j.1) := by
  classical
  cases q with
  | zero => exact moment_cumulant_inverse_fin_zero Y
  | succ n =>
      letI : Nonempty (Fin n.succ) := ⟨0⟩
      exact moment_cumulant_inverse_nonempty_index Y

end Problem56
