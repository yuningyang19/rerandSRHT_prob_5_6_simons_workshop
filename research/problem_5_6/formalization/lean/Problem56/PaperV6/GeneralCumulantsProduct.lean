import Problem56.PaperV6.GeneralCumulantsMoment

/-! Additive adaptation of only the expectation-dependent ProductCumulant layer.
Public join partitions, coarsening coefficients, and Stirling cancellation are
imported unchanged from B. Short private equivalence helpers are reproduced
under distinct names because their original declarations are inaccessible. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

noncomputable def measureConnectedPartitionCumulantSum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (τ : Finpartition (Finset.univ : Finset ι)) : ℝ := by
  classical
  exact ∑ σ : Finpartition (Finset.univ : Finset ι),
    if ProductPartitionConnected σ τ then measurePartitionCumulantProduct μ Y σ else 0

private noncomputable def measure_finsetOrderIsoOfEquiv
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro s t
    simp only [Equiv.finsetCongr_apply]
    exact Finset.map_subset_map

@[simp]
private theorem measure_finsetOrderIsoOfEquiv_apply
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset α) :
    measure_finsetOrderIsoOfEquiv e s = s.map e.toEmbedding :=
  rfl

private noncomputable def measure_finpartitionMapEquiv
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

private noncomputable def measure_finpartitionCopyEquiv
    {α : Type*} [Lattice α] [OrderBot α] {a b : α} (h : a = b) :
    Finpartition a ≃ Finpartition b where
  toFun P := P.copy h
  invFun Q := Q.copy h.symm
  left_inv P := by subst b; rfl
  right_inv Q := by subst b; rfl

@[simp]
private theorem measure_finsetOrderIsoOfEquiv_univ
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    measure_finsetOrderIsoOfEquiv e (Finset.univ : Finset α) = Finset.univ := by
  ext y
  simp

private noncomputable def measure_finpartitionCongr
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Finpartition (Finset.univ : Finset α) ≃
      Finpartition (Finset.univ : Finset β) :=
  (measure_finpartitionMapEquiv (measure_finsetOrderIsoOfEquiv e) Finset.univ).trans
    (measure_finpartitionCopyEquiv (measure_finsetOrderIsoOfEquiv_univ e))

@[simp]
private theorem measure_finpartitionCongr_parts
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    (measure_finpartitionCongr e P).parts =
      P.parts.map (measure_finsetOrderIsoOfEquiv e).toEmbedding :=
  rfl

theorem measure_jointCumulantOn_equiv
    {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (μ : Measure Ω) (Y : β → Ω → ℝ) :
    measureJointCumulant μ (fun a ↦ Y (e a)) = measureJointCumulant μ Y := by
  classical
  rw [measureJointCumulant, measureJointCumulant]
  apply Fintype.sum_equiv (measure_finpartitionCongr e)
  intro P
  have hcard : (measure_finpartitionCongr e P).parts.card = P.parts.card := by
    rw [measure_finpartitionCongr_parts, Finset.card_map]
  rw [hcard]
  congr 1
  rw [measure_finpartitionCongr_parts, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro A _
  apply congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ)
  funext ω
  change (∏ j ∈ A, Y (e j) ω) =
    ∏ j ∈ A.map e.toEmbedding, Y j ω
  rw [Finset.prod_map]
  rfl

private noncomputable def measure_mappedBlockElementEquiv
    {ι : Type*} [DecidableEq ι] (B : Finset ι) (C : Finset B) :
    C ≃ (C.map
      (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι)) where
  toFun j := ⟨j.1.1, Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩⟩
  invFun j :=
    let h := Finset.mem_map.mp j.2
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  left_inv j := by
    apply Subtype.ext
    let h := Finset.mem_map.mp
      (show j.1.1 ∈ C.map
        (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) from
          Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩)
    apply Subtype.ext
    exact (Classical.choose_spec h).2
  right_inv j := by
    apply Subtype.ext
    let h := Finset.mem_map.mp j.2
    exact (Classical.choose_spec h).2

private theorem measure_jointCumulantOn_mappedBlock
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (B : Finset ι) (C : Finset B) :
    measureJointCumulant μ (fun j : C ↦ Y j.1.1) =
      measureJointCumulant μ (fun j : C.map
        (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) ↦ Y j.1) := by
  calc
    _ = measureJointCumulant μ (fun j : C ↦
          (fun k : C.map
            (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) ↦ Y k.1)
            (measure_mappedBlockElementEquiv B C j)) := by
        rfl
    _ = _ := measure_jointCumulantOn_equiv (μ := μ) (measure_mappedBlockElementEquiv B C)
      (fun j ↦ Y j.1)

private theorem measure_nested_blockCumulantProduct_eq_global
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts,
      Finpartition (Finset.univ : Finset B.1)) :
    (∏ B : P.parts, ∏ C ∈ (Q B).parts,
        measureJointCumulant μ (fun j : C ↦ Y j.1.1)) =
      measurePartitionCumulantProduct μ Y (nestedGlobalRefinement P Q) := by
  classical
  rw [measurePartitionCumulantProduct, nestedGlobalRefinement]
  calc
    _ = ∏ B : P.parts,
        ∏ D ∈ (liftBlockPartition B.1 (Q B)).parts,
          measureJointCumulant μ (fun j : D ↦ Y j.1) := by
      apply Fintype.prod_congr
      intro B
      rw [liftBlockPartition_parts]
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl
        intro C _
        exact measure_jointCumulantOn_mappedBlock (μ := μ) Y B.1 C
      · intro C _ D _ hCD
        exact Finset.map_injective
          (⟨Subtype.val, Subtype.val_injective⟩ : B.1 ↪ ι) hCD
    _ = _ := (prod_bind_finpartition P
      (fun B : P.parts ↦ liftBlockPartition B.1 (Q B))
      (fun D ↦ measureJointCumulant μ (fun j : D ↦ Y j.1))).symm

noncomputable def measure_refinementCumulantSum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) : ℝ := by
  classical
  exact ∑ R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P},
    measurePartitionCumulantProduct μ Y R.1

theorem measure_partitionMomentProduct_eq_sum_refinement_cumulant
    {Ω ι : Type*} [MeasurableSpace Ω] 
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    measure_partitionMomentProduct μ Y P =
      measure_refinementCumulantSum (μ := μ) Y P := by
  classical
  rw [measure_partitionMomentProduct, measure_refinementCumulantSum]
  have hattach :
      (∏ C ∈ P.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j ω)) =
        ∏ B : P.parts,
          (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j : B.1, Y j.1 ω) := by
    change (∏ C ∈ P.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j ω)) =
      ∏ B ∈ (Finset.univ : Finset P.parts),
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j : B.1, Y j.1 ω)
    rw [Finset.univ_eq_attach]
    calc
      _ = ∏ B ∈ P.parts.attach,
          (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ B.1, Y j ω) :=
        (Finset.prod_attach P.parts (fun C ↦
          (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j ω))).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro B _
        apply congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ)
        funext ω
        exact Finset.prod_subtype B.1 (fun _ ↦ Iff.rfl)
          (fun j ↦ Y j ω)
  rw [hattach]
  have hblock (B : P.parts) :
      (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j : B.1, Y j.1 ω) =
        ∑ S : Finpartition (Finset.univ : Finset B.1),
          ∏ C ∈ S.parts, measureJointCumulant μ (fun j : C ↦ Y j.1.1) := by
    letI : Nonempty B.1 := Finset.nonempty_coe_sort.mpr
      (P.nonempty_of_mem_parts B.2)
    exact measure_moment_cumulant_inverse_nonempty_index μ (fun j : B.1 ↦ Y j.1)
  simp_rw [hblock]
  rw [Fintype.prod_sum]
  let e := nestedPartitionsEquivGlobalRefinements P
  apply Fintype.sum_equiv e
  intro Q
  exact measure_nested_blockCumulantProduct_eq_global (μ := μ) Y P Q

private theorem measure_unionPartitionBlocks_injective
    {α : Type*} [DecidableEq α] {s : Finset α}
    (R : Finpartition s) :
    Function.Injective (unionPartitionBlocks R) := by
  intro G H hGH
  ext B
  rw [← block_subset_unionPartitionBlocks_iff R G B,
    ← block_subset_unionPartitionBlocks_iff R H B, hGH]

private theorem measure_prod_blocks_eq_prod_unionPartitionBlocks
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (R : Finpartition (Finset.univ : Finset ι))
    (G : Finset R.parts) (f : ι → M) :
    (∏ B ∈ G, ∏ j ∈ B.1, f j) =
      ∏ j ∈ unionPartitionBlocks R G, f j := by
  classical
  rw [unionPartitionBlocks, Finset.prod_biUnion]
  intro B hB C hC hBC
  apply R.disjoint B.2 C.2
  intro h
  apply hBC
  exact Subtype.ext h

noncomputable def measure_outerCumulantCoarseningSum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (τ : Finpartition (Finset.univ : Finset ι)) : ℝ :=
  ∑ S : Finpartition (Finset.univ : Finset τ.parts),
    finpartitionMobiusWeight S *
      measure_partitionMomentProduct μ Y (coarsenFromBlockPartition τ S)

private theorem measure_outer_blockMomentProduct_eq_coarsening
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (τ : Finpartition (Finset.univ : Finset ι))
    (S : Finpartition (Finset.univ : Finset τ.parts)) :
    (∏ G ∈ S.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦
          ∏ B ∈ G, ∏ j ∈ B.1, Y j ω)) =
      measure_partitionMomentProduct μ Y (coarsenFromBlockPartition τ S) := by
  classical
  rw [measure_partitionMomentProduct, coarsenFromBlockPartition_parts]
  rw [Finset.prod_image (measure_unionPartitionBlocks_injective τ).injOn]
  apply Finset.prod_congr rfl
  intro G _
  apply congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ)
  funext ω
  exact measure_prod_blocks_eq_prod_unionPartitionBlocks τ G (fun j ↦ Y j ω)

theorem measure_jointCumulantOn_blockProducts_eq_outerCoarseningSum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (τ : Finpartition (Finset.univ : Finset ι)) :
    measureJointCumulant μ (fun B : τ.parts ↦
      fun ω ↦ ∏ j ∈ B.1, Y j ω) =
      measure_outerCumulantCoarseningSum (μ := μ) Y τ := by
  classical
  rw [measureJointCumulant, measure_outerCumulantCoarseningSum]
  apply Finset.sum_congr rfl
  intro S _
  rw [finpartitionMobiusWeight,
    measure_outer_blockMomentProduct_eq_coarsening (μ := μ)]

private noncomputable def measure_outerRefinementPairsSwap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Finpartition (Finset.univ : Finset ι)) :
    (Σ S : Finpartition (Finset.univ : Finset τ.parts),
      {σ : Finpartition (Finset.univ : Finset ι) //
        σ ≤ coarsenFromBlockPartition τ S}) ≃
    (Σ σ : Finpartition (Finset.univ : Finset ι),
      {S : Finpartition (Finset.univ : Finset τ.parts) //
        σ ≤ coarsenFromBlockPartition τ S}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv := by rintro ⟨S, σ, h⟩; rfl
  right_inv := by rintro ⟨σ, S, h⟩; rfl

theorem measure_outerCumulantCoarseningSum_reindex
    {Ω ι : Type*} [MeasurableSpace Ω] 
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (τ : Finpartition (Finset.univ : Finset ι)) :
    measure_outerCumulantCoarseningSum (μ := μ) Y τ =
      ∑ σ : Finpartition (Finset.univ : Finset ι),
        commonCoarseningMobiusSum σ τ * measurePartitionCumulantProduct μ Y σ := by
  classical
  rw [measure_outerCumulantCoarseningSum]
  simp_rw [measure_partitionMomentProduct_eq_sum_refinement_cumulant (μ := μ),
    measure_refinementCumulantSum, Finset.mul_sum]
  calc
    _ = ∑ z : Σ S : Finpartition (Finset.univ : Finset τ.parts),
          {σ : Finpartition (Finset.univ : Finset ι) //
            σ ≤ coarsenFromBlockPartition τ S},
        finpartitionMobiusWeight z.1 * measurePartitionCumulantProduct μ Y z.2.1 :=
      (Fintype.sum_sigma _).symm
    _ = ∑ z : Σ σ : Finpartition (Finset.univ : Finset ι),
          {S : Finpartition (Finset.univ : Finset τ.parts) //
            σ ≤ coarsenFromBlockPartition τ S},
        finpartitionMobiusWeight z.2.1 * measurePartitionCumulantProduct μ Y z.1 := by
      apply Fintype.sum_equiv (measure_outerRefinementPairsSwap τ)
      intro z
      rfl
    _ = ∑ σ : Finpartition (Finset.univ : Finset ι),
        ∑ S : {S : Finpartition (Finset.univ : Finset τ.parts) //
          σ ≤ coarsenFromBlockPartition τ S},
          finpartitionMobiusWeight S.1 * measurePartitionCumulantProduct μ Y σ :=
      Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [commonCoarseningMobiusSum, Finset.sum_mul]

theorem measure_product_cumulant_connected_identity_nonempty
    {Ω ι : Type*} [MeasurableSpace Ω] 
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (τ : Finpartition (Finset.univ : Finset ι)) :
    measureJointCumulant μ (fun B : τ.parts ↦
      fun ω ↦ ∏ j ∈ B.1, Y j ω) =
      measureConnectedPartitionCumulantSum μ Y τ := by
  classical
  rw [measure_jointCumulantOn_blockProducts_eq_outerCoarseningSum (μ := μ),
    measure_outerCumulantCoarseningSum_reindex (μ := μ),
    measureConnectedPartitionCumulantSum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [commonCoarseningMobiusSum_eq_connectivity]
  by_cases hconn : ProductPartitionConnected σ τ
  · have hcard :=
      (productPartitionConnected_iff_connectivity_card_one σ τ).mp hconn
    simp [hconn, hcard]
  · have hcard : (productConnectivityPartition σ τ).parts.card ≠ 1 :=
      fun hc ↦ hconn
        ((productPartitionConnected_iff_connectivity_card_one σ τ).mpr hc)
    simp [hconn, hcard]

theorem generalProductIdentity : GeneralProductIdentityExpected := by
  intro Ω ι _ _ _ _ μ _ Y _ τ
  exact measure_product_cumulant_connected_identity_nonempty μ Y τ

end Problem56.PaperV6
