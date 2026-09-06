import Problem56.PaperV6.GeneralCumulantsExpected

/-!
The expectation-dependent layer of B CumulantMoment is adapted to ordinary
real integrals. Public partition equivalences and Möbius cancellation are
reused unchanged. The algebraic proof requires no integrability assumption;
public finite-moment hypotheses are retained by the source-bound wrapper.
Expected types independently approved by v6_inventory before proof generation.
-/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV6

theorem measure_product_jointCumulant_expansion
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∏ B : P.parts, measureJointCumulant μ (fun j : B.1 ↦ Y j.1)) =
      ∑ Q : ∀ B : P.parts,
          Finpartition (Finset.univ : Finset B.1),
        ∏ B : P.parts,
          (((-1 : ℝ) ^ ((Q B).parts.card - 1) *
            (Nat.factorial ((Q B).parts.card - 1) : ℝ)) *
            ∏ C ∈ (Q B).parts,
              (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j.1 ω)) := by
  simp only [measureJointCumulant]
  rw [Fintype.prod_sum]

/-! ### Nested block partitions and their global refinement -/

noncomputable def measure_partitionMomentProduct
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (R : Finpartition (Finset.univ : Finset ι)) : ℝ :=
  ∏ C ∈ R.parts,
    (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j ω)

/-- Passing a block partition between the subtype and ambient
representations preserves its product of block moments. -/
theorem measure_blockMomentProduct_liftBlockPartition
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (B : Finset ι)
    (Q : Finpartition (Finset.univ : Finset B)) :
    (∏ C ∈ Q.parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j.1 ω)) =
      ∏ D ∈ (liftBlockPartition B Q).parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ D, Y j ω) := by
  classical
  rw [liftBlockPartition_parts]
  rw [Finset.prod_image (by
    intro C _ D _ hCD
    exact Finset.map_injective
      (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι) hCD)]
  apply Finset.prod_congr rfl
  intro C _
  apply congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ)
  funext ω
  change (∏ j ∈ C, Y j.1 ω) =
    ∏ j ∈ C.map (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ ι), Y j ω
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  rfl

/-- The moment factors in nested data are exactly the moment factors indexed
by the associated global refinement. -/
theorem measure_nested_blockMomentProduct_eq_global
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι))
    (Q : ∀ B : P.parts, Finpartition (Finset.univ : Finset B.1)) :
    (∏ B : P.parts, ∏ C ∈ (Q B).parts,
        (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j.1 ω)) =
      measure_partitionMomentProduct μ Y (nestedGlobalRefinement P Q) := by
  classical
  rw [measure_partitionMomentProduct, nestedGlobalRefinement]
  rw [prod_bind_finpartition P
    (fun B : P.parts ↦ liftBlockPartition B.1 (Q B))]
  apply Fintype.prod_congr
  intro B
  exact measure_blockMomentProduct_liftBlockPartition μ Y B.1 (Q B)


noncomputable def measure_globalRefinementExpansionSum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) : ℝ := by
  classical
  exact ∑ R : {R : Finpartition (Finset.univ : Finset ι) // R ≤ P},
    refinementMobiusWeight P R * measure_partitionMomentProduct μ Y R.1

/-- Reindex the product of block cumulants by global refinements of the outer
partition.  This is the exact finite reindexing immediately before the
Möbius-interval cancellation. -/
theorem measure_product_jointCumulant_expansion_global
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∏ B : P.parts, measureJointCumulant μ (fun j : B.1 ↦ Y j.1)) =
      measure_globalRefinementExpansionSum μ Y P := by
  classical
  rw [measure_globalRefinementExpansionSum]
  rw [measure_product_jointCumulant_expansion]
  let e := nestedPartitionsEquivGlobalRefinements P
  apply Fintype.sum_equiv e
  intro Q
  change
    (∏ B : P.parts,
      (finpartitionMobiusWeight (Q B) *
        ∏ C ∈ (Q B).parts,
          (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j ∈ C, Y j.1 ω))) = _
  rw [Finset.prod_mul_distrib]
  rw [← refinementMobiusWeight_nestedGlobalRefinement P Q,
    measure_nested_blockMomentProduct_eq_global μ Y P Q]
  rfl


theorem measure_sum_globalRefinementExpansionSum_reindex
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) :
    (∑ P : Finpartition (Finset.univ : Finset ι),
        measure_globalRefinementExpansionSum μ Y P) =
      ∑ R : Finpartition (Finset.univ : Finset ι),
        coarseningRefinementMobiusSum R * measure_partitionMomentProduct μ Y R := by
  classical
  simp only [measure_globalRefinementExpansionSum]
  calc
    _ = ∑ z : Σ P : Finpartition (Finset.univ : Finset ι),
          {R : Finpartition (Finset.univ : Finset ι) // R ≤ P},
        refinementMobiusWeight z.1 z.2 *
          measure_partitionMomentProduct μ Y z.2.1 :=
      (Fintype.sum_sigma _).symm
    _ = ∑ z : Σ R : Finpartition (Finset.univ : Finset ι),
          {P : Finpartition (Finset.univ : Finset ι) // R ≤ P},
        refinementMobiusWeight z.2.1 ⟨z.1, z.2.2⟩ *
          measure_partitionMomentProduct μ Y z.1 := by
      apply Fintype.sum_equiv
        (refinementPairsSwap (Finset.univ : Finset ι))
      intro z
      rfl
    _ = ∑ R : Finpartition (Finset.univ : Finset ι),
        ∑ P : {P : Finpartition (Finset.univ : Finset ι) // R ≤ P},
          refinementMobiusWeight P.1 ⟨R, P.2⟩ *
            measure_partitionMomentProduct μ Y R := Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R _
      rw [coarseningRefinementMobiusSum, Finset.sum_mul]

theorem measure_sum_globalRefinementExpansionSum_eq_indiscrete
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) :
    (∑ P : Finpartition (Finset.univ : Finset ι),
        measure_globalRefinementExpansionSum μ Y P) =
      measure_partitionMomentProduct μ Y
        (Finpartition.indiscrete Finset.univ_nonempty.ne_empty) := by
  classical
  rw [measure_sum_globalRefinementExpansionSum_reindex]
  simp_rw [sum_refinementMobiusWeight_over_coarsenings]
  let Ptop : Finpartition (Finset.univ : Finset ι) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  change (∑ R : Finpartition (Finset.univ : Finset ι),
      (if R.parts.card = 1 then 1 else 0) * measure_partitionMomentProduct μ Y R) =
    measure_partitionMomentProduct μ Y Ptop
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

theorem measure_partitionMomentProduct_indiscrete
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) :
    measure_partitionMomentProduct μ Y
        (Finpartition.indiscrete Finset.univ_nonempty.ne_empty) =
      (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j, Y j ω) := by
  rw [measure_partitionMomentProduct,
    Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty]
  simp

/-- Moment--cumulant inversion for a nonempty finite index type. -/
theorem measure_moment_cumulant_inverse_nonempty_index
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure Ω) (Y : ι → Ω → ℝ) :
    (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) (fun ω ↦ ∏ j, Y j ω) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        ∏ B ∈ P.parts, measureJointCumulant μ (fun j : B ↦ Y j.1) := by
  classical
  calc
    _ = measure_partitionMomentProduct μ Y
        (Finpartition.indiscrete Finset.univ_nonempty.ne_empty) :=
      (measure_partitionMomentProduct_indiscrete μ Y).symm
    _ = ∑ P : Finpartition (Finset.univ : Finset ι),
        measure_globalRefinementExpansionSum μ Y P :=
      (measure_sum_globalRefinementExpansionSum_eq_indiscrete μ Y).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      calc
        measure_globalRefinementExpansionSum μ Y P =
            ∏ B : P.parts,
              measureJointCumulant μ (fun j : B.1 ↦ Y j.1) :=
          (measure_product_jointCumulant_expansion_global μ Y P).symm
        _ = ∏ B ∈ P.parts,
              measureJointCumulant μ (fun j : B ↦ Y j.1) := by
          change (∏ B ∈ P.parts.attach,
              measureJointCumulant μ (fun j : B.1 ↦ Y j.1)) = _
          exact Finset.prod_attach P.parts (fun B ↦
            measureJointCumulant μ (fun j : B ↦ Y j.1))


 theorem generalMomentIdentity : GeneralMomentIdentityExpected := by
  intro Ω ι _ _ _ _ μ _ Y _
  exact measure_moment_cumulant_inverse_nonempty_index μ Y

end Problem56.PaperV6
