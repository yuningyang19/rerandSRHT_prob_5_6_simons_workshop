import Problem56.CumulantMoment
import Problem56.JointEntryCumulant
import Problem56.ProjectionMean

/-!
# Entry-cumulant expansion for the signed cyclic trace

This file isolates the exact moment--cumulant expansion of a cyclic product
of entries of the centered random projection.  It is independent of the
selector equality-partition reindexing and of the subsequent absolute-value
estimates.
-/

open scoped BigOperators Matrix

namespace Problem56

set_option maxHeartbeats 8000000

noncomputable section

abbrev SignPairSample (m : ℕ) :=
  SignLayer (WalshIndex m) × SignLayer (WalshIndex m)

def centeredRandomProjectionEntry {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : WalshIndex m) (d : SignPairSample m) : ℝ :=
  randomProjection d.1 d.2 V i j -
    (((r : ℝ) / walshCard m) •
      (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) i j

/-- Exact moment--cumulant expansion of a cyclic product of centered random
projection entries.  The absolute value is deliberately absent at this
stage. -/
theorem signPairExpectation_cyclic_centeredProjection_product_expansion
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (x : Fin q → WalshIndex m) :
    signPairExpectation (fun d₁ d₂ ↦
      ∏ f : Fin q,
        (randomProjection d₁ d₂ V -
          ((r : ℝ) / walshCard m) •
            (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))
          (x f) (x (cyclicSucc f))) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin q)),
        ∏ B ∈ P.parts,
          jointCumulantOn (fun e : B ↦
            centeredRandomProjectionEntry V
              (x e.1) (x (cyclicSucc e.1))) := by
  rw [signPairExpectation]
  exact moment_cumulant_inverse_fin (fun f d ↦
    centeredRandomProjectionEntry V (x f) (x (cyclicSucc f)) d)

private theorem jointCumulantOn_unique_eq_uniformExpectation
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Unique ι] (Y : ι → Ω → ℝ) :
    jointCumulantOn Y = uniformExpectation (Y default) := by
  classical
  letI : Subsingleton (Finpartition (Finset.univ : Finset ι)) := by
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
        intro z _
        obtain ⟨y, hy⟩ := R.nonempty_of_mem_parts hB
        simpa only [Subsingleton.elim z y] using hy
    rw [hparts P, hparts Q]
  let P₁ : Finpartition (Finset.univ : Finset ι) :=
    Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  rw [jointCumulantOn, Fintype.sum_subsingleton _ P₁]
  have hparts : P₁.parts = {Finset.univ} :=
    Finpartition.indiscrete_parts Finset.univ_nonempty.ne_empty
  rw [hparts]
  simp only [Finset.card_singleton, Nat.reduceSub, pow_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one, Finset.prod_singleton]
  rw [one_mul]
  apply congrArg uniformExpectation
  funext ω
  rw [Fintype.prod_unique]

/-- Centering invariance and constant multilinearity, combined in the exact
normalization needed for a blockwise entry-cumulant estimate. -/
theorem jointCumulantOn_sub_constants_eq_inv_pow_scaled
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    [DecidableEq ι] (Y : ι → Ω → ℝ) (c : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) (a : ℝ) (ha : a ≠ 0) :
    jointCumulantOn (fun j ω ↦ Y j ω - c j) =
      a⁻¹ ^ Fintype.card ι *
        jointCumulantOn (fun j ω ↦ a * Y j ω) := by
  rw [jointCumulantOn_sub_constants Y c hcard]
  let Z : ι → Ω → ℝ := fun j ω ↦ a * Y j ω
  have hscale := jointCumulantOn_const_family_mul (fun _j : ι ↦ a⁻¹) Z
  calc
    jointCumulantOn Y =
        jointCumulantOn (fun j ω ↦ a⁻¹ * Z j ω) := by
      congr 1
      funext j ω
      simp only [Z]
      field_simp
    _ = (∏ _j : ι, a⁻¹) * jointCumulantOn Z := hscale
    _ = a⁻¹ ^ Fintype.card ι * jointCumulantOn Z := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = a⁻¹ ^ Fintype.card ι *
        jointCumulantOn (fun j ω ↦ a * Y j ω) := rfl

/-- A singleton entry block vanishes because every centered projection entry
has zero sign-pair mean. -/
theorem centeredProjection_blockCumulant_eq_zero_of_card_one
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (x : Fin q → WalshIndex m) (B : Finset (Fin q))
    (hB : B.card = 1) :
    jointCumulantOn (fun e : B ↦
      centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1))) = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp hB
  letI : Unique {e : Fin q // e ∈ ({f} : Finset (Fin q))} :=
    { default := ⟨f, Finset.mem_singleton_self f⟩
      uniq := by
        intro e
        apply Subtype.ext
        exact Finset.mem_singleton.mp e.2 }
  rw [jointCumulantOn_unique_eq_uniformExpectation]
  have hdefault :
      ((default : {e : Fin q // e ∈ ({f} : Finset (Fin q))}).1) = f :=
    Finset.mem_singleton.mp
      ((default : {e : Fin q // e ∈ ({f} : Finset (Fin q))}).2)
  rw [hdefault]
  change uniformExpectation (fun d : SignPairSample m ↦
    (randomProjection d.1 d.2 V -
      ((r : ℝ) / walshCard m) •
        (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))
      (x f) (x (cyclicSucc f))) = 0
  exact randomProjection_centered_mean_entry V hV
    (x f) (x (cyclicSucc f))

/-- Enumerate the source labels of one entry block by `Fin B.card`. -/
noncomputable def cyclicBlockSourceLabels {m q : ℕ}
    (x : Fin q → WalshIndex m) (B : Finset (Fin q)) :
    Fin B.card → WalshIndex m :=
  fun f ↦ x (((Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm f).1)

/-- Enumerate the cyclic target labels of one entry block by `Fin B.card`. -/
noncomputable def cyclicBlockTargetLabels {m q : ℕ}
    (x : Fin q → WalshIndex m) (B : Finset (Fin q)) :
    Fin B.card → WalshIndex m :=
  fun f ↦ x (cyclicSucc
    (((Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm f).1))

/-- For a nonsingleton block, centering does not change its cumulant.  Pulling
out one inverse Walsh-cardinality from each coordinate then expresses the
block in the exact normalization used by the joint-entry cumulant lemma. -/
theorem centeredProjection_blockCumulant_eq_inv_pow_scaled
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (x : Fin q → WalshIndex m) (B : Finset (Fin q))
    (hB : 2 ≤ B.card) :
    jointCumulantOn (fun e : B ↦
      centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1))) =
      ((walshCard m : ℝ)⁻¹) ^ B.card *
        jointCumulant
          (fun f : Fin B.card ↦ fun d : SignPairSample m ↦
            (walshCard m : ℝ) * randomProjection d.1 d.2 V
              (cyclicBlockSourceLabels x B f)
              (cyclicBlockTargetLabels x B f)) := by
  classical
  let raw : B → SignPairSample m → ℝ := fun e d ↦
    randomProjection d.1 d.2 V (x e.1) (x (cyclicSucc e.1))
  let constant : B → ℝ := fun e ↦
    (((r : ℝ) / walshCard m) •
      (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))
      (x e.1) (x (cyclicSucc e.1))
  have hcard : Fintype.card B = B.card := Fintype.card_coe B
  have hn : (walshCard m : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : walshCard m ≠ 0)
  let scaled : B → SignPairSample m → ℝ := fun e d ↦
    (walshCard m : ℝ) * raw e d
  have hnormalize := jointCumulantOn_sub_constants_eq_inv_pow_scaled
    raw constant (hcard.symm ▸ hB) (walshCard m : ℝ) hn
  have hleft :
      (fun e : B ↦
        centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1))) =
      (fun e d ↦ raw e d - constant e) := by
    funext e d
    rfl
  rw [hleft, hnormalize, hcard]
  congr 1
  let e : Fin B.card ≃ B :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
  have hreindex := jointCumulantOn_equiv_index e scaled
  simpa only [jointCumulant, scaled, raw, e, cyclicBlockSourceLabels,
    cyclicBlockTargetLabels] using hreindex.symm

/-- Quantitative and XOR-vanishing consequences for one nonsingleton entry
block.  The only external mathematical input is the exact graph-rank
contraction principle already used by the joint-entry cumulant theorem. -/
theorem centeredProjection_blockCumulant_bound_and_vanish
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (x : Fin q → WalshIndex m) (B : Finset (Fin q))
    (hB : 2 ≤ B.card) :
    |jointCumulantOn (fun e : B ↦
      centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1)))| ≤
        ((walshCard m : ℝ)⁻¹) ^ B.card *
          (((2 * B.card : ℕ) : ℝ) ^ (12 * B.card) * r) ∧
    ((∑ f : Fin B.card,
        (cyclicBlockSourceLabels x B f + cyclicBlockTargetLabels x B f)) ≠ 0 →
      jointCumulantOn (fun e : B ↦
        centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1))) = 0) := by
  let i := cyclicBlockSourceLabels x B
  let j := cyclicBlockTargetLabels x B
  have hq : 1 ≤ B.card := by omega
  have hassembly := joint_entry_cumulant_assembly
    hgraph V hV i j hq
  have hnormalize := centeredProjection_blockCumulant_eq_inv_pow_scaled
    V x B hB
  have hinv_nonneg : 0 ≤ (walshCard m : ℝ)⁻¹ := by positivity
  constructor
  · rw [hnormalize, abs_mul, abs_of_nonneg (pow_nonneg hinv_nonneg _)]
    exact mul_le_mul_of_nonneg_left hassembly.1 (pow_nonneg hinv_nonneg _)
  · intro hxor
    rw [hnormalize, hassembly.2.1]
    · ring
    · simpa only [i, j] using hxor

/-- Product bound for every nonsingleton block of one full entry partition.
The exponent `2*p` is obtained from the exact partition cardinality identity,
so no normalization factor is discarded. -/
theorem centeredProjection_partitionCumulantProduct_bound
    (hgraph : GraphRankContractionPrinciple)
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (x : Fin (2 * p) → WalshIndex m)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hnonsingleton : ∀ B ∈ P.parts, 2 ≤ B.card) :
    |∏ B ∈ P.parts,
      jointCumulantOn (fun e : B ↦
        centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1)))| ≤
      ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
        (entryPartitionCumulantConstant P : ℝ) *
        (r : ℝ) ^ P.parts.card := by
  classical
  let nInv : ℝ := (walshCard m : ℝ)⁻¹
  let C : Finset (Fin (2 * p)) → ℝ := fun B ↦
    (((2 * B.card : ℕ) : ℝ) ^ (12 * B.card))
  rw [Finset.abs_prod]
  calc
    (∏ B ∈ P.parts,
        |jointCumulantOn (fun e : B ↦
          centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1)))|) ≤
        ∏ B ∈ P.parts, nInv ^ B.card * (C B * r) := by
      apply Finset.prod_le_prod
      · intro B hB
        exact abs_nonneg _
      · intro B hB
        simpa only [nInv, C, Nat.cast_ofNat] using
          (centeredProjection_blockCumulant_bound_and_vanish
            hgraph V hV x B (hnonsingleton B hB)).1
    _ = (∏ B ∈ P.parts, nInv ^ B.card) *
        (∏ B ∈ P.parts, C B * r) := by
      rw [Finset.prod_mul_distrib]
    _ = nInv ^ (∑ B ∈ P.parts, B.card) *
        ((∏ B ∈ P.parts, C B) * (r : ℝ) ^ P.parts.card) := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib]
      simp
    _ = nInv ^ (2 * p) *
        (entryPartitionCumulantConstant P : ℝ) *
        (r : ℝ) ^ P.parts.card := by
      have hsum : (∑ B ∈ P.parts, B.card) = 2 * p := by
        rw [P.sum_card_parts]
        simp
      have hconstant : (∏ B ∈ P.parts, C B) =
          (entryPartitionCumulantConstant P : ℝ) := by
        simp only [C, entryPartitionCumulantConstant]
        norm_cast
      rw [hsum, hconstant]
      ring
    _ = ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
        (entryPartitionCumulantConstant P : ℝ) *
        (r : ℝ) ^ P.parts.card := rfl

/-- If one nonsingleton entry block violates its XOR constraint, the entire
partition cumulant product vanishes before any triangle inequality. -/
theorem centeredProjection_partitionCumulantProduct_eq_zero_of_block_xor
    (hgraph : GraphRankContractionPrinciple)
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (x : Fin (2 * p) → WalshIndex m)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (B : Finset (Fin (2 * p))) (hBP : B ∈ P.parts)
    (hB : 2 ≤ B.card)
    (hxor : (∑ f : Fin B.card,
      (cyclicBlockSourceLabels x B f + cyclicBlockTargetLabels x B f)) ≠ 0) :
    (∏ C ∈ P.parts,
      jointCumulantOn (fun e : C ↦
        centeredRandomProjectionEntry V (x e.1) (x (cyclicSucc e.1)))) = 0 := by
  apply Finset.prod_eq_zero hBP
  exact (centeredProjection_blockCumulant_bound_and_vanish
    hgraph V hV x B hB).2 hxor

#print axioms signPairExpectation_cyclic_centeredProjection_product_expansion
#print axioms centeredProjection_blockCumulant_eq_zero_of_card_one
#print axioms centeredProjection_blockCumulant_eq_inv_pow_scaled
#print axioms centeredProjection_blockCumulant_bound_and_vanish
#print axioms centeredProjection_partitionCumulantProduct_bound
#print axioms centeredProjection_partitionCumulantProduct_eq_zero_of_block_xor

end

end Problem56
