import Problem56.GraphFiberSplit
import Problem56.IndexedEulerCircuit

/-!
# Exact graph modifications toward the bridgeless conversion

This file isolates the algebraic part of the Mingo--Speicher modification
argument used by `I05`.  It supplies three concrete operations without changing
the original indexed edge type:

* reverse an arbitrary set of indexed edges, transposing exactly those
  rectangular matrices;
* split every vertex into an arbitrary finite nonempty fiber, joining every
  non-root copy to its root by an identity edge (and, crucially, introducing no
  identity self-loop at the root);
* add the vertex weights as diagonal loops before applying the rooted split.

All three operations preserve the scalar contraction exactly and do not
increase the product of Euclidean operator norms.  An indexed Euler circuit
supplies the occurrence routing, and a final finite reindexing step lowers
arbitrary source universes to the `Type 0` witnesses required by `I05`.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

/-! ## Selective edge reversal -/

/-- The edge index is retained together with its uniquely chosen orientation.
The subtype formulation makes rectangular endpoint types definitionally
correct in both orientation branches. -/
abbrev SelectivelyReversedEdge (ε : Type*) (reverse : ε → Bool) :=
  {q : OrientedIndexedEdge ε // q.2 = reverse q.1}

def selectiveReversalEquiv {ε : Type*} (reverse : ε → Bool) :
    ε ≃ SelectivelyReversedEdge ε reverse where
  toFun e := ⟨(e, reverse e), rfl⟩
  invFun q := q.1.1
  left_inv _ := rfl
  right_inv := by
    intro q
    apply Subtype.ext
    rcases q with ⟨⟨e, b⟩, hb⟩
    simp only
    rw [← hb]

def selectivelyReversedSrc {ι ε : Type*} (src dst : ε → ι)
    {reverse : ε → Bool} : SelectivelyReversedEdge ε reverse → ι :=
  fun q => orientedTail src dst q.1

def selectivelyReversedDst {ι ε : Type*} (src dst : ε → ι)
    {reverse : ε → Bool} : SelectivelyReversedEdge ε reverse → ι :=
  fun q => orientedHead src dst q.1

noncomputable def selectivelyReversedMatrix
    {ι ε : Type*} [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    {reverse : ε → Bool} :
    ∀ q : SelectivelyReversedEdge ε reverse, Matrix
      (Fin (dim (selectivelyReversedSrc src dst q)))
      (Fin (dim (selectivelyReversedDst src dst q))) ℝ
  | ⟨(_, false), _⟩ => M _
  | ⟨(_, true), _⟩ => (M _).transpose

theorem graphContraction_selectivelyReverse
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (reverse : ε → Bool) :
    graphContraction dim
        (selectivelyReversedSrc src dst (reverse := reverse))
        (selectivelyReversedDst src dst (reverse := reverse))
        (selectivelyReversedMatrix dim src dst M (reverse := reverse)) w =
      graphContraction dim src dst M w := by
  classical
  simp only [graphContraction]
  apply Finset.sum_congr rfl
  intro labels _
  congr 1
  exact Fintype.prod_equiv (selectiveReversalEquiv reverse).symm
    (fun q : SelectivelyReversedEdge ε reverse =>
      selectivelyReversedMatrix dim src dst M q
        (labels (selectivelyReversedSrc src dst q))
        (labels (selectivelyReversedDst src dst q)))
    (fun e => M e (labels (src e)) (labels (dst e)))
    (fun q => by
      rcases q with ⟨⟨e, b⟩, hb⟩
      cases b <;>
        simp [selectiveReversalEquiv, selectivelyReversedMatrix,
          selectivelyReversedSrc, selectivelyReversedDst, orientedTail,
          orientedHead, Matrix.transpose_apply])

theorem selectivelyReversedMatrix_norm_product_eq
    {ι ε : Type*} [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (reverse : ε → Bool) :
    (∏ q : SelectivelyReversedEdge ε reverse, euclideanOperatorNorm
      (selectivelyReversedMatrix dim src dst M q)) =
      ∏ e, euclideanOperatorNorm (M e) := by
  classical
  exact Fintype.prod_equiv (selectiveReversalEquiv reverse).symm
    (fun q : SelectivelyReversedEdge ε reverse =>
      euclideanOperatorNorm (selectivelyReversedMatrix dim src dst M q))
    (fun e => euclideanOperatorNorm (M e))
    (fun q => by
      rcases q with ⟨⟨e, b⟩, hb⟩
      cases b
      · rfl
      · exact euclideanOperatorNorm_transpose (M e))

/-! ## Root-pruned finite-fiber splitting -/

abbrev ProperFiberCopy {ι : Type*} (copy : ι → Type*)
    (rootCopy : ∀ v, copy v) :=
  {z : FiberSplitVertex copy // z.2 ≠ rootCopy z.1}

abbrev RootedFiberSplitEdge (ε : Type*) {ι : Type*} (copy : ι → Type*)
    (rootCopy : ∀ v, copy v) :=
  ε ⊕ ProperFiberCopy copy rootCopy

def rootedFiberSplitSrc {ι ε : Type*} {copy : ι → Type*}
    (src : ε → ι) (srcCopy : ∀ e, copy (src e))
    (rootCopy : ∀ v, copy v) :
    RootedFiberSplitEdge ε copy rootCopy → FiberSplitVertex copy
  | Sum.inl e => ⟨src e, srcCopy e⟩
  | Sum.inr z => ⟨z.1.1, rootCopy z.1.1⟩

def rootedFiberSplitDst {ι ε : Type*} {copy : ι → Type*}
    (dst : ε → ι) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    RootedFiberSplitEdge ε copy rootCopy → FiberSplitVertex copy
  | Sum.inl e => ⟨dst e, dstCopy e⟩
  | Sum.inr z => z.1

noncomputable def rootedFiberSplitMatrix
    {ι ε : Type*} [DecidableEq ι] {copy : ι → Type*}
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    ∀ e : RootedFiberSplitEdge ε copy rootCopy,
      Matrix (Fin (fiberSplitDim dim
        (rootedFiberSplitSrc src srcCopy rootCopy e)))
        (Fin (fiberSplitDim dim
          (rootedFiberSplitDst dst dstCopy rootCopy e))) ℝ
  | Sum.inl e => M e
  | Sum.inr _ => weightDiagonal (fun _ => 1)

theorem rootedFiberSplitIdentityProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (rootCopy : ∀ v, copy v)
    (labels : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z)) :
    (∏ z : ProperFiberCopy copy rootCopy,
      weightDiagonal (fun _ : Fin (dim z.1.1) => (1 : ℝ))
        (labels ⟨z.1.1, rootCopy z.1.1⟩) (labels z.1)) =
      (by classical
        exact if FiberSplitConsistent dim rootCopy labels then 1 else 0) := by
  classical
  by_cases h : FiberSplitConsistent dim rootCopy labels
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro z _
    rw [show labels ⟨z.1.1, rootCopy z.1.1⟩ = labels z.1 from (h z.1).symm]
    simp [weightDiagonal]
    rfl
  · rw [if_neg h]
    obtain ⟨z, hz⟩ := Classical.not_forall.mp h
    have hzcopy : z.2 ≠ rootCopy z.1 := by
      intro heq
      apply hz
      cases z with
      | mk x c =>
          dsimp only at heq ⊢
          subst c
          rfl
    let z' : ProperFiberCopy copy rootCopy := ⟨z, hzcopy⟩
    apply Finset.prod_eq_zero (Finset.mem_univ z')
    unfold weightDiagonal
    dsimp only [fiberSplitDim]
    rw [if_neg (fun heq => hz heq.symm)]

private theorem rootedFiberSplit_sum_ite_eq_subtype
    {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    (∑ x, if P x then f x else 0) = ∑ x : {x // P x}, f x.1 := by
  classical
  calc
    (∑ x, if P x then f x else 0) =
        ∑ x ∈ (Finset.univ.filter P), f x := by
          simp only [Finset.sum_filter]
    _ = ∑ x : {x // P x}, f x.1 := by
      exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

theorem graphContraction_rootedFiberSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    graphContraction (fiberSplitDim dim)
        (rootedFiberSplitSrc src srcCopy rootCopy)
        (rootedFiberSplitDst dst dstCopy rootCopy)
        (rootedFiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy)
        (fun _ _ => 1) =
      graphContraction dim src dst M (fun _ _ => 1) := by
  classical
  simp only [graphContraction, Finset.prod_const_one, mul_one]
  rw [show (∑ labels : ∀ z : FiberSplitVertex copy,
      Fin (fiberSplitDim dim z),
      ∏ e : RootedFiberSplitEdge ε copy rootCopy,
        rootedFiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e
          (labels (rootedFiberSplitSrc src srcCopy rootCopy e))
          (labels (rootedFiberSplitDst dst dstCopy rootCopy e))) =
      ∑ labels : ∀ z : FiberSplitVertex copy,
        Fin (fiberSplitDim dim z),
        (∏ e : ε, M e (labels ⟨src e, srcCopy e⟩)
          (labels ⟨dst e, dstCopy e⟩)) *
        ∏ z : ProperFiberCopy copy rootCopy,
          weightDiagonal (fun _ : Fin (dim z.1.1) => (1 : ℝ))
            (labels ⟨z.1.1, rootCopy z.1.1⟩) (labels z.1) by
    apply Finset.sum_congr rfl
    intro labels _
    rw [Fintype.prod_sum_type]
    rfl]
  simp_rw [rootedFiberSplitIdentityProduct dim rootCopy]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [rootedFiberSplit_sum_ite_eq_subtype
    (FiberSplitConsistent dim rootCopy)
    (fun labels => ∏ e : ε,
      M e (labels ⟨src e, srcCopy e⟩) (labels ⟨dst e, dstCopy e⟩))]
  apply Fintype.sum_equiv (fiberSplitConsistentEquiv dim rootCopy)
  intro labels
  apply Finset.prod_congr rfl
  intro e _
  rw [labels.2 ⟨src e, srcCopy e⟩, labels.2 ⟨dst e, dstCopy e⟩]
  rfl

theorem rootedFiberSplitMatrix_norm_product_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    (∏ e : RootedFiberSplitEdge ε copy rootCopy,
      euclideanOperatorNorm
        (rootedFiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [Fintype.prod_sum_type]
  simp only [rootedFiberSplitMatrix]
  have hidentity :
      (∏ z : ProperFiberCopy copy rootCopy,
        euclideanOperatorNorm
          (weightDiagonal (fun _ : Fin (dim z.1.1) => (1 : ℝ)))) ≤ 1 := by
    exact Finset.prod_le_one
      (fun z _ => euclideanOperatorNorm_nonneg
        (weightDiagonal (fun _ : Fin (dim z.1.1) => (1 : ℝ))))
      (fun z _ => euclideanOperatorNorm_weightDiagonal_le_one _ (by simp))
  exact mul_le_of_le_one_right
    (Finset.prod_nonneg fun e _ => euclideanOperatorNorm_nonneg (M e)) hidentity

theorem graphContraction_weightLoops_rootedFiberSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (srcCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopSrc src e))
    (dstCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopDst dst e))
    (rootCopy : ∀ v, copy v) :
    graphContraction (fiberSplitDim dim)
        (rootedFiberSplitSrc (weightLoopSrc src) srcCopy rootCopy)
        (rootedFiberSplitDst (weightLoopDst dst) dstCopy rootCopy)
        (rootedFiberSplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
          (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy)
        (fun _ _ => 1) =
      graphContraction dim src dst M w := by
  rw [graphContraction_rootedFiberSplit, graphContraction_weightLoopMatrix]

theorem weightLoops_rootedFiberSplit_norm_product_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (hweight : ∀ v i, |w v i| ≤ 1)
    (srcCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopSrc src e))
    (dstCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopDst dst e))
    (rootCopy : ∀ v, copy v) :
    (∏ e,
      euclideanOperatorNorm
        (rootedFiberSplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
          (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  exact (rootedFiberSplitMatrix_norm_product_le dim
      (weightLoopSrc src) (weightLoopDst dst)
      (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy).trans
    (weightLoopMatrix_norm_product_le dim src dst M w hweight)

/-! ## Euler infrastructure after adding the weight loops -/

theorem graphConnected_weightLoops
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (hconn : GraphConnected src dst) :
    GraphConnected (weightLoopSrc src) (weightLoopDst dst) := by
  intro a b
  induction hconn a b with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      apply ih.tail
      rcases hbc with ⟨e, h | h⟩
      · exact ⟨Sum.inl e, Or.inl h⟩
      · exact ⟨Sum.inl e, Or.inr h⟩

theorem graphDegree_weightLoops
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (v : ι) :
    graphDegree (weightLoopSrc src) (weightLoopDst dst) v =
      graphDegree src dst v + 2 := by
  classical
  have hsrc :
      ((Finset.univ : Finset (WeightLoopEdge ι ε)).filter
        fun e => weightLoopSrc src e = v).card =
        ((Finset.univ : Finset ε).filter fun e => src e = v).card + 1 := by
    rw [show ((Finset.univ : Finset (WeightLoopEdge ι ε)).filter
        fun e => weightLoopSrc src e = v) =
        ((Finset.univ : Finset ε).filter fun e => src e = v).disjSum
          ((Finset.univ : Finset ι).filter fun x => x = v) by
      ext e
      rcases e with e | x
      · rw [Finset.inl_mem_disjSum]
        constructor
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopSrc] using (Finset.mem_filter.mp h).2⟩
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopSrc] using (Finset.mem_filter.mp h).2⟩
      · rw [Finset.inr_mem_disjSum]
        constructor
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopSrc] using (Finset.mem_filter.mp h).2⟩
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopSrc] using (Finset.mem_filter.mp h).2⟩]
    rw [Finset.card_disjSum]
    congr 1
    rw [show ((Finset.univ : Finset ι).filter fun x => x = v) = {v} by
      ext x
      simp [Finset.mem_filter]]
    simp
  have hdst :
      ((Finset.univ : Finset (WeightLoopEdge ι ε)).filter
        fun e => weightLoopDst dst e = v).card =
        ((Finset.univ : Finset ε).filter fun e => dst e = v).card + 1 := by
    rw [show ((Finset.univ : Finset (WeightLoopEdge ι ε)).filter
        fun e => weightLoopDst dst e = v) =
        ((Finset.univ : Finset ε).filter fun e => dst e = v).disjSum
          ((Finset.univ : Finset ι).filter fun x => x = v) by
      ext e
      rcases e with e | x
      · rw [Finset.inl_mem_disjSum]
        constructor
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopDst] using (Finset.mem_filter.mp h).2⟩
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopDst] using (Finset.mem_filter.mp h).2⟩
      · rw [Finset.inr_mem_disjSum]
        constructor
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopDst] using (Finset.mem_filter.mp h).2⟩
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [weightLoopDst] using (Finset.mem_filter.mp h).2⟩]
    rw [Finset.card_disjSum]
    congr 1
    rw [show ((Finset.univ : Finset ι).filter fun x => x = v) = {v} by
      ext x
      simp [Finset.mem_filter]]
    simp
  unfold graphDegree
  rw [hsrc, hdst]
  omega

theorem graphDegree_weightLoops_even
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (heven : ∀ v, Even (graphDegree src dst v)) :
    ∀ v, Even (graphDegree (weightLoopSrc src) (weightLoopDst dst) v) := by
  intro v
  rw [graphDegree_weightLoops]
  exact (heven v).add even_two

theorem graphDegree_weightLoops_pos
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (v : ι) :
    0 < graphDegree (weightLoopSrc src) (weightLoopDst dst) v := by
  rw [graphDegree_weightLoops]
  omega

theorem exists_weightLoop_indexed_euler_circuit
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v)) (u : ι) :
    ∃ C : IndexedEulerCircuit (weightLoopSrc src) (weightLoopDst dst),
      C.trail.steps ≠ [] := by
  exact exists_nonempty_indexed_euler_circuit_of_positive_degree
    (weightLoopSrc src) (weightLoopDst dst)
    (graphConnected_weightLoops src dst hconn)
    (graphDegree_weightLoops_even src dst heven) u
    (graphDegree_weightLoops_pos src dst u)

theorem weightLoop_eulerCircuit_visits
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι)
    (C : IndexedEulerCircuit (weightLoopSrc src) (weightLoopDst dst))
    (v : ι) : C.trail.Visits v := by
  exact C.trail.visits_src_of_edge_mem (Sum.inr v) (C.covers (Sum.inr v))

/-- The weighted Euler circuit may be rotated so that its first oriented
incidence leaves any prescribed vertex.  In particular this retains the
selected `u` rather than choosing an anonymous circuit anchor. -/
theorem exists_weightLoop_indexed_euler_circuit_based_at
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v)) (u : ι) :
    ∃ C : IndexedEulerCircuit (weightLoopSrc src) (weightLoopDst dst),
      C.trail.steps ≠ [] ∧ C.anchor = u := by
  obtain ⟨C, hCne⟩ :=
    exists_weightLoop_indexed_euler_circuit src dst hconn heven u
  have huvisit := weightLoop_eulerCircuit_visits src dst C u
  have hCclosed : C.trail.IsClosed := by
    intro hne
    exact (C.begins_at hne).trans (C.ends_at hne).symm
  obtain ⟨q, hq, hqtail⟩ :=
    C.trail.exists_tail_step_of_visits hCne hCclosed u huvisit
  obtain ⟨R, hRne, hRhead, _, hRclosed, hRmem⟩ :=
    C.trail.exists_rotation_starting_with hCclosed q hq
  let C' : IndexedEulerCircuit (weightLoopSrc src) (weightLoopDst dst) :=
    { anchor := u
      trail := R
      begins_at := by
        intro hne
        rw [hRhead]
        exact hqtail
      ends_at := by
        intro hne
        exact (hRclosed hne).symm.trans ((by rw [hRhead]; exact hqtail) :
          orientedTail (weightLoopSrc src) (weightLoopDst dst)
            (R.steps.head hne) = u)
      covers := by
        intro e
        exact (hRmem e).mpr (C.covers e) }
  exact ⟨C', hRne, rfl⟩

/-! ## Cutting a based Euler circuit at the prescribed output -/

def reverseOrientedEdge {ε : Type*} : OrientedIndexedEdge ε →
    OrientedIndexedEdge ε
  | (e, b) => (e, !b)

@[simp] theorem reverseOrientedEdge_fst {ε : Type*}
    (q : OrientedIndexedEdge ε) : (reverseOrientedEdge q).1 = q.1 := by
  rcases q with ⟨e, b⟩
  rfl

@[simp] theorem orientedTail_reverseOrientedEdge
    {ι ε : Type*} (src dst : ε → ι) (q : OrientedIndexedEdge ε) :
    orientedTail src dst (reverseOrientedEdge q) = orientedHead src dst q := by
  rcases q with ⟨e, b⟩
  cases b <;> rfl

@[simp] theorem orientedHead_reverseOrientedEdge
    {ι ε : Type*} (src dst : ε → ι) (q : OrientedIndexedEdge ε) :
    orientedHead src dst (reverseOrientedEdge q) = orientedTail src dst q := by
  rcases q with ⟨e, b⟩
  cases b <;> rfl

def reverseOrientedList {ε : Type*}
    (L : List (OrientedIndexedEdge ε)) : List (OrientedIndexedEdge ε) :=
  L.reverse.map reverseOrientedEdge

theorem reverseOrientedList_isChain
    {ι ε : Type*} (src dst : ε → ι)
    (L : List (OrientedIndexedEdge ε))
    (hchain : L.IsChain fun a b =>
      orientedHead src dst a = orientedTail src dst b) :
    (reverseOrientedList L).IsChain fun a b =>
      orientedHead src dst a = orientedTail src dst b := by
  rw [reverseOrientedList, List.isChain_map, List.isChain_reverse]
  simpa only [orientedHead_reverseOrientedEdge,
    orientedTail_reverseOrientedEdge, eq_comm] using hchain

theorem reverseOrientedList_ne_nil
    {ε : Type*} {L : List (OrientedIndexedEdge ε)} (hne : L ≠ []) :
    reverseOrientedList L ≠ [] := by
  simpa [reverseOrientedList] using hne

theorem reverseOrientedList_begins_at_old_end
    {ι ε : Type*} (src dst : ε → ι)
    (L : List (OrientedIndexedEdge ε)) (hne : L ≠ []) :
    orientedTail src dst
        ((reverseOrientedList L).head (reverseOrientedList_ne_nil hne)) =
      orientedHead src dst (L.getLast hne) := by
  simp only [reverseOrientedList, List.head_map,
    orientedTail_reverseOrientedEdge, List.head_reverse]

theorem reverseOrientedList_ends_at_old_beginning
    {ι ε : Type*} (src dst : ε → ι)
    (L : List (OrientedIndexedEdge ε)) (hne : L ≠ []) :
    orientedHead src dst
        ((reverseOrientedList L).getLast (reverseOrientedList_ne_nil hne)) =
      orientedTail src dst (L.head hne) := by
  simp only [reverseOrientedList, List.getLast_map,
    orientedHead_reverseOrientedEdge, List.getLast_reverse]

/-- Two directed indexed paths from `input` to `output` whose edge projections
form an exact permutation of the original finite edge type.  Vertices may
repeat in the lists; the later fiber split turns occurrences into distinct
copies. -/
structure IndexedTwoPathCover {ι ε : Type*} [Fintype ε]
    (src dst : ε → ι) (input output : ι) where
  first : List (OrientedIndexedEdge ε)
  second : List (OrientedIndexedEdge ε)
  first_ne : first ≠ []
  second_ne : second ≠ []
  first_chain : first.IsChain fun a b =>
    orientedHead src dst a = orientedTail src dst b
  second_chain : second.IsChain fun a b =>
    orientedHead src dst a = orientedTail src dst b
  first_begins : orientedTail src dst (first.head first_ne) = input
  first_ends : orientedHead src dst (first.getLast first_ne) = output
  second_begins : orientedTail src dst (second.head second_ne) = input
  second_ends : orientedHead src dst (second.getLast second_ne) = output
  edge_perm : ((first ++ second).map Prod.fst).Perm
    (Finset.univ : Finset ε).toList

theorem exists_weightLoop_twoPathCover
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ x, Even (graphDegree src dst x))
    (u v : ι) (huv : u ≠ v) :
    Nonempty (IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst) u v) := by
  obtain ⟨C, hCne, hCbase⟩ :=
    exists_weightLoop_indexed_euler_circuit_based_at src dst hconn heven u
  have hCclosed : C.trail.IsClosed := by
    intro hne
    exact (C.begins_at hne).trans (C.ends_at hne).symm
  have hvvisit := weightLoop_eulerCircuit_visits src dst C v
  obtain ⟨q, hq, hqtail⟩ :=
    C.trail.exists_tail_step_of_visits hCne hCclosed v hvvisit
  obtain ⟨A, B, hsplit⟩ := List.mem_iff_append.mp hq
  have hAne : A ≠ [] := by
    intro hA
    have hbegin := C.begins_at hCne
    have hhead : C.trail.steps.head hCne = q := by
      apply List.head_of_mem_head?
      rw [hsplit, hA]
      simp
    rw [hhead] at hbegin
    exact huv ((hbegin.trans hCbase).symm.trans hqtail)
  let S := q :: B
  have hSne : S ≠ [] := by simp [S]
  have hAllChain : (A ++ S).IsChain fun a b =>
      orientedHead (weightLoopSrc src) (weightLoopDst dst) a =
        orientedTail (weightLoopSrc src) (weightLoopDst dst) b := by
    rw [show A ++ S = C.trail.steps by simpa [S] using hsplit.symm]
    exact C.trail.adjacent
  have hAchain := hAllChain.left_of_append
  have hSchain := hAllChain.right_of_append
  have hAbegins : orientedTail (weightLoopSrc src) (weightLoopDst dst)
      (A.head hAne) = u := by
    have hbegin := C.begins_at hCne
    have hhead : C.trail.steps.head hCne = A.head hAne := by
      apply List.head_of_mem_head?
      rw [hsplit, List.head?_append_of_ne_nil A hAne]
      exact List.head_mem_head? hAne
    rw [hhead] at hbegin
    exact hbegin.trans hCbase
  have hAends : orientedHead (weightLoopSrc src) (weightLoopDst dst)
      (A.getLast hAne) = v := by
    have hcross := (List.isChain_append.mp hAllChain).2.2
    have hlastmem : A.getLast hAne ∈ A.getLast? := by
      rw [List.getLast?_eq_getLast_of_ne_nil hAne]
      simp
    have hqmem : q ∈ S.head? := by simp [S]
    exact (hcross _ hlastmem _ hqmem).trans hqtail
  have hSends : orientedHead (weightLoopSrc src) (weightLoopDst dst)
      (S.getLast hSne) = u := by
    have hend := C.ends_at hCne
    have hASne : A ++ S ≠ [] := by simp [hAne]
    have hsteps : C.trail.steps = A ++ S := by simpa [S] using hsplit
    have hlast : C.trail.steps.getLast hCne = S.getLast hSne :=
      (List.getLast_congr hCne hASne hsteps).trans
        (List.getLast_append_of_ne_nil hASne hSne)
    rw [hlast] at hend
    exact hend.trans hCbase
  let R := reverseOrientedList S
  have hRne : R ≠ [] := reverseOrientedList_ne_nil hSne
  have hRchain := reverseOrientedList_isChain
    (weightLoopSrc src) (weightLoopDst dst) S hSchain
  have hRbegins : orientedTail (weightLoopSrc src) (weightLoopDst dst)
      (R.head hRne) = u := by
    simpa [R] using (reverseOrientedList_begins_at_old_end
      (weightLoopSrc src) (weightLoopDst dst) S hSne).trans hSends
  have hRends : orientedHead (weightLoopSrc src) (weightLoopDst dst)
      (R.getLast hRne) = v := by
    have hrev := reverseOrientedList_ends_at_old_beginning
      (weightLoopSrc src) (weightLoopDst dst) S hSne
    have hShead : orientedTail (weightLoopSrc src) (weightLoopDst dst)
        (S.head hSne) = v := by simpa [S] using hqtail
    simpa [R] using hrev.trans hShead
  have hprojR : R.map Prod.fst = (S.map Prod.fst).reverse := by
    simp [R, reverseOrientedList, List.map_map, Function.comp_def]
  have hpermSteps : ((A ++ R).map Prod.fst).Perm
      (C.trail.steps.map Prod.fst) := by
    rw [List.map_append, hprojR, hsplit, show q :: B = S by rfl,
      List.map_append]
    exact (List.Perm.append_left (A.map Prod.fst)
      (List.reverse_perm (S.map Prod.fst))).trans
      (List.Perm.refl _)
  refine ⟨{
    first := A
    second := R
    first_ne := hAne
    second_ne := hRne
    first_chain := hAchain
    second_chain := by simpa [R] using hRchain
    first_begins := hAbegins
    first_ends := hAends
    second_begins := hRbegins
    second_ends := hRends
    edge_perm := hpermSteps.trans C.edgeProjection_perm_univ_toList }⟩

/-! ## Occurrence vertices carried by the two paths -/

/-- An internal point of a list: neither the point before its first entry nor
the point after its last entry. -/
abbrev PathInterior {alpha : Type*} (L : List alpha) :=
  {p : Fin (L.length + 1) // p.1 ≠ 0 ∧ p.1 ≠ L.length}

/-- Universe-polymorphic version of the preceding occurrence type.  The
parameters are lists rather than the cover itself so no graph data are erased. -/
abbrev TwoPathOccurrenceNode {epsilon : Type*}
    (first second : List (OrientedIndexedEdge epsilon)) :=
  Unit ⊕ PathInterior first ⊕ PathInterior second ⊕ Unit

def twoPathInputNode {epsilon : Type*}
    {first second : List (OrientedIndexedEdge epsilon)} :
    TwoPathOccurrenceNode first second :=
  Sum.inl ()

def twoPathOutputNode {epsilon : Type*}
    {first second : List (OrientedIndexedEdge epsilon)} :
    TwoPathOccurrenceNode first second :=
  Sum.inr (Sum.inr (Sum.inr ()))

def twoPathFirstInteriorNode {epsilon : Type*}
    {first second : List (OrientedIndexedEdge epsilon)}
    (p : PathInterior first) : TwoPathOccurrenceNode first second :=
  Sum.inr (Sum.inl p)

def twoPathSecondInteriorNode {epsilon : Type*}
    {first second : List (OrientedIndexedEdge epsilon)}
    (p : PathInterior second) : TwoPathOccurrenceNode first second :=
  Sum.inr (Sum.inr (Sum.inl p))

/-- The point before entry `i` (or after the last entry) as a node of the first
path. -/
def twoPathFirstPointNode {epsilon : Type*}
    (first second : List (OrientedIndexedEdge epsilon))
    (p : Fin (first.length + 1)) : TwoPathOccurrenceNode first second :=
  if h0 : p.1 = 0 then twoPathInputNode
  else if hlast : p.1 = first.length then twoPathOutputNode
  else twoPathFirstInteriorNode ⟨p, h0, hlast⟩

/-- The corresponding point of the second path. -/
def twoPathSecondPointNode {epsilon : Type*}
    (first second : List (OrientedIndexedEdge epsilon))
    (p : Fin (second.length + 1)) : TwoPathOccurrenceNode first second :=
  if h0 : p.1 = 0 then twoPathInputNode
  else if hlast : p.1 = second.length then twoPathOutputNode
  else twoPathSecondInteriorNode ⟨p, h0, hlast⟩

/-- A numeric topological key.  The first and second interiors occupy disjoint
intervals; the shared input is least and the shared output is greatest. -/
def twoPathNodeRank {epsilon : Type*}
    (first second : List (OrientedIndexedEdge epsilon)) :
    TwoPathOccurrenceNode first second -> Nat
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl p) => p.1.1
  | Sum.inr (Sum.inr (Sum.inl p)) => first.length + p.1.1
  | Sum.inr (Sum.inr (Sum.inr _)) => first.length + second.length

theorem twoPathNodeRank_injective {epsilon : Type*}
    (first second : List (OrientedIndexedEdge epsilon))
    (hfirst : first ≠ []) (hsecond : second ≠ []) :
    Function.Injective (twoPathNodeRank first second) := by
  have hfpos : 0 < first.length := List.length_pos_of_ne_nil hfirst
  have hspos : 0 < second.length := List.length_pos_of_ne_nil hsecond
  intro a b h
  rcases a with a | a
  · rcases b with b | b
    · rfl
    · rcases b with b | b
      · rcases b with ⟨p, hp⟩
        simp only [twoPathNodeRank] at h
        omega
      · rcases b with b | b
        · rcases b with ⟨p, hp⟩
          simp only [twoPathNodeRank] at h
          omega
        · simp only [twoPathNodeRank] at h
          omega
  · rcases a with a | a
    · rcases a with ⟨p, hp⟩
      rcases b with b | b
      · simp only [twoPathNodeRank] at h
        omega
      · rcases b with b | b
        · rcases b with ⟨q, hq⟩
          simp only [twoPathNodeRank] at h
          congr
          exact Fin.ext h
        · rcases b with b | b
          · rcases b with ⟨q, hq⟩
            simp only [twoPathNodeRank] at h
            omega
          · simp only [twoPathNodeRank] at h
            omega
    · rcases a with a | a
      · rcases a with ⟨p, hp⟩
        rcases b with b | b
        · simp only [twoPathNodeRank] at h
          omega
        · rcases b with b | b
          · rcases b with ⟨q, hq⟩
            simp only [twoPathNodeRank] at h
            omega
          · rcases b with b | b
            · rcases b with ⟨q, hq⟩
              simp only [twoPathNodeRank] at h
              congr
              exact Fin.ext (Nat.add_left_cancel h)
            · simp only [twoPathNodeRank] at h
              omega
      · rcases b with b | b
        · simp only [twoPathNodeRank] at h
          omega
        · rcases b with b | b
          · rcases b with ⟨p, hp⟩
            simp only [twoPathNodeRank] at h
            omega
          · rcases b with b | b
            · rcases b with ⟨p, hp⟩
              simp only [twoPathNodeRank] at h
              omega
            · rfl

def orientedPathSourcePoint {epsilon : Type*}
    (L : List (OrientedIndexedEdge epsilon)) (i : Fin L.length) :
    Fin (L.length + 1) :=
  Fin.castSucc i

def orientedPathTargetPoint {epsilon : Type*}
    (L : List (OrientedIndexedEdge epsilon)) (i : Fin L.length) :
    Fin (L.length + 1) :=
  Fin.succ i

/-- Vertex at a path point.  Point zero is the supplied input and every later
point is the head of the preceding oriented edge occurrence. -/
def orientedPathPointVertex {iota epsilon : Type*}
    (src dst : epsilon -> iota) (input : iota)
    (L : List (OrientedIndexedEdge epsilon)) :
    Fin (L.length + 1) -> iota :=
  Fin.cases input (fun i => orientedHead src dst (L.get i))

@[simp] theorem orientedPathPointVertex_zero
    {iota epsilon : Type*} (src dst : epsilon -> iota) (input : iota)
    (L : List (OrientedIndexedEdge epsilon)) :
    orientedPathPointVertex src dst input L ⟨0, by omega⟩ = input := by
  rfl

theorem orientedPathPointVertex_source
    {iota epsilon : Type*} (src dst : epsilon -> iota) (input : iota)
    (L : List (OrientedIndexedEdge epsilon))
    (hne : L ≠ [])
    (hchain : L.IsChain fun a b =>
      orientedHead src dst a = orientedTail src dst b)
    (hbegins : orientedTail src dst (L.head hne) = input)
    (i : Fin L.length) :
    orientedPathPointVertex src dst input L (orientedPathSourcePoint L i) =
      orientedTail src dst (L.get i) := by
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      simp only [orientedPathSourcePoint, orientedPathPointVertex,
        Fin.castSucc_mk]
      rw [L.head_eq_getElem_zero hne] at hbegins
      exact hbegins.symm
  | succ n =>
      rw [show orientedPathSourcePoint L ⟨n + 1, hi⟩ =
          Fin.succ ⟨n, by omega⟩ by apply Fin.ext; rfl]
      simp only [orientedPathPointVertex, Fin.cases_succ]
      have hrel := (List.isChain_iff_getElem.mp hchain) n (by omega)
      simpa only [List.get_eq_getElem] using hrel

@[simp] theorem orientedPathPointVertex_target
    {iota epsilon : Type*} (src dst : epsilon -> iota) (input : iota)
    (L : List (OrientedIndexedEdge epsilon)) (i : Fin L.length) :
    orientedPathPointVertex src dst input L (orientedPathTargetPoint L i) =
      orientedHead src dst (L.get i) := by
  simp [orientedPathTargetPoint, orientedPathPointVertex]

def twoPathNodeVertex
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    TwoPathOccurrenceNode P.first P.second -> iota
  | Sum.inl _ => input
  | Sum.inr (Sum.inl p) =>
      orientedPathPointVertex src dst input P.first p.1
  | Sum.inr (Sum.inr (Sum.inl p)) =>
      orientedPathPointVertex src dst input P.second p.1
  | Sum.inr (Sum.inr (Sum.inr _)) => output

@[simp] theorem twoPathNodeVertex_input
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    twoPathNodeVertex P (twoPathInputNode
      (first := P.first) (second := P.second)) = input := rfl

@[simp] theorem twoPathNodeVertex_output
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    twoPathNodeVertex P (twoPathOutputNode
      (first := P.first) (second := P.second)) = output := rfl

theorem twoPathNodeVertex_firstPoint
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : Fin (P.first.length + 1)) :
    twoPathNodeVertex P (twoPathFirstPointNode P.first P.second p) =
      orientedPathPointVertex src dst input P.first p := by
  unfold twoPathFirstPointNode
  split_ifs with h0 hlast
  · have hp : p = 0 := Fin.ext h0
    rw [hp]
    simp only [twoPathNodeVertex, twoPathInputNode]
    exact (orientedPathPointVertex_zero src dst input P.first).symm
  · have hlen : 0 < P.first.length := List.length_pos_of_ne_nil P.first_ne
    have hp : p = Fin.last P.first.length := Fin.ext hlast
    rw [hp]
    have hlastindex : P.first.length - 1 < P.first.length := by omega
    rw [show Fin.last P.first.length =
        Fin.succ ⟨P.first.length - 1, hlastindex⟩ by
          apply Fin.ext
          simp only [Fin.val_last, Fin.val_succ]
          omega]
    simp only [twoPathNodeVertex, twoPathOutputNode,
      orientedPathPointVertex, Fin.cases_succ]
    rw [List.get_length_sub_one]
    exact P.first_ends.symm
  · rfl

theorem twoPathNodeVertex_secondPoint
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : Fin (P.second.length + 1)) :
    twoPathNodeVertex P (twoPathSecondPointNode P.first P.second p) =
      orientedPathPointVertex src dst input P.second p := by
  unfold twoPathSecondPointNode
  split_ifs with h0 hlast
  · have hp : p = 0 := Fin.ext h0
    rw [hp]
    simp only [twoPathNodeVertex, twoPathInputNode]
    exact (orientedPathPointVertex_zero src dst input P.second).symm
  · have hlen : 0 < P.second.length := List.length_pos_of_ne_nil P.second_ne
    have hp : p = Fin.last P.second.length := Fin.ext hlast
    rw [hp]
    have hlastindex : P.second.length - 1 < P.second.length := by omega
    rw [show Fin.last P.second.length =
        Fin.succ ⟨P.second.length - 1, hlastindex⟩ by
          apply Fin.ext
          simp only [Fin.val_last, Fin.val_succ]
          omega]
    simp only [twoPathNodeVertex, twoPathOutputNode,
      orientedPathPointVertex, Fin.cases_succ]
    rw [List.get_length_sub_one]
    exact P.second_ends.symm
  · rfl

theorem twoPathNodeVertex_firstSource
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (i : Fin P.first.length) :
    twoPathNodeVertex P
        (twoPathFirstPointNode P.first P.second
          (orientedPathSourcePoint P.first i)) =
      orientedTail src dst (P.first.get i) := by
  rw [twoPathNodeVertex_firstPoint]
  exact orientedPathPointVertex_source src dst input P.first P.first_ne
    P.first_chain P.first_begins i

theorem twoPathNodeVertex_firstTarget
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (i : Fin P.first.length) :
    twoPathNodeVertex P
        (twoPathFirstPointNode P.first P.second
          (orientedPathTargetPoint P.first i)) =
      orientedHead src dst (P.first.get i) := by
  rw [twoPathNodeVertex_firstPoint]
  exact orientedPathPointVertex_target src dst input P.first i

theorem twoPathNodeVertex_secondSource
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (i : Fin P.second.length) :
    twoPathNodeVertex P
        (twoPathSecondPointNode P.first P.second
          (orientedPathSourcePoint P.second i)) =
      orientedTail src dst (P.second.get i) := by
  rw [twoPathNodeVertex_secondPoint]
  exact orientedPathPointVertex_source src dst input P.second P.second_ne
    P.second_chain P.second_begins i

theorem twoPathNodeVertex_secondTarget
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (i : Fin P.second.length) :
    twoPathNodeVertex P
        (twoPathSecondPointNode P.first P.second
          (orientedPathTargetPoint P.second i)) =
      orientedHead src dst (P.second.get i) := by
  rw [twoPathNodeVertex_secondPoint]
  exact orientedPathPointVertex_target src dst input P.second i

abbrev TwoPathStepPosition
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :=
  Fin P.first.length ⊕ Fin P.second.length

def twoPathStepAt
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    TwoPathStepPosition P -> OrientedIndexedEdge epsilon
  | Sum.inl i => P.first.get i
  | Sum.inr i => P.second.get i

def twoPathStepSourceNode
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    TwoPathStepPosition P -> TwoPathOccurrenceNode P.first P.second
  | Sum.inl i => twoPathFirstPointNode P.first P.second
      (orientedPathSourcePoint P.first i)
  | Sum.inr i => twoPathSecondPointNode P.first P.second
      (orientedPathSourcePoint P.second i)

def twoPathStepTargetNode
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    TwoPathStepPosition P -> TwoPathOccurrenceNode P.first P.second
  | Sum.inl i => twoPathFirstPointNode P.first P.second
      (orientedPathTargetPoint P.first i)
  | Sum.inr i => twoPathSecondPointNode P.first P.second
      (orientedPathTargetPoint P.second i)

theorem twoPathStepSource_vertex
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : TwoPathStepPosition P) :
    twoPathNodeVertex P (twoPathStepSourceNode P p) =
      orientedTail src dst (twoPathStepAt P p) := by
  rcases p with i | i
  · exact twoPathNodeVertex_firstSource P i
  · exact twoPathNodeVertex_secondSource P i

theorem twoPathStepTarget_vertex
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : TwoPathStepPosition P) :
    twoPathNodeVertex P (twoPathStepTargetNode P p) =
      orientedHead src dst (twoPathStepAt P p) := by
  rcases p with i | i
  · exact twoPathNodeVertex_firstTarget P i
  · exact twoPathNodeVertex_secondTarget P i

theorem twoPathStep_rank_lt
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : TwoPathStepPosition P) :
    twoPathNodeRank P.first P.second (twoPathStepSourceNode P p) <
      twoPathNodeRank P.first P.second (twoPathStepTargetNode P p) := by
  rcases p with i | i
  · rcases i with ⟨i, hi⟩
    unfold twoPathStepSourceNode twoPathStepTargetNode
    unfold orientedPathSourcePoint orientedPathTargetPoint
    unfold twoPathFirstPointNode
    simp only [Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> simp [twoPathNodeRank, twoPathInputNode,
      twoPathOutputNode, twoPathFirstInteriorNode] <;> omega
  · rcases i with ⟨i, hi⟩
    unfold twoPathStepSourceNode twoPathStepTargetNode
    unfold orientedPathSourcePoint orientedPathTargetPoint
    unfold twoPathSecondPointNode
    simp only [Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> simp [twoPathNodeRank, twoPathInputNode,
      twoPathOutputNode, twoPathSecondInteriorNode] <;> omega

private theorem twoPathProjection_nodup
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    ((P.first ++ P.second).map Prod.fst).Nodup := by
  exact P.edge_perm.nodup_iff.mpr (Finset.nodup_toList Finset.univ)

private theorem twoPathProjection_all
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    ∀ e : epsilon, e ∈ (P.first ++ P.second).map Prod.fst := by
  intro e
  exact P.edge_perm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ e))

/-- Exact equivalence between the two path step positions and the indexed edge
type.  Thus parallel edges remain distinct throughout the conversion. -/
noncomputable def twoPathEdgeEquiv
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    TwoPathStepPosition P ≃ epsilon := by
  refine Equiv.ofBijective (fun p => (twoPathStepAt P p).1) ?_
  have hnd : (P.first.map Prod.fst ++ P.second.map Prod.fst).Nodup := by
    simpa only [List.map_append] using twoPathProjection_nodup P
  have hndFirst : (P.first.map Prod.fst).Nodup := hnd.of_append_left
  have hndSecond : (P.second.map Prod.fst).Nodup := hnd.of_append_right
  have hdisjoint : List.Disjoint (P.first.map Prod.fst) (P.second.map Prod.fst) :=
    List.disjoint_of_nodup_append hnd
  constructor
  · intro p q hpq
    rcases p with i | i <;> rcases q with j | j
    · apply congrArg Sum.inl
      change (P.first.get i).1 = (P.first.get j).1 at hpq
      let i' : Fin (P.first.map Prod.fst).length :=
        ⟨i.1, by simpa using i.2⟩
      let j' : Fin (P.first.map Prod.fst).length :=
        ⟨j.1, by simpa using j.2⟩
      have hij : i' = j' := hndFirst.injective_get (by
        simpa [i', j', List.get_eq_getElem] using hpq)
      have hv : i'.1 = j'.1 := congrArg Fin.val hij
      exact Fin.ext hv
    · exfalso
      have hi : (P.first.get i).1 ∈ P.first.map Prod.fst :=
        List.mem_map_of_mem (List.get_mem P.first i)
      have hj : (P.second.get j).1 ∈ P.second.map Prod.fst :=
        List.mem_map_of_mem (List.get_mem P.second j)
      change (P.first.get i).1 = (P.second.get j).1 at hpq
      exact List.disjoint_left.mp hdisjoint hi (hpq.symm ▸ hj)
    · exfalso
      have hj : (P.first.get j).1 ∈ P.first.map Prod.fst :=
        List.mem_map_of_mem (List.get_mem P.first j)
      have hi : (P.second.get i).1 ∈ P.second.map Prod.fst :=
        List.mem_map_of_mem (List.get_mem P.second i)
      change (P.second.get i).1 = (P.first.get j).1 at hpq
      exact List.disjoint_left.mp hdisjoint hj (hpq ▸ hi)
    · apply congrArg Sum.inr
      change (P.second.get i).1 = (P.second.get j).1 at hpq
      let i' : Fin (P.second.map Prod.fst).length :=
        ⟨i.1, by simpa using i.2⟩
      let j' : Fin (P.second.map Prod.fst).length :=
        ⟨j.1, by simpa using j.2⟩
      have hij : i' = j' := hndSecond.injective_get (by
        simpa [i', j', List.get_eq_getElem] using hpq)
      have hv : i'.1 = j'.1 := congrArg Fin.val hij
      exact Fin.ext hv
  · intro e
    have he := twoPathProjection_all P e
    rcases List.mem_map.mp he with ⟨q, hq, hqe⟩
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
      refine ⟨Sum.inl i, ?_⟩
      simpa only [twoPathStepAt, hi] using hqe
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
      refine ⟨Sum.inr i, ?_⟩
      simpa only [twoPathStepAt, hi] using hqe

@[simp] theorem twoPathEdgeEquiv_apply_left
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (i : Fin P.first.length) :
    twoPathEdgeEquiv P (Sum.inl i) = (P.first.get i).1 := by
  simp [twoPathEdgeEquiv, twoPathStepAt]

@[simp] theorem twoPathEdgeEquiv_apply_right
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (i : Fin P.second.length) :
    twoPathEdgeEquiv P (Sum.inr i) = (P.second.get i).1 := by
  simp [twoPathEdgeEquiv, twoPathStepAt]

theorem twoPathStepAt_fst
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : TwoPathStepPosition P) :
    (twoPathStepAt P p).1 = twoPathEdgeEquiv P p := by
  rcases p with i | i
  · exact (twoPathEdgeEquiv_apply_left P i).symm
  · exact (twoPathEdgeEquiv_apply_right P i).symm

abbrev TwoPathCopy
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (x : iota) :=
  {z : TwoPathOccurrenceNode P.first P.second // twoPathNodeVertex P z = x}

def twoPathNodeAsFiber
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (z : TwoPathOccurrenceNode P.first P.second) :
    FiberSplitVertex (TwoPathCopy P) :=
  ⟨twoPathNodeVertex P z, ⟨z, rfl⟩⟩

def twoPathFiberNode
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    FiberSplitVertex (TwoPathCopy P) ->
      TwoPathOccurrenceNode P.first P.second :=
  fun z => z.2.1

@[simp] theorem twoPathFiberNode_nodeAsFiber
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (z : TwoPathOccurrenceNode P.first P.second) :
    twoPathFiberNode P (twoPathNodeAsFiber P z) = z := rfl

theorem twoPathFiberNode_injective
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    Function.Injective (twoPathFiberNode P) := by
  rintro ⟨x, ⟨a, ha⟩⟩ ⟨y, ⟨b, hb⟩⟩ hab
  dsimp only [twoPathFiberNode] at hab
  subst b
  subst x
  subst y
  rfl

def twoPathFiberRank
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    FiberSplitVertex (TwoPathCopy P) -> Nat :=
  fun z => twoPathNodeRank P.first P.second (twoPathFiberNode P z)

theorem twoPathFiberRank_injective
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    Function.Injective (twoPathFiberRank P) := by
  intro a b h
  apply twoPathFiberNode_injective P
  exact twoPathNodeRank_injective P.first P.second P.first_ne P.second_ne h

theorem twoPathCopy_nonempty_weightLoops
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (x : iota) :
    Nonempty (TwoPathCopy P x) := by
  let p := (twoPathEdgeEquiv P).symm (Sum.inr x)
  have hpedge : (twoPathStepAt P p).1 = Sum.inr x :=
    (twoPathStepAt_fst P p).trans
      ((twoPathEdgeEquiv P).apply_symm_apply (Sum.inr x))
  have htail : orientedTail (weightLoopSrc src) (weightLoopDst dst)
      (twoPathStepAt P p) = x := by
    rcases hq : twoPathStepAt P p with ⟨e, b⟩
    rw [hq] at hpedge
    simp only at hpedge
    subst e
    cases b <;> rfl
  exact ⟨⟨twoPathStepSourceNode P p,
    (twoPathStepSource_vertex P p).trans htail⟩⟩

noncomputable def twoPathRootCopy
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (x : iota) : TwoPathCopy P x :=
  Classical.choice (twoPathCopy_nonempty_weightLoops P x)

def twoPathStepSourceCopy
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : TwoPathStepPosition P) :
    TwoPathCopy P (orientedTail src dst (twoPathStepAt P p)) :=
  ⟨twoPathStepSourceNode P p, twoPathStepSource_vertex P p⟩

def twoPathStepTargetCopy
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (p : TwoPathStepPosition P) :
    TwoPathCopy P (orientedHead src dst (twoPathStepAt P p)) :=
  ⟨twoPathStepTargetNode P p, twoPathStepTarget_vertex P p⟩

noncomputable def twoPathSrcNode
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (e : epsilon) :
    TwoPathOccurrenceNode P.first P.second :=
  let p := (twoPathEdgeEquiv P).symm e
  if (twoPathStepAt P p).2 then
    twoPathStepTargetNode P p
  else
    twoPathStepSourceNode P p

noncomputable def twoPathDstNode
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (e : epsilon) :
    TwoPathOccurrenceNode P.first P.second :=
  let p := (twoPathEdgeEquiv P).symm e
  if (twoPathStepAt P p).2 then
    twoPathStepSourceNode P p
  else
    twoPathStepTargetNode P p

theorem twoPathSrcNode_vertex
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (e : epsilon) :
    twoPathNodeVertex P (twoPathSrcNode P e) = src e := by
  let p := (twoPathEdgeEquiv P).symm e
  have hpedge : (twoPathStepAt P p).1 = e :=
    (twoPathStepAt_fst P p).trans ((twoPathEdgeEquiv P).apply_symm_apply e)
  rcases hq : twoPathStepAt P p with ⟨e', b⟩
  rw [hq] at hpedge
  simp only at hpedge
  subst e'
  cases b
  · simpa [twoPathSrcNode, p, hq, orientedTail] using
      twoPathStepSource_vertex P p
  · simpa [twoPathSrcNode, p, hq, orientedHead] using
      twoPathStepTarget_vertex P p

theorem twoPathDstNode_vertex
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) (e : epsilon) :
    twoPathNodeVertex P (twoPathDstNode P e) = dst e := by
  let p := (twoPathEdgeEquiv P).symm e
  have hpedge : (twoPathStepAt P p).1 = e :=
    (twoPathStepAt_fst P p).trans ((twoPathEdgeEquiv P).apply_symm_apply e)
  rcases hq : twoPathStepAt P p with ⟨e', b⟩
  rw [hq] at hpedge
  simp only at hpedge
  subst e'
  cases b
  · simpa [twoPathDstNode, p, hq, orientedHead] using
      twoPathStepTarget_vertex P p
  · simpa [twoPathDstNode, p, hq, orientedTail] using
      twoPathStepSource_vertex P p

noncomputable def twoPathSrcCopy
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    ∀ e : epsilon, TwoPathCopy P (src e) :=
  fun e => ⟨twoPathSrcNode P e, twoPathSrcNode_vertex P e⟩

noncomputable def twoPathDstCopy
    {iota epsilon : Type*} [Fintype epsilon] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    ∀ e : epsilon, TwoPathCopy P (dst e) :=
  fun e => ⟨twoPathDstNode P e, twoPathDstNode_vertex P e⟩

noncomputable def twoPathRootedReverse
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) :
    RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
      (twoPathRootCopy P) -> Bool
  | Sum.inl e => (twoPathStepAt P ((twoPathEdgeEquiv P).symm e)).2
  | Sum.inr z => decide (twoPathFiberRank P z.1 <
      twoPathFiberRank P ⟨z.1.1, twoPathRootCopy P z.1.1⟩)

noncomputable def twoPathTransformedOriginalEdge
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : TwoPathStepPosition P) :
    SelectivelyReversedEdge
      (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
        (twoPathRootCopy P)) (twoPathRootedReverse P) := by
  refine ⟨(Sum.inl (twoPathEdgeEquiv P p), (twoPathStepAt P p).2), ?_⟩
  simp [twoPathRootedReverse]

theorem twoPathTransformedOriginal_src
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : TwoPathStepPosition P) :
    selectivelyReversedSrc
        (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
          (twoPathRootCopy P))
        (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
          (twoPathRootCopy P))
        (twoPathTransformedOriginalEdge P p) =
      twoPathNodeAsFiber P (twoPathStepSourceNode P p) := by
  rcases hq : twoPathStepAt P p with ⟨e, b⟩
  have hedge : e = twoPathEdgeEquiv P p := by
    simpa [hq] using twoPathStepAt_fst P p
  subst e
  cases b
  · simp only [twoPathTransformedOriginalEdge, selectivelyReversedSrc,
      orientedTail]
    have hbool : (twoPathStepAt P p).2 = false := by
      simpa using congrArg Prod.snd hq
    rw [hbool]
    apply twoPathFiberNode_injective P
    simp [rootedFiberSplitSrc, twoPathSrcCopy, twoPathFiberNode,
      twoPathNodeAsFiber, twoPathSrcNode, hbool]
  · simp only [twoPathTransformedOriginalEdge, selectivelyReversedSrc,
      orientedTail]
    have hbool : (twoPathStepAt P p).2 = true := by
      simpa using congrArg Prod.snd hq
    rw [hbool]
    apply twoPathFiberNode_injective P
    simp [rootedFiberSplitDst, twoPathDstCopy, twoPathFiberNode,
      twoPathNodeAsFiber, twoPathDstNode, hbool]

theorem twoPathTransformedOriginal_dst
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : TwoPathStepPosition P) :
    selectivelyReversedDst
        (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
          (twoPathRootCopy P))
        (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
          (twoPathRootCopy P))
        (twoPathTransformedOriginalEdge P p) =
      twoPathNodeAsFiber P (twoPathStepTargetNode P p) := by
  rcases hq : twoPathStepAt P p with ⟨e, b⟩
  have hedge : e = twoPathEdgeEquiv P p := by
    simpa [hq] using twoPathStepAt_fst P p
  subst e
  cases b
  · simp only [twoPathTransformedOriginalEdge, selectivelyReversedDst,
      orientedHead]
    have hbool : (twoPathStepAt P p).2 = false := by
      simpa using congrArg Prod.snd hq
    rw [hbool]
    apply twoPathFiberNode_injective P
    simp [rootedFiberSplitDst, twoPathDstCopy, twoPathFiberNode,
      twoPathNodeAsFiber, twoPathDstNode, hbool]
  · simp only [twoPathTransformedOriginalEdge, selectivelyReversedDst,
      orientedHead]
    have hbool : (twoPathStepAt P p).2 = true := by
      simpa using congrArg Prod.snd hq
    rw [hbool]
    apply twoPathFiberNode_injective P
    simp [rootedFiberSplitSrc, twoPathSrcCopy, twoPathFiberNode,
      twoPathNodeAsFiber, twoPathSrcNode, hbool]

noncomputable def twoPathTransformedIdentityEdge
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output)
    (z : ProperFiberCopy (TwoPathCopy P) (twoPathRootCopy P)) :
    SelectivelyReversedEdge
      (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
        (twoPathRootCopy P)) (twoPathRootedReverse P) :=
  ⟨(Sum.inr z, twoPathRootedReverse P (Sum.inr z)), rfl⟩

theorem twoPathTransformedIdentity_rank_lt
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output)
    (z : ProperFiberCopy (TwoPathCopy P) (twoPathRootCopy P)) :
    twoPathFiberRank P
        (selectivelyReversedSrc
          (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
            (twoPathRootCopy P))
          (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
            (twoPathRootCopy P))
          (twoPathTransformedIdentityEdge P z)) <
      twoPathFiberRank P
        (selectivelyReversedDst
          (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
            (twoPathRootCopy P))
          (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
            (twoPathRootCopy P))
          (twoPathTransformedIdentityEdge P z)) := by
  let root : FiberSplitVertex (TwoPathCopy P) :=
    ⟨z.1.1, twoPathRootCopy P z.1.1⟩
  have hne : z.1 ≠ root := by
    intro h
    have hc : z.1.2 = twoPathRootCopy P z.1.1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact z.2 hc
  have hrankne : twoPathFiberRank P z.1 ≠ twoPathFiberRank P root := by
    intro h
    exact hne (twoPathFiberRank_injective P h)
  by_cases hlt : twoPathFiberRank P z.1 < twoPathFiberRank P root
  · have hrev : twoPathRootedReverse P (Sum.inr z) = true := by
      simp [twoPathRootedReverse, root, hlt]
    simp [twoPathTransformedIdentityEdge, selectivelyReversedSrc,
      selectivelyReversedDst, orientedTail, orientedHead, rootedFiberSplitSrc,
      rootedFiberSplitDst, hrev, root]
    simpa [root] using hlt
  · have hrev : twoPathRootedReverse P (Sum.inr z) = false := by
      simp [twoPathRootedReverse, root, hlt]
    simp [twoPathTransformedIdentityEdge, selectivelyReversedSrc,
      selectivelyReversedDst, orientedTail, orientedHead, rootedFiberSplitSrc,
      rootedFiberSplitDst, hrev, root]
    have hrootlt : twoPathFiberRank P root < twoPathFiberRank P z.1 := by
      omega
    simpa [root] using hrootlt

theorem twoPathTransformedEdge_rank_lt
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output)
    (q : SelectivelyReversedEdge
      (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
        (twoPathRootCopy P)) (twoPathRootedReverse P)) :
    twoPathFiberRank P
        (selectivelyReversedSrc
          (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
            (twoPathRootCopy P))
          (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
            (twoPathRootCopy P)) q) <
      twoPathFiberRank P
        (selectivelyReversedDst
          (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
            (twoPathRootCopy P))
          (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
            (twoPathRootCopy P)) q) := by
  rcases q with ⟨⟨e, b⟩, hb⟩
  rcases e with e | z
  · let p := (twoPathEdgeEquiv P).symm e
    have hpedge : twoPathEdgeEquiv P p = e :=
      (twoPathEdgeEquiv P).apply_symm_apply e
    have hpbool : (twoPathStepAt P p).2 = b := by
      calc
        (twoPathStepAt P p).2 = twoPathRootedReverse P (Sum.inl e) := by
          simp [twoPathRootedReverse, p]
        _ = b := hb.symm
    have hq :
        (⟨((Sum.inl e, b)), hb⟩ : SelectivelyReversedEdge
          (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
            (twoPathRootCopy P)) (twoPathRootedReverse P)) =
          twoPathTransformedOriginalEdge P p := by
      apply Subtype.ext
      apply Prod.ext
      · simp [twoPathTransformedOriginalEdge, hpedge]
      · exact hpbool.symm
    rw [hq, twoPathTransformedOriginal_src,
      twoPathTransformedOriginal_dst]
    exact twoPathStep_rank_lt P p
  · have hq :
        (⟨((Sum.inr z, b)), hb⟩ : SelectivelyReversedEdge
          (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
            (twoPathRootCopy P)) (twoPathRootedReverse P)) =
          twoPathTransformedIdentityEdge P z := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hb
    rw [hq]
    exact twoPathTransformedIdentity_rank_lt P z

noncomputable def twoPathDAGSrc
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) :
    SelectivelyReversedEdge
      (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
        (twoPathRootCopy P)) (twoPathRootedReverse P) ->
      FiberSplitVertex (TwoPathCopy P) :=
  selectivelyReversedSrc
    (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
      (twoPathRootCopy P))
    (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
      (twoPathRootCopy P))

noncomputable def twoPathDAGDst
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) :
    SelectivelyReversedEdge
      (RootedFiberSplitEdge (WeightLoopEdge iota epsilon) (TwoPathCopy P)
        (twoPathRootCopy P)) (twoPathRootedReverse P) ->
      FiberSplitVertex (TwoPathCopy P) :=
  selectivelyReversedDst
    (rootedFiberSplitSrc (weightLoopSrc src) (twoPathSrcCopy P)
      (twoPathRootCopy P))
    (rootedFiberSplitDst (weightLoopDst dst) (twoPathDstCopy P)
      (twoPathRootCopy P))

def twoPathInputFiber
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    FiberSplitVertex (TwoPathCopy P) :=
  twoPathNodeAsFiber P (twoPathInputNode
    (first := P.first) (second := P.second))

def twoPathOutputFiber
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output) :
    FiberSplitVertex (TwoPathCopy P) :=
  twoPathNodeAsFiber P (twoPathOutputNode
    (first := P.first) (second := P.second))

theorem twoPathStep_directedAdjacent
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : TwoPathStepPosition P) :
    directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P)
      (twoPathNodeAsFiber P (twoPathStepSourceNode P p))
      (twoPathNodeAsFiber P (twoPathStepTargetNode P p)) := by
  refine ⟨twoPathTransformedOriginalEdge P p, ?_, ?_⟩
  · exact twoPathTransformedOriginal_src P p
  · exact twoPathTransformedOriginal_dst P p

theorem twoPathFirstPoint_from_input
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : Fin (P.first.length + 1)) :
    twoPathNodeAsFiber P (twoPathFirstPointNode P.first P.second p) =
        twoPathInputFiber P ∨
      Relation.TransGen (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P))
        (twoPathInputFiber P)
        (twoPathNodeAsFiber P
          (twoPathFirstPointNode P.first P.second p)) := by
  induction p using Fin.induction with
  | zero =>
      left
      rfl
  | succ i ih =>
      right
      have hstep := twoPathStep_directedAdjacent P (Sum.inl i)
      have hstep' : directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P)
          (twoPathNodeAsFiber P
            (twoPathFirstPointNode P.first P.second (Fin.castSucc i)))
          (twoPathNodeAsFiber P
            (twoPathFirstPointNode P.first P.second (Fin.succ i))) := by
        simpa [twoPathStepSourceNode, twoPathStepTargetNode,
          orientedPathSourcePoint, orientedPathTargetPoint] using hstep
      rcases ih with h | h
      · rw [h] at hstep'
        exact Relation.TransGen.single hstep'
      · exact h.tail hstep'

theorem twoPathSecondPoint_from_input
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : Fin (P.second.length + 1)) :
    twoPathNodeAsFiber P (twoPathSecondPointNode P.first P.second p) =
        twoPathInputFiber P ∨
      Relation.TransGen (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P))
        (twoPathInputFiber P)
        (twoPathNodeAsFiber P
          (twoPathSecondPointNode P.first P.second p)) := by
  induction p using Fin.induction with
  | zero =>
      left
      rfl
  | succ i ih =>
      right
      have hstep := twoPathStep_directedAdjacent P (Sum.inr i)
      have hstep' : directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P)
          (twoPathNodeAsFiber P
            (twoPathSecondPointNode P.first P.second (Fin.castSucc i)))
          (twoPathNodeAsFiber P
            (twoPathSecondPointNode P.first P.second (Fin.succ i))) := by
        simpa [twoPathStepSourceNode, twoPathStepTargetNode,
          orientedPathSourcePoint, orientedPathTargetPoint] using hstep
      rcases ih with h | h
      · rw [h] at hstep'
        exact Relation.TransGen.single hstep'
      · exact h.tail hstep'

theorem twoPathFirstPoint_to_output
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : Fin (P.first.length + 1)) :
    twoPathNodeAsFiber P (twoPathFirstPointNode P.first P.second p) =
        twoPathOutputFiber P ∨
      Relation.TransGen (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P))
        (twoPathNodeAsFiber P
          (twoPathFirstPointNode P.first P.second p))
        (twoPathOutputFiber P) := by
  induction p using Fin.reverseInduction with
  | last =>
      left
      unfold twoPathFirstPointNode twoPathOutputFiber
      simp [twoPathOutputNode, P.first_ne]
  | cast i ih =>
      right
      have hstep := twoPathStep_directedAdjacent P (Sum.inl i)
      have hstep' : directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P)
          (twoPathNodeAsFiber P
            (twoPathFirstPointNode P.first P.second (Fin.castSucc i)))
          (twoPathNodeAsFiber P
            (twoPathFirstPointNode P.first P.second (Fin.succ i))) := by
        simpa [twoPathStepSourceNode, twoPathStepTargetNode,
          orientedPathSourcePoint, orientedPathTargetPoint] using hstep
      rcases ih with h | h
      · rw [h] at hstep'
        exact Relation.TransGen.single hstep'
      · exact Relation.TransGen.head hstep' h

theorem twoPathSecondPoint_to_output
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (p : Fin (P.second.length + 1)) :
    twoPathNodeAsFiber P (twoPathSecondPointNode P.first P.second p) =
        twoPathOutputFiber P ∨
      Relation.TransGen (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P))
        (twoPathNodeAsFiber P
          (twoPathSecondPointNode P.first P.second p))
        (twoPathOutputFiber P) := by
  induction p using Fin.reverseInduction with
  | last =>
      left
      unfold twoPathSecondPointNode twoPathOutputFiber
      simp [twoPathOutputNode, P.second_ne]
  | cast i ih =>
      right
      have hstep := twoPathStep_directedAdjacent P (Sum.inr i)
      have hstep' : directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P)
          (twoPathNodeAsFiber P
            (twoPathSecondPointNode P.first P.second (Fin.castSucc i)))
          (twoPathNodeAsFiber P
            (twoPathSecondPointNode P.first P.second (Fin.succ i))) := by
        simpa [twoPathStepSourceNode, twoPathStepTargetNode,
          orientedPathSourcePoint, orientedPathTargetPoint] using hstep
      rcases ih with h | h
      · rw [h] at hstep'
        exact Relation.TransGen.single hstep'
      · exact Relation.TransGen.head hstep' h

theorem twoPathFiber_eq_nodeAsFiber
    {iota epsilon : Type*} [Fintype epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover src dst input output)
    (z : FiberSplitVertex (TwoPathCopy P)) :
    z = twoPathNodeAsFiber P (twoPathFiberNode P z) := by
  rcases z with ⟨x, ⟨node, hnode⟩⟩
  dsimp only [twoPathFiberNode]
  subst x
  rfl

theorem twoPathFiber_from_input
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (z : FiberSplitVertex (TwoPathCopy P)) :
    z = twoPathInputFiber P ∨
      Relation.TransGen (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P))
        (twoPathInputFiber P) z := by
  rw [twoPathFiber_eq_nodeAsFiber P z]
  rcases twoPathFiberNode P z with _ | node
  · left
    rfl
  · rcases node with p | node
    · simpa [twoPathFirstPointNode, p.2.1, p.2.2,
        twoPathFirstInteriorNode] using twoPathFirstPoint_from_input P p.1
    · rcases node with p | node
      · simpa [twoPathSecondPointNode, p.2.1, p.2.2,
          twoPathSecondInteriorNode] using twoPathSecondPoint_from_input P p.1
      · have h := twoPathFirstPoint_from_input P (Fin.last P.first.length)
        simpa [twoPathFirstPointNode, twoPathOutputFiber,
          twoPathOutputNode, P.first_ne] using h

theorem twoPathFiber_to_output
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) (z : FiberSplitVertex (TwoPathCopy P)) :
    z = twoPathOutputFiber P ∨
      Relation.TransGen (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P))
        z (twoPathOutputFiber P) := by
  rw [twoPathFiber_eq_nodeAsFiber P z]
  rcases twoPathFiberNode P z with _ | node
  · have h := twoPathFirstPoint_to_output P (0 : Fin (P.first.length + 1))
    simpa [twoPathFirstPointNode, twoPathInputFiber,
      twoPathInputNode] using h
  · rcases node with p | node
    · simpa [twoPathFirstPointNode, p.2.1, p.2.2,
        twoPathFirstInteriorNode] using twoPathFirstPoint_to_output P p.1
    · rcases node with p | node
      · simpa [twoPathSecondPointNode, p.2.1, p.2.2,
          twoPathSecondInteriorNode] using twoPathSecondPoint_to_output P p.1
      · left
        rfl

theorem twoPathTransGen_rank_lt
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) {a b : FiberSplitVertex (TwoPathCopy P)}
    (h : Relation.TransGen
      (directedAdjacent (twoPathDAGSrc P) (twoPathDAGDst P)) a b) :
    twoPathFiberRank P a < twoPathFiberRank P b := by
  induction h with
  | single hab =>
      rcases hab with ⟨e, heSrc, heDst⟩
      rw [← heSrc, ← heDst]
      exact twoPathTransformedEdge_rank_lt P e
  | tail hab hbc ih =>
      rcases hbc with ⟨e, heSrc, heDst⟩
      apply lt_trans ih
      rw [← heSrc, ← heDst]
      exact twoPathTransformedEdge_rank_lt P e

theorem twoPath_mingoAdmissibleDAG
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    {src dst : epsilon -> iota} {input output : iota}
    (P : IndexedTwoPathCover (weightLoopSrc src) (weightLoopDst dst)
      input output) :
    MingoAdmissibleDAG (twoPathDAGSrc P) (twoPathDAGDst P)
      (twoPathInputFiber P) (twoPathOutputFiber P) := by
  refine ⟨?_, twoPathFiber_from_input P, twoPathFiber_to_output P⟩
  intro z hcycle
  exact (Nat.lt_irrefl (twoPathFiberRank P z))
    (twoPathTransGen_rank_lt P hcycle)


/-! ## Scalar contraction as the sum of endpoint entries -/

private theorem sum_sum_sum_indicator_pair
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β]
    (left : γ → α) (right : γ → β) (f : γ → ℝ) :
    (∑ a, ∑ b, ∑ x, if left x = a ∧ right x = b then f x else 0) =
      ∑ x, f x := by
  classical
  calc
    (∑ a, ∑ b, ∑ x,
        if left x = a ∧ right x = b then f x else 0) =
        ∑ a, ∑ x, ∑ b,
          if left x = a ∧ right x = b then f x else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ a, ∑ b,
          if left x = a ∧ right x = b then f x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x, f x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single_of_mem (left x) (Finset.mem_univ _)]
      · rw [Finset.sum_eq_single_of_mem (right x) (Finset.mem_univ _)]
        · simp
        · intro b _ hb
          have hright : ¬right x = b := fun h => hb h.symm
          simp [hright]
      · intro a _ ha
        have hleft : ¬left x = a := fun h => ha h.symm
        simp [hleft]

theorem sum_graphOperator_eq_graphContraction_one
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) :
    (∑ a, ∑ b, graphOperator dim src dst M input output a b) =
      graphContraction dim src dst M (fun _ _ => 1) := by
  classical
  simp only [graphOperator, graphContraction, Finset.prod_const_one, mul_one]
  exact sum_sum_sum_indicator_pair
    (fun labels : ∀ x, Fin (dim x) => labels input)
    (fun labels : ∀ x, Fin (dim x) => labels output)
    (fun labels : ∀ x, Fin (dim x) =>
      ∏ e, M e (labels (src e)) (labels (dst e)))

/-!
The following theorem is deliberately a reduction, not the closure of `I05`.
Its routing hypotheses describe only concrete finite data: copies, incidence
assignments, an arbitrary selective reversal, and the resulting DAG proof.
There is no assumed equality or norm certificate; both are derived above.
-/
theorem bridgelessConversion_of_rootedFiberRouting
    {ι ε : Type} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (hweight : ∀ v i, |w v i| ≤ 1)
    (u v : ι) (huv : u ≠ v)
    {copy : ι → Type} [∀ x, Fintype (copy x)] [∀ x, DecidableEq (copy x)]
    (srcCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopSrc src e))
    (dstCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopDst dst e))
    (rootCopy : ∀ x, copy x)
    (reverse : RootedFiberSplitEdge (WeightLoopEdge ι ε) copy rootCopy → Bool)
    (input output : FiberSplitVertex copy)
    (hinput : input.1 = u) (houtput : output.1 = v)
    (hdag : MingoAdmissibleDAG
      (selectivelyReversedSrc (reverse := reverse)
        (rootedFiberSplitSrc (weightLoopSrc src) srcCopy rootCopy)
        (rootedFiberSplitDst (weightLoopDst dst) dstCopy rootCopy))
      (selectivelyReversedDst (reverse := reverse)
        (rootedFiberSplitSrc (weightLoopSrc src) srcCopy rootCopy)
        (rootedFiberSplitDst (weightLoopDst dst) dstCopy rootCopy))
      input output) :
    ∃ (ι' ε' : Type) (_ : Fintype ι') (_ : Fintype ε')
      (_ : DecidableEq ι') (dim' : ι' → ℕ) (src' dst' : ε' → ι')
      (M' : ∀ e, Matrix (Fin (dim' (src' e))) (Fin (dim' (dst' e))) ℝ)
      (input output : ι'),
      input ≠ output ∧ MingoAdmissibleDAG src' dst' input output ∧
      dim' input = dim u ∧ dim' output = dim v ∧
      graphContraction dim src dst M w =
        ∑ a, ∑ b, graphOperator dim' src' dst' M' input output a b ∧
      (∏ e, euclideanOperatorNorm (M' e)) ≤
        ∏ e, euclideanOperatorNorm (M e) := by
  classical
  let oldSrc := rootedFiberSplitSrc (weightLoopSrc src) srcCopy rootCopy
  let oldDst := rootedFiberSplitDst (weightLoopDst dst) dstCopy rootCopy
  let oldM := rootedFiberSplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
    (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy
  let newSrc := selectivelyReversedSrc (reverse := reverse) oldSrc oldDst
  let newDst := selectivelyReversedDst (reverse := reverse) oldSrc oldDst
  let newM := selectivelyReversedMatrix (fiberSplitDim dim) oldSrc oldDst oldM
    (reverse := reverse)
  refine ⟨FiberSplitVertex copy,
    SelectivelyReversedEdge
      (RootedFiberSplitEdge (WeightLoopEdge ι ε) copy rootCopy) reverse,
    inferInstance, inferInstance, inferInstance,
    fiberSplitDim dim, newSrc, newDst, newM, input, output, ?_⟩
  have hne : input ≠ output := by
    intro heq
    have : u = v := by rw [← hinput, ← houtput, heq]
    exact huv this
  refine ⟨hne, hdag, ?_, ?_, ?_, ?_⟩
  · simpa [fiberSplitDim] using congrArg dim hinput
  · simpa [fiberSplitDim] using congrArg dim houtput
  · rw [← graphContraction_weightLoops_rootedFiberSplit dim src dst M w
      srcCopy dstCopy rootCopy]
    rw [← graphContraction_selectivelyReverse
      (fiberSplitDim dim) oldSrc oldDst oldM (fun _ _ => 1) reverse]
    exact (sum_graphOperator_eq_graphContraction_one
      (fiberSplitDim dim) newSrc newDst newM input output).symm
  · rw [selectivelyReversedMatrix_norm_product_eq]
    exact weightLoops_rootedFiberSplit_norm_product_le dim src dst M w hweight
      srcCopy dstCopy rootCopy

theorem bridgelessConversion_type0
    {iota epsilon : Type} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota] [DecidableEq epsilon]
    (dim : iota → ℕ) (src dst : epsilon → iota)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ x, Fin (dim x) → ℝ)
    (hconn : GraphConnected src dst)
    (heven : ∀ x, Even (graphDegree src dst x))
    (_hpositive : ∀ x, 0 < graphDegree src dst x)
    (hweight : ∀ x i, |w x i| ≤ 1)
    (u v : iota) (huv : u ≠ v) :
    ∃ (iota' epsilon' : Type) (_ : Fintype iota') (_ : Fintype epsilon')
      (_ : DecidableEq iota') (dim' : iota' → ℕ)
      (src' dst' : epsilon' → iota')
      (M' : ∀ e, Matrix (Fin (dim' (src' e))) (Fin (dim' (dst' e))) ℝ)
      (input output : iota'),
      input ≠ output ∧ MingoAdmissibleDAG src' dst' input output ∧
      dim' input = dim u ∧ dim' output = dim v ∧
      graphContraction dim src dst M w =
        ∑ a, ∑ b, graphOperator dim' src' dst' M' input output a b ∧
      (∏ e, euclideanOperatorNorm (M' e)) ≤
        ∏ e, euclideanOperatorNorm (M e) := by
  classical
  let P := Classical.choice
    (exists_weightLoop_twoPathCover src dst hconn heven u v huv)
  exact bridgelessConversion_of_rootedFiberRouting dim src dst M w hweight u v
    huv (twoPathSrcCopy P) (twoPathDstCopy P) (twoPathRootCopy P)
    (twoPathRootedReverse P) (twoPathInputFiber P) (twoPathOutputFiber P)
    rfl rfl (twoPath_mingoAdmissibleDAG P)

/-! ## Lowering arbitrary finite source universes -/

def graphReindexDim {iota0 iota : Type*} (V : iota0 ≃ iota)
    (dim : iota → ℕ) : iota0 → ℕ :=
  fun x ↦ dim (V x)

def graphReindexSrc {iota0 iota epsilon0 epsilon : Type*}
    (V : iota0 ≃ iota) (E : epsilon0 ≃ epsilon)
    (src : epsilon → iota) : epsilon0 → iota0 :=
  fun e ↦ V.symm (src (E e))

noncomputable def graphReindexMatrix
    {iota0 iota epsilon0 epsilon : Type*}
    (V : iota0 ≃ iota) (E : epsilon0 ≃ epsilon)
    (dim : iota → ℕ) (src dst : epsilon → iota)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ) :
    ∀ e, Matrix
      (Fin (graphReindexDim V dim (graphReindexSrc V E src e)))
      (Fin (graphReindexDim V dim (graphReindexSrc V E dst e))) ℝ :=
  fun e a b ↦ M (E e)
    (V.apply_symm_apply (src (E e)) ▸ a)
    (V.apply_symm_apply (dst (E e)) ▸ b)

def graphReindexWeight {iota0 iota : Type*} (V : iota0 ≃ iota)
    (dim : iota → ℕ) (w : ∀ x, Fin (dim x) → ℝ) :
    ∀ x, Fin (graphReindexDim V dim x) → ℝ :=
  fun x ↦ w (V x)

theorem graphContraction_reindex
    {iota0 iota epsilon0 epsilon : Type*}
    [Fintype iota0] [Fintype iota] [Fintype epsilon0] [Fintype epsilon]
    [DecidableEq iota0] [DecidableEq iota]
    (V : iota0 ≃ iota) (E : epsilon0 ≃ epsilon)
    (dim : iota → ℕ) (src dst : epsilon → iota)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ x, Fin (dim x) → ℝ) :
    graphContraction (graphReindexDim V dim)
      (graphReindexSrc V E src) (graphReindexSrc V E dst)
      (graphReindexMatrix V E dim src dst M)
      (graphReindexWeight V dim w) =
      graphContraction dim src dst M w := by
  classical
  unfold graphContraction
  let L := Equiv.piCongrLeft (fun x : iota ↦ Fin (dim x)) V
  apply Fintype.sum_equiv L
  intro labels
  dsimp only [L]
  congr 1
  · apply Fintype.prod_equiv E
    intro e
    rw [Equiv.piCongrLeft_apply, Equiv.piCongrLeft_apply]
    simp [graphReindexSrc, graphReindexMatrix]
  · apply Fintype.prod_equiv V
    intro x
    simp [graphReindexWeight]

theorem euclideanNorm_comp_equiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (x : beta → ℝ) :
    euclideanNorm (x ∘ e) = euclideanNorm x := by
  unfold euclideanNorm
  congr 1
  exact Equiv.sum_comp e (fun i ↦ x i ^ 2)

theorem euclideanOperatorNorm_reindex
    {alpha0 alpha beta0 beta : Type*}
    [Fintype alpha0] [Fintype alpha] [Fintype beta0] [Fintype beta]
    (R : alpha0 ≃ alpha) (C : beta0 ≃ beta) (A : Matrix alpha beta ℝ) :
    euclideanOperatorNorm (Matrix.reindex R.symm C.symm A) =
      euclideanOperatorNorm A := by
  unfold euclideanOperatorNorm
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let y : beta → ℝ := x ∘ C.symm
    refine ⟨y, ?_, ?_⟩
    · exact (euclideanNorm_comp_equiv C.symm x).trans hx
    · rw [← euclideanNorm_comp_equiv R (A.mulVec y)]
      congr 1
      funext i
      simp only [Function.comp_apply, Matrix.mulVec, dotProduct,
        Matrix.reindex_apply]
      apply Fintype.sum_equiv C
      intro j
      simp [y]
  · rintro ⟨y, hy, rfl⟩
    let x : beta0 → ℝ := y ∘ C
    refine ⟨x, ?_, ?_⟩
    · exact (euclideanNorm_comp_equiv C y).trans hy
    · rw [← euclideanNorm_comp_equiv R (A.mulVec y)]
      congr 1
      funext i
      simp only [Function.comp_apply, Matrix.mulVec, dotProduct,
        Matrix.reindex_apply]
      symm
      apply Fintype.sum_equiv C
      intro j
      simp [x]

theorem fin_transport_val {gamma : Type*} (dim : gamma → ℕ)
    {a b : gamma} (h : a = b) (i : Fin (dim a)) :
    (h ▸ i).1 = i.1 := by
  subst b
  rfl

theorem fin_equivCast_congrArg_val {gamma : Type*} (dim : gamma → ℕ)
    {x y : gamma} (h : x = y) (i : Fin (dim x)) :
    (Equiv.cast (congrArg Fin (congrArg dim h)) i : Fin (dim y)).1 = i.1 := by
  subst y
  rfl

theorem graphDegree_reindex
    {iota0 iota epsilon0 epsilon : Type*}
    [Fintype epsilon0] [Fintype epsilon]
    [DecidableEq iota0] [DecidableEq iota]
    (V : iota0 ≃ iota) (E : epsilon0 ≃ epsilon)
    (src dst : epsilon → iota) (x : iota0) :
    graphDegree (graphReindexSrc V E src) (graphReindexSrc V E dst) x =
      graphDegree src dst (V x) := by
  classical
  unfold graphDegree
  congr 1
  · let es : {e : epsilon0 // graphReindexSrc V E src e = x} ≃
        {e : epsilon // src e = V x} :=
      Equiv.subtypeEquiv E (by
        intro e
        simp only [graphReindexSrc]
        constructor
        · intro h
          simpa using congrArg V h
        · intro h
          apply V.injective
          simpa using h)
    rw [← Fintype.card_subtype
      (fun e : epsilon0 ↦ graphReindexSrc V E src e = x)]
    rw [← Fintype.card_subtype (fun e : epsilon ↦ src e = V x)]
    exact Fintype.card_congr es
  · let ed : {e : epsilon0 // graphReindexSrc V E dst e = x} ≃
        {e : epsilon // dst e = V x} :=
      Equiv.subtypeEquiv E (by
        intro e
        simp only [graphReindexSrc]
        constructor
        · intro h
          simpa using congrArg V h
        · intro h
          apply V.injective
          simpa using h)
    rw [← Fintype.card_subtype
      (fun e : epsilon0 ↦ graphReindexSrc V E dst e = x)]
    rw [← Fintype.card_subtype (fun e : epsilon ↦ dst e = V x)]
    exact Fintype.card_congr ed

theorem graphConnected_reindex
    {iota0 iota epsilon0 epsilon : Type*}
    (V : iota0 ≃ iota) (E : epsilon0 ≃ epsilon)
    (src dst : epsilon → iota) (hconn : GraphConnected src dst) :
    GraphConnected (graphReindexSrc V E src) (graphReindexSrc V E dst) := by
  intro a b
  have h := hconn (V a) (V b)
  have hm := h.lift (p := graphAdjacent
    (graphReindexSrc V E src) (graphReindexSrc V E dst))
    V.symm (fun x y hxy ↦ ?_)
  · change Relation.ReflTransGen
      (graphAdjacent (graphReindexSrc V E src) (graphReindexSrc V E dst))
      (V.symm (V a)) (V.symm (V b)) at hm
    simpa using hm
  · rcases hxy with ⟨e, h | h⟩
    · exact ⟨E.symm e, Or.inl ⟨by simpa [graphReindexSrc] using h.1,
        by simpa [graphReindexSrc] using h.2⟩⟩
    · exact ⟨E.symm e, Or.inr ⟨by simpa [graphReindexSrc] using h.1,
        by simpa [graphReindexSrc] using h.2⟩⟩

theorem graphMatrixNormProduct_reindex
    {iota0 iota epsilon0 epsilon : Type*}
    [Fintype iota0] [Fintype iota] [Fintype epsilon0] [Fintype epsilon]
    [DecidableEq iota0] [DecidableEq iota]
    (V : iota0 ≃ iota) (E : epsilon0 ≃ epsilon)
    (dim : iota → ℕ) (src dst : epsilon → iota)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ) :
    (∏ e, euclideanOperatorNorm (graphReindexMatrix V E dim src dst M e)) =
      ∏ e, euclideanOperatorNorm (M e) := by
  apply Fintype.prod_equiv E
  intro e
  let R : Fin (graphReindexDim V dim (graphReindexSrc V E src e)) ≃
      Fin (dim (src (E e))) := Equiv.cast
        (congrArg Fin (congrArg dim (V.apply_symm_apply (src (E e)))))
  let C : Fin (graphReindexDim V dim (graphReindexSrc V E dst e)) ≃
      Fin (dim (dst (E e))) := Equiv.cast
        (congrArg Fin (congrArg dim (V.apply_symm_apply (dst (E e)))))
  rw [← euclideanOperatorNorm_reindex R C (M (E e))]
  congr 1
  ext a b
  change Fin (dim (V (V.symm (src (E e))))) at a
  change Fin (dim (V (V.symm (dst (E e))))) at b
  simp [R, C, graphReindexMatrix, Matrix.reindex_apply]
  congr 2
  · apply Fin.ext
    calc
      (V.apply_symm_apply (src (E e)) ▸ a).1 = a.1 :=
        fin_transport_val dim (V.apply_symm_apply (src (E e))) a
      _ = (R a).1 :=
        (fin_equivCast_congrArg_val dim
          (V.apply_symm_apply (src (E e))) a).symm
  · apply Fin.ext
    calc
      (V.apply_symm_apply (dst (E e)) ▸ b).1 = b.1 :=
        fin_transport_val dim (V.apply_symm_apply (dst (E e))) b
      _ = (C b).1 :=
        (fin_equivCast_congrArg_val dim
          (V.apply_symm_apply (dst (E e))) b).symm

/-- The exact universe-polymorphic I05 content.  The finite source graph is
first reindexed by `Fin` types, so the constructed witnesses inhabit `Type 0`
as required by the public statement. -/
theorem mingo_speicher_bridgeless_conversion
    {iota epsilon : Type*} [Fintype iota] [Fintype epsilon]
    [DecidableEq iota]
    (dim : iota → ℕ) (src dst : epsilon → iota)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ x, Fin (dim x) → ℝ)
    (hconn : GraphConnected src dst)
    (heven : ∀ x, Even (graphDegree src dst x))
    (hpositive : ∀ x, 0 < graphDegree src dst x)
    (hweight : ∀ x i, |w x i| ≤ 1)
    (u v : iota) (huv : u ≠ v) :
    ∃ (iota' epsilon' : Type) (_ : Fintype iota') (_ : Fintype epsilon')
      (_ : DecidableEq iota') (dim' : iota' → ℕ)
      (src' dst' : epsilon' → iota')
      (M' : ∀ e, Matrix (Fin (dim' (src' e))) (Fin (dim' (dst' e))) ℝ)
      (input output : iota'),
      input ≠ output ∧ MingoAdmissibleDAG src' dst' input output ∧
      dim' input = dim u ∧ dim' output = dim v ∧
      graphContraction dim src dst M w =
        ∑ a, ∑ b, graphOperator dim' src' dst' M' input output a b ∧
      (∏ e, euclideanOperatorNorm (M' e)) ≤
        ∏ e, euclideanOperatorNorm (M e) := by
  classical
  let V : Fin (Fintype.card iota) ≃ iota := (Fintype.equivFin iota).symm
  let E : Fin (Fintype.card epsilon) ≃ epsilon :=
    (Fintype.equivFin epsilon).symm
  let dim0 := graphReindexDim V dim
  let src0 := graphReindexSrc V E src
  let dst0 := graphReindexSrc V E dst
  let M0 := graphReindexMatrix V E dim src dst M
  let w0 := graphReindexWeight V dim w
  have hconn0 : GraphConnected src0 dst0 :=
    graphConnected_reindex V E src dst hconn
  have heven0 : ∀ x, Even (graphDegree src0 dst0 x) := by
    intro x
    rw [graphDegree_reindex V E src dst x]
    exact heven (V x)
  have hpositive0 : ∀ x, 0 < graphDegree src0 dst0 x := by
    intro x
    rw [graphDegree_reindex V E src dst x]
    exact hpositive (V x)
  have hweight0 : ∀ x i, |w0 x i| ≤ 1 := by
    intro x i
    exact hweight (V x) i
  have huv0 : V.symm u ≠ V.symm v := V.symm.injective.ne huv
  obtain ⟨iota', epsilon', fintypeIota', fintypeEpsilon', decIota',
      dim', src', dst', M', input', output', hne, hdag, hdimInput,
      hdimOutput, hcontraction, hnorm⟩ :=
    bridgelessConversion_type0 dim0 src0 dst0 M0 w0 hconn0 heven0
      hpositive0 hweight0 (V.symm u) (V.symm v) huv0
  refine ⟨iota', epsilon', fintypeIota', fintypeEpsilon', decIota',
    dim', src', dst', M', input', output', hne, hdag, ?_, ?_, ?_, ?_⟩
  · simpa [dim0, graphReindexDim] using hdimInput
  · simpa [dim0, graphReindexDim] using hdimOutput
  · rw [← hcontraction]
    exact (show graphContraction dim0 src0 dst0 M0 w0 =
      graphContraction dim src dst M w from
        graphContraction_reindex V E dim src dst M w).symm
  · exact hnorm.trans_eq
      (graphMatrixNormProduct_reindex V E dim src dst M)

end Problem56

#print axioms Problem56.graphContraction_selectivelyReverse
#print axioms Problem56.selectivelyReversedMatrix_norm_product_eq
#print axioms Problem56.rootedFiberSplitIdentityProduct
#print axioms Problem56.graphContraction_rootedFiberSplit
#print axioms Problem56.rootedFiberSplitMatrix_norm_product_le
#print axioms Problem56.graphContraction_weightLoops_rootedFiberSplit
#print axioms Problem56.weightLoops_rootedFiberSplit_norm_product_le
#print axioms Problem56.graphConnected_weightLoops
#print axioms Problem56.graphDegree_weightLoops
#print axioms Problem56.exists_weightLoop_indexed_euler_circuit_based_at
#print axioms Problem56.reverseOrientedList_isChain
#print axioms Problem56.exists_weightLoop_twoPathCover
#print axioms Problem56.sum_graphOperator_eq_graphContraction_one
#print axioms Problem56.bridgelessConversion_of_rootedFiberRouting
#print axioms Problem56.twoPath_mingoAdmissibleDAG
#print axioms Problem56.bridgelessConversion_type0
#print axioms Problem56.graphContraction_reindex
#print axioms Problem56.graphMatrixNormProduct_reindex
#print axioms Problem56.mingo_speicher_bridgeless_conversion
