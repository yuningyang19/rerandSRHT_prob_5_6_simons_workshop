import Problem56.GraphVertexSplit

/-!
The arbitrary finite-copy version of the exact vertex-splitting operation.
For every old vertex `v`, a finite nonempty fiber `copy v` supplies its copies.
One chosen root copy is joined by an identity edge to every copy.  Original
edge incidences may be routed to arbitrary copies of their old endpoints.

This representation is designed for the eventual Euler/ear construction in
I05: path occurrences become the copy fibers, while the identity stars recover
the old single label at every vertex.  All endpoint dimensions remain
definitionally correct, including rectangular original matrices.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

abbrev FiberSplitVertex {ι : Type*} (copy : ι → Type*) := Σ v, copy v
abbrev FiberSplitEdge (ε : Type*) {ι : Type*} (copy : ι → Type*) :=
  ε ⊕ FiberSplitVertex copy

def fiberSplitDim {ι : Type*} {copy : ι → Type*} (dim : ι → ℕ) :
    FiberSplitVertex copy → ℕ :=
  fun z => dim z.1

def fiberSplitSrc {ι ε : Type*} {copy : ι → Type*}
    (src : ε → ι) (srcCopy : ∀ e, copy (src e))
    (rootCopy : ∀ v, copy v) :
    FiberSplitEdge ε copy → FiberSplitVertex copy
  | Sum.inl e => ⟨src e, srcCopy e⟩
  | Sum.inr z => ⟨z.1, rootCopy z.1⟩

def fiberSplitDst {ι ε : Type*} {copy : ι → Type*}
    (dst : ε → ι) (dstCopy : ∀ e, copy (dst e)) :
    FiberSplitEdge ε copy → FiberSplitVertex copy
  | Sum.inl e => ⟨dst e, dstCopy e⟩
  | Sum.inr z => z

noncomputable def fiberSplitMatrix
    {ι ε : Type*} [DecidableEq ι] {copy : ι → Type*}
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    ∀ e : FiberSplitEdge ε copy,
      Matrix (Fin (fiberSplitDim dim
        (fiberSplitSrc src srcCopy rootCopy e)))
        (Fin (fiberSplitDim dim (fiberSplitDst dst dstCopy e))) ℝ
  | Sum.inl e => M e
  | Sum.inr _ => weightDiagonal (fun _ => 1)

def FiberSplitConsistent {ι : Type*} {copy : ι → Type*}
    (dim : ι → ℕ) (rootCopy : ∀ v, copy v)
    (labels : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z)) : Prop :=
  ∀ z, labels z = labels ⟨z.1, rootCopy z.1⟩

def fiberSplitDecode {ι : Type*} {copy : ι → Type*}
    (dim : ι → ℕ) (rootCopy : ∀ v, copy v)
    (labels : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z)) :
    ∀ v, Fin (dim v) :=
  fun v => labels ⟨v, rootCopy v⟩

noncomputable def fiberSplitConsistentEquiv
    {ι : Type*} [Fintype ι] {copy : ι → Type*}
    [∀ v, Fintype (copy v)]
    (dim : ι → ℕ) (rootCopy : ∀ v, copy v) :
    {labels : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z) //
      FiberSplitConsistent dim rootCopy labels} ≃ (∀ v, Fin (dim v)) where
  toFun labels := fiberSplitDecode dim rootCopy labels.1
  invFun labels := ⟨fun z => labels z.1, fun _ => rfl⟩
  left_inv := by
    intro labels
    apply Subtype.ext
    funext z
    exact (labels.2 z).symm
  right_inv := by
    intro labels
    rfl

private theorem fiberSplit_sum_ite_eq_subtype
    {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    (∑ x, if P x then f x else 0) = ∑ x : {x // P x}, f x.1 := by
  classical
  calc
    (∑ x, if P x then f x else 0) =
        ∑ x ∈ (Finset.univ.filter P), f x := by
          simp only [Finset.sum_filter, Finset.mem_univ, if_true]
    _ = ∑ x : {x // P x}, f x.1 := by
      exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

theorem fiberSplitIdentityProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (rootCopy : ∀ v, copy v)
    (labels : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z)) :
    (∏ z : FiberSplitVertex copy,
      weightDiagonal (fun _ : Fin (dim z.1) => (1 : ℝ))
        (labels ⟨z.1, rootCopy z.1⟩) (labels z)) =
      (by classical
        exact if FiberSplitConsistent dim rootCopy labels then 1 else 0) := by
  classical
  by_cases h : FiberSplitConsistent dim rootCopy labels
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro z _
    simp [weightDiagonal, h z]
    rfl
  · rw [if_neg h]
    obtain ⟨z, hz⟩ := Classical.not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ z)
    unfold weightDiagonal
    dsimp only [fiberSplitDim] at hz ⊢
    rw [if_neg (fun heq => hz heq.symm)]

theorem graphContraction_fiberSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    graphContraction (fiberSplitDim dim)
        (fiberSplitSrc src srcCopy rootCopy) (fiberSplitDst dst dstCopy)
        (fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy)
        (fun _ _ => 1) =
      graphContraction dim src dst M (fun _ _ => 1) := by
  classical
  simp only [graphContraction, Finset.prod_const_one, mul_one]
  rw [show (∑ labels : ∀ z : FiberSplitVertex copy,
      Fin (fiberSplitDim dim z),
      ∏ e : FiberSplitEdge ε copy,
        fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e
          (labels (fiberSplitSrc src srcCopy rootCopy e))
          (labels (fiberSplitDst dst dstCopy e))) =
      ∑ labels : ∀ z : FiberSplitVertex copy,
        Fin (fiberSplitDim dim z),
        (∏ e : ε, M e (labels ⟨src e, srcCopy e⟩)
          (labels ⟨dst e, dstCopy e⟩)) *
        ∏ z : FiberSplitVertex copy,
          weightDiagonal (fun _ : Fin (dim z.1) => (1 : ℝ))
            (labels ⟨z.1, rootCopy z.1⟩) (labels z) by
    apply Finset.sum_congr rfl
    intro labels _
    rw [Fintype.prod_sum_type]
    rfl]
  simp_rw [fiberSplitIdentityProduct dim rootCopy]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [fiberSplit_sum_ite_eq_subtype
    (FiberSplitConsistent dim rootCopy)
    (fun labels => ∏ e : ε,
      M e (labels ⟨src e, srcCopy e⟩) (labels ⟨dst e, dstCopy e⟩))]
  apply Fintype.sum_equiv (fiberSplitConsistentEquiv dim rootCopy)
  intro labels
  apply Finset.prod_congr rfl
  intro e _
  rw [labels.2 ⟨src e, srcCopy e⟩, labels.2 ⟨dst e, dstCopy e⟩]
  rfl

theorem fiberSplitMatrix_norm_product_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) :
    (∏ e : FiberSplitEdge ε copy,
      euclideanOperatorNorm
        (fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [Fintype.prod_sum_type]
  simp only [fiberSplitMatrix]
  have hidentity :
      (∏ z : FiberSplitVertex copy,
        euclideanOperatorNorm
          (weightDiagonal (fun _ : Fin (dim z.1) => (1 : ℝ)))) ≤ 1 := by
    exact Finset.prod_le_one
      (fun z _ => euclideanOperatorNorm_nonneg
        (weightDiagonal (fun _ : Fin (dim z.1) => (1 : ℝ))))
      (fun z _ => euclideanOperatorNorm_weightDiagonal_le_one _ (by simp))
  exact mul_le_of_le_one_right
    (Finset.prod_nonneg fun e _ => euclideanOperatorNorm_nonneg (M e)) hidentity

theorem graphContraction_weightLoops_fiberSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (srcCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopSrc src e))
    (dstCopy : ∀ e : WeightLoopEdge ι ε, copy (weightLoopDst dst e))
    (rootCopy : ∀ v, copy v) :
    graphContraction (fiberSplitDim dim)
        (fiberSplitSrc (weightLoopSrc src) srcCopy rootCopy)
        (fiberSplitDst (weightLoopDst dst) dstCopy)
        (fiberSplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
          (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy)
        (fun _ _ => 1) =
      graphContraction dim src dst M w := by
  rw [graphContraction_fiberSplit, graphContraction_weightLoopMatrix]

theorem weightLoops_fiberSplit_norm_product_le
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
        (fiberSplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
          (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  exact (fiberSplitMatrix_norm_product_le dim
      (weightLoopSrc src) (weightLoopDst dst)
      (weightLoopMatrix dim src dst M w) srcCopy dstCopy rootCopy).trans
    (weightLoopMatrix_norm_product_le dim src dst M w hweight)

end Problem56

#print axioms Problem56.fiberSplitIdentityProduct
#print axioms Problem56.graphContraction_fiberSplit
#print axioms Problem56.fiberSplitMatrix_norm_product_le
#print axioms Problem56.graphContraction_weightLoops_fiberSplit
#print axioms Problem56.weightLoops_fiberSplit_norm_product_le
