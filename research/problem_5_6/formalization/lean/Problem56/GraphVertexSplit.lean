import Problem56.GraphWeightLoops

/-!
An exact simultaneous binary vertex split for graph contractions.  Every old
vertex receives two copies, every old incidence may be routed independently to
either copy, and one identity edge per vertex forces the two copied labels to
agree.  Splitting unused vertices as well is harmless and removes the dependent
transport bookkeeping that arises from a one-vertex-at-a-time representation.

This is a source-faithful finite instance of the vertex modification in
Mingo--Speicher Proposition 13.  It preserves loops, indexed parallel edges,
rectangular matrices, the scalar contraction, and the product norm bound.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

abbrev BinarySplitVertex (ι : Type*) := ι × Bool
abbrev BinarySplitEdge (ι ε : Type*) := ε ⊕ ι

def binarySplitDim {ι : Type*} (dim : ι → ℕ) : BinarySplitVertex ι → ℕ :=
  fun z => dim z.1

def binarySplitSrc {ι ε : Type*} (src : ε → ι)
    (sourceSide : ε → Bool) : BinarySplitEdge ι ε → BinarySplitVertex ι
  | Sum.inl e => (src e, sourceSide e)
  | Sum.inr v => (v, false)

def binarySplitDst {ι ε : Type*} (dst : ε → ι)
    (targetSide : ε → Bool) : BinarySplitEdge ι ε → BinarySplitVertex ι
  | Sum.inl e => (dst e, targetSide e)
  | Sum.inr v => (v, true)

noncomputable def binarySplitMatrix {ι ε : Type*} [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (sourceSide targetSide : ε → Bool) :
    ∀ e : BinarySplitEdge ι ε,
      Matrix (Fin (binarySplitDim dim (binarySplitSrc src sourceSide e)))
        (Fin (binarySplitDim dim (binarySplitDst dst targetSide e))) ℝ
  | Sum.inl e => M e
  | Sum.inr _ => weightDiagonal (fun _ => 1)

def BinarySplitConsistent {ι : Type*} (dim : ι → ℕ)
    (labels : ∀ z : BinarySplitVertex ι, Fin (binarySplitDim dim z)) : Prop :=
  ∀ v, labels (v, false) = labels (v, true)

def binarySplitDecode {ι : Type*} (dim : ι → ℕ)
    (labels : ∀ z : BinarySplitVertex ι, Fin (binarySplitDim dim z)) :
    ∀ v, Fin (dim v) :=
  fun v => labels (v, false)

theorem binarySplitLabel_eq_decode {ι : Type*} (dim : ι → ℕ)
    (labels : ∀ z : BinarySplitVertex ι, Fin (binarySplitDim dim z))
    (hlabels : BinarySplitConsistent dim labels) (v : ι) (side : Bool) :
    labels (v, side) = binarySplitDecode dim labels v := by
  cases side
  · rfl
  · exact (hlabels v).symm

noncomputable def binarySplitConsistentEquiv {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) :
    {labels : ∀ z : BinarySplitVertex ι, Fin (binarySplitDim dim z) //
      BinarySplitConsistent dim labels} ≃ (∀ v, Fin (dim v)) where
  toFun labels := binarySplitDecode dim labels.1
  invFun labels := ⟨fun z => labels z.1, fun _ => rfl⟩
  left_inv := by
    intro labels
    apply Subtype.ext
    funext z
    rcases z with ⟨v, side⟩
    exact (binarySplitLabel_eq_decode dim labels.1 labels.2 v side).symm
  right_inv := by
    intro labels
    rfl

private theorem fintype_sum_ite_eq_subtype
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

theorem binarySplitIdentityProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι] (dim : ι → ℕ)
    (labels : ∀ z : BinarySplitVertex ι, Fin (binarySplitDim dim z)) :
    (∏ v, weightDiagonal (fun _ : Fin (dim v) => (1 : ℝ))
        (labels (v, false)) (labels (v, true))) =
      (by classical
          exact if BinarySplitConsistent dim labels then 1 else 0) := by
  classical
  by_cases h : BinarySplitConsistent dim labels
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro v _
    simp [weightDiagonal, h v]
    rfl
  · rw [if_neg h]
    obtain ⟨v, hv⟩ := Classical.not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    unfold weightDiagonal
    dsimp only [binarySplitDim] at hv ⊢
    rw [if_neg hv]

theorem graphContraction_binarySplit
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (sourceSide targetSide : ε → Bool) :
    graphContraction (binarySplitDim dim) (binarySplitSrc src sourceSide)
        (binarySplitDst dst targetSide)
        (binarySplitMatrix dim src dst M sourceSide targetSide)
        (fun _ _ => 1) =
      graphContraction dim src dst M (fun _ _ => 1) := by
  classical
  simp only [graphContraction, Finset.prod_const_one, mul_one]
  rw [show (∑ labels : ∀ z : BinarySplitVertex ι,
      Fin (binarySplitDim dim z),
      ∏ e : BinarySplitEdge ι ε,
        binarySplitMatrix dim src dst M sourceSide targetSide e
          (labels (binarySplitSrc src sourceSide e))
          (labels (binarySplitDst dst targetSide e))) =
      ∑ labels : ∀ z : BinarySplitVertex ι,
        Fin (binarySplitDim dim z),
        (∏ e : ε, M e (labels (src e, sourceSide e))
          (labels (dst e, targetSide e))) *
        ∏ v : ι, weightDiagonal (fun _ : Fin (dim v) => (1 : ℝ))
          (labels (v, false)) (labels (v, true)) by
    apply Finset.sum_congr rfl
    intro labels _
    rw [Fintype.prod_sum_type]
    rfl]
  simp_rw [binarySplitIdentityProduct dim]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [fintype_sum_ite_eq_subtype (BinarySplitConsistent dim)
    (fun labels => ∏ e : ε, M e (labels (src e, sourceSide e))
      (labels (dst e, targetSide e)))]
  apply Fintype.sum_equiv (binarySplitConsistentEquiv dim)
  intro labels
  apply Finset.prod_congr rfl
  intro e _
  rw [binarySplitLabel_eq_decode dim labels.1 labels.2,
    binarySplitLabel_eq_decode dim labels.1 labels.2]
  rfl

theorem binarySplitMatrix_norm_product_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (sourceSide targetSide : ε → Bool) :
    (∏ e : BinarySplitEdge ι ε,
      euclideanOperatorNorm
        (binarySplitMatrix dim src dst M sourceSide targetSide e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [Fintype.prod_sum_type]
  simp only [binarySplitMatrix]
  have hidentity :
      (∏ v : ι,
        euclideanOperatorNorm
          (weightDiagonal (fun _ : Fin (dim v) => (1 : ℝ)))) ≤ 1 := by
    exact Finset.prod_le_one
      (fun v _ => euclideanOperatorNorm_nonneg
        (weightDiagonal (fun _ : Fin (dim v) => (1 : ℝ))))
      (fun v _ => euclideanOperatorNorm_weightDiagonal_le_one _ (by simp))
  exact mul_le_of_le_one_right
    (Finset.prod_nonneg fun e _ => euclideanOperatorNorm_nonneg (M e)) hidentity

/-- Add the vertex weights as diagonal loops and then route every resulting
incidence through an arbitrary binary split.  This packages the two exact
Mingo--Speicher modification primitives while leaving the later acyclic
orientation choice completely free. -/
theorem graphContraction_weightLoops_binarySplit
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (sourceSide targetSide : WeightLoopEdge ι ε → Bool) :
    graphContraction (binarySplitDim dim)
        (binarySplitSrc (weightLoopSrc src) sourceSide)
        (binarySplitDst (weightLoopDst dst) targetSide)
        (binarySplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
          (weightLoopMatrix dim src dst M w) sourceSide targetSide)
        (fun _ _ => 1) =
      graphContraction dim src dst M w := by
  rw [graphContraction_binarySplit, graphContraction_weightLoopMatrix]

theorem weightLoops_binarySplit_norm_product_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (hweight : ∀ v i, |w v i| ≤ 1)
    (sourceSide targetSide : WeightLoopEdge ι ε → Bool) :
    (∏ e,
      euclideanOperatorNorm
        (binarySplitMatrix dim (weightLoopSrc src) (weightLoopDst dst)
          (weightLoopMatrix dim src dst M w) sourceSide targetSide e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  exact (binarySplitMatrix_norm_product_le dim
      (weightLoopSrc src) (weightLoopDst dst)
      (weightLoopMatrix dim src dst M w) sourceSide targetSide).trans
    (weightLoopMatrix_norm_product_le dim src dst M w hweight)

end Problem56

#print axioms Problem56.binarySplitIdentityProduct
#print axioms Problem56.graphContraction_binarySplit
#print axioms Problem56.binarySplitMatrix_norm_product_le
#print axioms Problem56.graphContraction_weightLoops_binarySplit
#print axioms Problem56.weightLoops_binarySplit_norm_product_le
