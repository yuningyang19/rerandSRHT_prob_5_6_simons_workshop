import Problem56.PaperV6.GraphBridges
import Problem56.PaperV6.GraphModificationsExpected

open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace Problem56.PaperV6

/-- Checked finite-sum restriction used to retain fixed boundary labels. -/
theorem sum_guard_eq_subtype {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    (∑ x, if P x then f x else 0) = ∑ x : {x // P x}, f x.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

theorem fiberSplit_equiv_apply {ι : Type*} [Fintype ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)]
    (dim : ι → ℕ) (rootCopy : ∀ v, copy v)
    (lab : {lab : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z) //
      FiberSplitConsistent dim rootCopy lab}) :
    (fiberSplitConsistentEquiv dim rootCopy) lab = fiberSplitDecode dim rootCopy lab.1 := rfl

theorem graph_fiber_boundary : FiberBoundaryExpected := by
  classical
  intro ι ε _ _ _ copy _ _ dim src dst M srcCopy dstCopy rootCopy
    input output inputCopy outputCopy hio
  funext a b
  unfold graphOperator
  let F : (∀ v, Fin (dim v)) → ℝ := fun lab ↦
    if lab input = a ∧ lab output = b then
      ∏ e, M e (lab (src e)) (lab (dst e)) else 0
  calc
    _ = ∑ lab : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z),
        if FiberSplitConsistent dim rootCopy lab then
          F (fiberSplitDecode dim rootCopy lab) else 0 := by
      apply Finset.sum_congr rfl
      intro lab _
      have hprod : (∏ e : FiberSplitEdge ε copy,
          fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e
            (lab (fiberSplitSrc src srcCopy rootCopy e))
            (lab (fiberSplitDst dst dstCopy e))) =
          (∏ e : ε, M e (lab ⟨src e, srcCopy e⟩) (lab ⟨dst e, dstCopy e⟩)) *
          (if FiberSplitConsistent dim rootCopy lab then 1 else 0) := by
        rw [Fintype.prod_sum_type]
        change _ * (∏ z : FiberSplitVertex copy,
          weightDiagonal (fun _ : Fin (dim z.1) ↦ (1 : ℝ))
            (lab ⟨z.1, rootCopy z.1⟩) (lab z)) = _
        rw [fiberSplitIdentityProduct dim rootCopy]
        rfl
      rw [hprod]
      by_cases hc : FiberSplitConsistent dim rootCopy lab
      · rw [if_pos hc, mul_one, if_pos hc]
        have hboundary :
            (lab ⟨input, inputCopy⟩ = a ∧ lab ⟨output, outputCopy⟩ = b) ↔
            (fiberSplitDecode dim rootCopy lab input = a ∧
              fiberSplitDecode dim rootCopy lab output = b) := by
          rw [hc ⟨input, inputCopy⟩, hc ⟨output, outputCopy⟩]
          rfl
        simp only [hboundary]
        dsimp only [F]
        congr 1
        apply Finset.prod_congr rfl
        intro e _
        rw [hc ⟨src e, srcCopy e⟩, hc ⟨dst e, dstCopy e⟩]
        rfl
      · simp only [hc, if_false, mul_zero, ite_self]
    _ = ∑ lab : {lab : ∀ z : FiberSplitVertex copy, Fin (fiberSplitDim dim z) //
          FiberSplitConsistent dim rootCopy lab},
          F (fiberSplitDecode dim rootCopy lab.1) :=
      sum_guard_eq_subtype _ _
    _ = _ := by
      apply Fintype.sum_equiv (fiberSplitConsistentEquiv dim rootCopy)
      intro lab
      simp only [fiberSplit_equiv_apply, F]
      with_unfolding_all congr

theorem graph_reversal_boundary : ReversalBoundaryExpected := by
  classical
  intro ι ε _ _ _ dim src dst M reverse input output
  funext a b
  unfold graphOperator
  apply Finset.sum_congr rfl
  intro labels _
  congr 1
  exact Fintype.prod_equiv (selectiveReversalEquiv reverse).symm
    (fun q : SelectivelyReversedEdge ε reverse ↦
      selectivelyReversedMatrix dim src dst M q
        (labels (selectivelyReversedSrc src dst q))
        (labels (selectivelyReversedDst src dst q)))
    (fun e ↦ M e (labels (src e)) (labels (dst e)))
    (fun q ↦ by
      rcases q with ⟨⟨e, b⟩, hb⟩
      cases b <;>
        simp [selectiveReversalEquiv, selectivelyReversedMatrix,
          selectivelyReversedSrc, selectivelyReversedDst, orientedTail,
          orientedHead, Matrix.transpose_apply])

/-- Positive coordinate dimension is the exact paper condition needed for
identity norm one; B's zero-dimensional extension gives only ≤ one. -/
theorem paper_identity_norm {n : ℕ} (hn : 0 < n) :
    euclideanOperatorNorm (weightDiagonal (fun _ : Fin n ↦ (1 : ℝ))) = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hid : weightDiagonal (fun _ : Fin n ↦ (1 : ℝ)) = 1 := by
    ext i j
    simp [weightDiagonal, Matrix.one_apply]
  rw [hid, euclideanOperatorNorm_eq_l2_opNorm]
  exact norm_one

theorem graph_fiber_norm_product {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) (hdim : ∀ v, 0 < dim v) :
    (∏ e : FiberSplitEdge ε copy,
      euclideanOperatorNorm (fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e)) =
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [Fintype.prod_sum_type]
  change (∏ e : ε, euclideanOperatorNorm (M e)) *
    (∏ z : FiberSplitVertex copy,
      euclideanOperatorNorm (weightDiagonal (fun _ : Fin (dim z.1) ↦ (1 : ℝ)))) = _
  have hi : (∏ z : FiberSplitVertex copy,
      euclideanOperatorNorm (weightDiagonal (fun _ : Fin (dim z.1) ↦ (1 : ℝ)))) = 1 := by
    apply Finset.prod_eq_one
    intro z _
    exact paper_identity_norm (hdim z.1)
  rw [hi, mul_one]

end Problem56.PaperV6
