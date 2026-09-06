import Problem56.PaperV6.RootedHistoryExpected
import Problem56.PaperV6.GraphModifications

open scoped BigOperators Matrix Classical
namespace Problem56.PaperV6

/-- The accepted finite-label proof extended to the actual root-pruned split.
B's rooted identity product omits tautological root identity loops. -/
theorem rooted_graph_boundary {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) (input output : ι)
    (inputCopy : copy input) (outputCopy : copy output) :
    graphOperator (fiberSplitDim dim) (rootedFiberSplitSrc src srcCopy rootCopy)
      (rootedFiberSplitDst dst dstCopy rootCopy)
      (rootedFiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy)
      ⟨input, inputCopy⟩ ⟨output, outputCopy⟩ =
      graphOperator dim src dst M input output := by
  classical
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
      have hprod : (∏ e : RootedFiberSplitEdge ε copy rootCopy,
          rootedFiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e
            (lab (rootedFiberSplitSrc src srcCopy rootCopy e))
            (lab (rootedFiberSplitDst dst dstCopy rootCopy e))) =
          (∏ e : ε, M e (lab ⟨src e, srcCopy e⟩) (lab ⟨dst e, dstCopy e⟩)) *
          (if FiberSplitConsistent dim rootCopy lab then 1 else 0) := by
        rw [Fintype.prod_sum_type]
        change _ * (∏ z : ProperFiberCopy copy rootCopy,
          weightDiagonal (fun _ : Fin (dim z.1.1) ↦ (1 : ℝ))
            (lab ⟨z.1.1, rootCopy z.1.1⟩) (lab z.1)) = _
        rw [rootedFiberSplitIdentityProduct dim rootCopy]
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

/-- Positive dimensions give exact product equality for root-pruned stars. -/
theorem rooted_graph_norm_product {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) (hdim : ∀ v, 0 < dim v) :
    (∏ e : RootedFiberSplitEdge ε copy rootCopy,
      euclideanOperatorNorm (rootedFiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e)) =
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [Fintype.prod_sum_type]
  change (∏ e : ε, euclideanOperatorNorm (M e)) *
    (∏ z : ProperFiberCopy copy rootCopy,
      euclideanOperatorNorm (weightDiagonal (fun _ : Fin (dim z.1.1) ↦ (1 : ℝ)))) = _
  have hi : (∏ z : ProperFiberCopy copy rootCopy,
      euclideanOperatorNorm (weightDiagonal (fun _ : Fin (dim z.1.1) ↦ (1 : ℝ)))) = 1 := by
    apply Finset.prod_eq_one
    intro z _
    exact paper_identity_norm (hdim z.1.1)
  rw [hi, mul_one]

end Problem56.PaperV6
