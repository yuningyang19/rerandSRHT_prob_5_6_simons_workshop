import Problem56.GraphFiberSplit
import Problem56.GraphBridgelessConversion

open scoped BigOperators Matrix

namespace Problem56.PaperV6

/-- Reviewer-owned I-V6-11: selected copies carry the two fixed boundary labels.
This is an entrywise equality, not only equality after summing boundaries. -/
def FiberBoundaryExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (copy : ι → Type) [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) (input output : ι)
    (inputCopy : copy input) (outputCopy : copy output),
    input ≠ output →
    graphOperator (fiberSplitDim dim) (fiberSplitSrc src srcCopy rootCopy)
      (fiberSplitDst dst dstCopy)
      (fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy)
      ⟨input,inputCopy⟩ ⟨output,outputCopy⟩ =
      graphOperator dim src dst M input output

def ReversalBoundaryExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (reverse : ε → Bool) (input output : ι),
    graphOperator dim (selectivelyReversedSrc src dst (reverse := reverse))
      (selectivelyReversedDst src dst (reverse := reverse))
      (selectivelyReversedMatrix dim src dst M (reverse := reverse)) input output =
      graphOperator dim src dst M input output

end Problem56.PaperV6
