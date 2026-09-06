import Problem56.GraphBridgelessConversion

open scoped BigOperators Matrix

namespace Problem56.PaperV6

/-- Primitive indexed-multigraph definition: after deleting any one indexed
edge, every pair of vertices is still joined by an undirected walk. Loops and
parallel edges are retained by the endpoint maps and the edge subtype. -/
def EveryEdgeDeletionConnected {ι ε : Type*} (src dst : ε → ι) : Prop :=
  ∀ e : ε, GraphConnected
    (fun f : {f : ε // f ≠ e} => src f.1)
    (fun f : {f : ε // f ≠ e} => dst f.1)

/-- Pending I-V6-10 consequence of the cited graph modification lemma,
frozen from C main.tex 930--936 and the boundary-preservation prose.

This is a proposition, not a theorem or an assumed certificate. It deliberately
has no parity or positive-degree hypothesis. The two boundary entries are
preserved individually, rectangular dimensions are explicit, and the new norm
product is bounded in the conclusion. It records the operator consequence of
modification rather than encoding a syntactic history of elementary moves.
`graphOperator` uses B's input-row/output-column convention; the existing v6
transpose bridge supplies the manuscript's target-row/source-column convention.
-/
def GeneralBridgelessConversionExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (u v : ι),
    GraphConnected src dst → EveryEdgeDeletionConnected src dst → u ≠ v →
    ∃ (ι' ε' : Type) (_ : Fintype ι') (_ : Fintype ε')
      (_ : DecidableEq ι') (dim' : ι' → ℕ) (src' dst' : ε' → ι')
      (M' : ∀ e, Matrix (Fin (dim' (src' e))) (Fin (dim' (dst' e))) ℝ)
      (input output : ι') (hinput : dim' input = dim u)
      (houtput : dim' output = dim v),
      input ≠ output ∧ MingoAdmissibleDAG src' dst' input output ∧
      (∀ (a : Fin (dim u)) (b : Fin (dim v)),
        graphOperator dim' src' dst' M' input output
          (Fin.cast hinput.symm a) (Fin.cast houtput.symm b) =
        graphOperator dim src dst M u v a b) ∧
      (∏ e, euclideanOperatorNorm (M' e)) ≤
        ∏ e, euclideanOperatorNorm (M e)

end Problem56.PaperV6
