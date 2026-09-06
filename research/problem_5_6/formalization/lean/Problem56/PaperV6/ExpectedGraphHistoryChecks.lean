import Problem56.PaperV6.RootedHistoryConversion

/-! Independent reviewer-owned assignments for frozen C I-V6-10/I-V6-11.
Only existing proof terms are assigned. No conversion or preservation proof is
supplied by this file. Primitive graph/entry/norm definitions were read separately. -/
open scoped BigOperators Matrix
namespace Problem56.PaperV6

example : ∀ G : FiniteBoundaryGraph,
    GraphConnected G.src G.dst → EveryEdgeDeletionConnected G.src G.dst →
    G.input ≠ G.output →
    ∃ H : FiniteBoundaryGraph, BoundaryModification G H ∧
      H.input ≠ H.output ∧ MingoAdmissibleDAG H.src H.dst H.input H.output :=
  generalBridgeless_modification

example : ∀ G H : FiniteBoundaryGraph, ElementaryBoundaryModification G H →
    BoundaryEntriesPreserved G H ∧
    boundaryGraphNormProduct H ≤ boundaryGraphNormProduct G ∧
    ((∀ v, 0 < G.dim v) →
      (∀ v, 0 < H.dim v) ∧ boundaryGraphNormProduct H = boundaryGraphNormProduct G) :=
  rooted_elementary

example : ∀ G H : FiniteBoundaryGraph, BoundaryModification G H →
    BoundaryEntriesPreserved G H ∧
    boundaryGraphNormProduct H ≤ boundaryGraphNormProduct G ∧
    ((∀ v, 0 < G.dim v) →
      (∀ v, 0 < H.dim v) ∧ boundaryGraphNormProduct H = boundaryGraphNormProduct G) :=
  rooted_history

example : GeneralBridgelessModificationExpected → GeneralBridgelessConversionExpected :=
  rooted_history_consequence

example :
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
          ∏ e, euclideanOperatorNorm (M e) :=
  general_bridgeless_matrix_conversion

end Problem56.PaperV6
