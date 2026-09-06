import Problem56.PaperV6.GeneralBridgelessModifications

open scoped BigOperators Matrix
namespace Problem56.PaperV6

/-- The primitive finite boundary sum; no analytic property is assumed. -/
noncomputable def boundaryGraphOperator (G : FiniteBoundaryGraph) :
    Matrix (Fin (G.dim G.input)) (Fin (G.dim G.output)) ℝ :=
  graphOperator G.dim G.src G.dst G.matrix G.input G.output

noncomputable def boundaryGraphNormProduct (G : FiniteBoundaryGraph) : ℝ :=
  ∏ e, euclideanOperatorNorm (G.matrix e)

def PositiveBoundaryGraphDimensions (G : FiniteBoundaryGraph) : Prop :=
  ∀ v, 0 < G.dim v

/-- Equality after the explicit casts required by the two endpoint dimensions.
These equalities are conclusions about a modification, not fields in graph data. -/
def BoundaryEntriesPreserved (G H : FiniteBoundaryGraph) : Prop :=
  ∃ (hi : H.dim H.input = G.dim G.input)
    (ho : H.dim H.output = G.dim G.output),
    ∀ (a : Fin (G.dim G.input)) (b : Fin (G.dim G.output)),
      boundaryGraphOperator H (Fin.cast hi.symm a) (Fin.cast ho.symm b) =
        boundaryGraphOperator G a b

/-- Exact one-step consequence of a literal permitted reversal or root-pruned
identity split. The weak norm inequality includes zero-dimensional spaces. -/
def RootedElementaryExpected : Prop :=
  ∀ G H : FiniteBoundaryGraph, ElementaryBoundaryModification G H →
    BoundaryEntriesPreserved G H ∧
    boundaryGraphNormProduct H ≤ boundaryGraphNormProduct G ∧
    (PositiveBoundaryGraphDimensions G →
      PositiveBoundaryGraphDimensions H ∧
      boundaryGraphNormProduct H = boundaryGraphNormProduct G)

/-- The same statements for an actual finite permitted history, including the
empty history. Positivity is preserved through every intermediate graph. -/
def RootedHistoryExpected : Prop :=
  ∀ G H : FiniteBoundaryGraph, BoundaryModification G H →
    BoundaryEntriesPreserved G H ∧
    boundaryGraphNormProduct H ≤ boundaryGraphNormProduct G ∧
    (PositiveBoundaryGraphDimensions G →
      PositiveBoundaryGraphDimensions H ∧
      boundaryGraphNormProduct H = boundaryGraphNormProduct G)

/-- Compositional bridge only: once the separate pure graph construction is
proved, its literal modification history gives the stated matrix consequence.
No norm or boundary certificate is accepted as an input. -/
def GeneralBridgelessConsequenceBridgeExpected : Prop :=
  GeneralBridgelessModificationExpected → GeneralBridgelessConversionExpected

end Problem56.PaperV6
