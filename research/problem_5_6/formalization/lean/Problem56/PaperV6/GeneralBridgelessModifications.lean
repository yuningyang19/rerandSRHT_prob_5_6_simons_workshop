import Problem56.PaperV6.GeneralBridgelessExpected

namespace Problem56.PaperV6

/-- Finite rectangular graph data with two marked boundary vertices.
There are no analytic inequalities or conversion assumptions in this object. -/
structure FiniteBoundaryGraph where
  Vertex : Type
  Edge : Type
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  vertexDecidableEq : DecidableEq Vertex
  dim : Vertex → ℕ
  src : Edge → Vertex
  dst : Edge → Vertex
  matrix : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ
  input : Vertex
  output : Vertex

attribute [instance] FiniteBoundaryGraph.vertexFintype
  FiniteBoundaryGraph.edgeFintype FiniteBoundaryGraph.vertexDecidableEq

namespace FiniteBoundaryGraph

/-- Edge reversal is paired with actual matrix transposition. -/
noncomputable def reverse (G : FiniteBoundaryGraph) (r : G.Edge → Bool) :
    FiniteBoundaryGraph where
  Vertex := G.Vertex
  Edge := SelectivelyReversedEdge G.Edge r
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  vertexDecidableEq := inferInstance
  dim := G.dim
  src := selectivelyReversedSrc G.src G.dst
  dst := selectivelyReversedDst G.src G.dst
  matrix := selectivelyReversedMatrix G.dim G.src G.dst G.matrix
  input := G.input
  output := G.output

/-- A finite vertex split, retaining each original edge exactly once and
joining every non-root copy to the root by an actual identity matrix. A binary
split is the special case of a two-element fiber at one vertex. Iteration
therefore expresses the splits in the published ear-insertion construction. -/
noncomputable def split (G : FiniteBoundaryGraph)
    (copy : G.Vertex → Type) [∀ v, Fintype (copy v)]
    [∀ v, DecidableEq (copy v)] (root : ∀ v, copy v)
    (srcCopy : ∀ e, copy (G.src e)) (dstCopy : ∀ e, copy (G.dst e))
    (inputCopy : copy G.input) (outputCopy : copy G.output) :
    FiniteBoundaryGraph where
  Vertex := FiberSplitVertex copy
  Edge := RootedFiberSplitEdge G.Edge copy root
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  vertexDecidableEq := inferInstance
  dim := fiberSplitDim G.dim
  src := rootedFiberSplitSrc G.src srcCopy root
  dst := rootedFiberSplitDst G.dst dstCopy root
  matrix := rootedFiberSplitMatrix G.dim G.src G.dst G.matrix srcCopy dstCopy root
  input := ⟨G.input, inputCopy⟩
  output := ⟨G.output, outputCopy⟩

end FiniteBoundaryGraph

/-- A syntactic elementary modification. Neither constructor accepts a
boundary equality, an operator inequality, nor an acyclicity certificate. -/
inductive ElementaryBoundaryModification :
    FiniteBoundaryGraph → FiniteBoundaryGraph → Prop
  | reverse (G : FiniteBoundaryGraph) (r : G.Edge → Bool) :
      ElementaryBoundaryModification G (G.reverse r)
  | split (G : FiniteBoundaryGraph)
      (copy : G.Vertex → Type) [∀ v, Fintype (copy v)]
      [∀ v, DecidableEq (copy v)] (root : ∀ v, copy v)
      (srcCopy : ∀ e, copy (G.src e)) (dstCopy : ∀ e, copy (G.dst e))
      (inputCopy : copy G.input) (outputCopy : copy G.output) :
      ElementaryBoundaryModification G
        (G.split copy root srcCopy dstCopy inputCopy outputCopy)

/-- Finite compositional modification history, including the empty history. -/
def BoundaryModification := Relation.ReflTransGen ElementaryBoundaryModification

/-- The literal general graph-conversion obligation, separate from its
operator consequence. This records finite permitted moves, not an assumed
analytic certificate. No proof of this proposition is presently supplied. -/
def GeneralBridgelessModificationExpected : Prop :=
  ∀ G : FiniteBoundaryGraph,
    GraphConnected G.src G.dst → EveryEdgeDeletionConnected G.src G.dst →
    G.input ≠ G.output →
    ∃ H : FiniteBoundaryGraph, BoundaryModification G H ∧
      H.input ≠ H.output ∧ MingoAdmissibleDAG H.src H.dst H.input H.output

end Problem56.PaperV6
