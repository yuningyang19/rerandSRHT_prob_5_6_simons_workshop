import Problem56.PaperV6.GeneralBridgelessTotalRank

namespace Problem56.PaperV6

/-- Used original edges and all inserted identity edges are active. -/
def constructionActiveEdge (H : FiniteBoundaryGraph)
    {ε : Type} (oldEdge : ε → H.Edge) (used : Set ε) (e : H.Edge) : Prop :=
  e ∉ Set.range oldEdge ∨ ∃ a ∈ used, oldEdge a = e

def constructionAdjacent (H : FiniteBoundaryGraph)
    {ε : Type} (oldEdge : ε → H.Edge) (used : Set ε)
    (a b : H.Vertex) : Prop :=
  ∃ e, H.src e = a ∧ H.dst e = b ∧ constructionActiveEdge H oldEdge used e

/-- A partial construction invariant. The actual full graph is obtained by a
finite permitted history. Only the active subgraph is asserted to be a DAG;
unused original edges remain in the full graph and may create directed cycles.

No boundary-matrix equality or norm conclusion is an invariant field. Existence
of an initial state and extension to a larger used edge set remain obligations.
-/
structure GeneralBridgelessState (G : FiniteBoundaryGraph) where
  current : FiniteBoundaryGraph
  history : BoundaryModification G current
  projection : current.Vertex → G.Vertex
  projection_surjective : Function.Surjective projection
  oldEdge : G.Edge → current.Edge
  oldEdge_injective : Function.Injective oldEdge
  reversed : G.Edge → Bool
  source_projection : ∀ e,
    projection (current.src (oldEdge e)) = orientedTail G.src G.dst (e, reversed e)
  target_projection : ∀ e,
    projection (current.dst (oldEdge e)) = orientedHead G.src G.dst (e, reversed e)
  input_projection : projection current.input = G.input
  output_projection : projection current.output = G.output
  active : Set G.Vertex
  used : Set G.Edge
  input_active : G.input ∈ active
  output_active : G.output ∈ active
  used_endpoints_active : ∀ e ∈ used, G.src e ∈ active ∧ G.dst e ∈ active
  outside_fiber_unique : ∀ v ∉ active, ∀ a b,
    projection a = v → projection b = v → a = b
  auxiliary_endpoints_active : ∀ e ∉ Set.range oldEdge,
    projection (current.src e) ∈ active ∧ projection (current.dst e) ∈ active
  partial_acyclic : ∀ v,
    ¬ Relation.TransGen (constructionAdjacent current oldEdge used) v v
  partial_from_input : ∀ v, projection v ∈ active →
    v = current.input ∨
      Relation.TransGen (constructionAdjacent current oldEdge used) current.input v
  partial_to_output : ∀ v, projection v ∈ active →
    v = current.output ∨
      Relation.TransGen (constructionAdjacent current oldEdge used) v current.output

/-- The decreasing measure counts only unused original edges. Added identity
edges are never counted as unfinished work. -/
noncomputable def GeneralBridgelessState.remaining {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) : ℕ := by
  classical
  exact Fintype.card {e : G.Edge // e ∉ S.used}

end Problem56.PaperV6
