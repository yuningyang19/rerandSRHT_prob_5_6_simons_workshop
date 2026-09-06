import Problem56.PaperV6.GeneralBridgelessState
import Problem56.PaperV6.GeneralBridgelessPathOrientation

namespace Problem56.PaperV6

theorem initial_state_adjacency (G : FiniteBoundaryGraph)
    (P : VertexSimpleIndexedPath G.src G.dst G.input G.output) :
    constructionAdjacent (G.reverse P.globalReversal)
      (selectiveReversalEquiv P.globalReversal) (Set.range P.edge) = P.pathAdjacent := by
  classical
  let E := selectiveReversalEquiv P.globalReversal
  have htail (i : Fin P.length) :
      (G.reverse P.globalReversal).src (E (P.edge i)) = P.point i.castSucc := by
    change orientedTail G.src G.dst (P.edge i, P.globalReversal (P.edge i)) = _
    rw [P.globalReversal_edge]
    exact P.tail i
  have hhead (i : Fin P.length) :
      (G.reverse P.globalReversal).dst (E (P.edge i)) = P.point i.succ := by
    change orientedHead G.src G.dst (P.edge i, P.globalReversal (P.edge i)) = _
    rw [P.globalReversal_edge]
    exact P.head i
  funext x y
  apply propext
  constructor
  · rintro ⟨e, hs, ht, he⟩
    rcases he with hnot | ⟨f, ⟨i, hif⟩, hfe⟩
    · exact (hnot ⟨E.symm e, E.apply_symm_apply e⟩).elim
    · subst f
      rw [← hfe] at hs ht
      exact ⟨i, (htail i).symm.trans hs, (hhead i).symm.trans ht⟩
  · rintro ⟨i, hx, hy⟩
    exact ⟨E (P.edge i), (htail i).trans hx, (hhead i).trans hy,
      Or.inr ⟨P.edge i, ⟨i, rfl⟩, rfl⟩⟩

/-- Start the actual full-graph construction by orienting a simple path from
the prescribed input to output. All other original edges remain present but
unused. This proves an initial invariant; it does not require a DAG or a
conversion certificate from the caller. -/
noncomputable def initialGeneralBridgelessState (G : FiniteBoundaryGraph)
    (P : VertexSimpleIndexedPath G.src G.dst G.input G.output) : GeneralBridgelessState G := by
  classical
  let r := P.globalReversal
  let E := selectiveReversalEquiv r
  refine {
    current := G.reverse r
    history := Relation.ReflTransGen.single (ElementaryBoundaryModification.reverse G r)
    projection := id
    projection_surjective := Function.surjective_id
    oldEdge := E
    oldEdge_injective := E.injective
    reversed := r
    source_projection := fun _ => rfl
    target_projection := fun _ => rfl
    input_projection := rfl
    output_projection := rfl
    active := Set.range P.point
    used := Set.range P.edge
    input_active := ⟨0, P.first⟩
    output_active := ⟨Fin.last P.length, P.last⟩
    used_endpoints_active := ?_
    outside_fiber_unique := ?_
    auxiliary_endpoints_active := ?_
    partial_acyclic := ?_
    partial_from_input := ?_
    partial_to_output := ?_ }
  · rintro e ⟨i, rfl⟩
    exact P.edge_endpoints_mem i
  · intro v hv x y hx hy
    exact hx.trans hy.symm
  · intro e he
    exact (he ⟨E.symm e, E.apply_symm_apply e⟩).elim
  · intro v
    change ¬ Relation.TransGen
      (constructionAdjacent (G.reverse P.globalReversal)
        (selectiveReversalEquiv P.globalReversal) (Set.range P.edge)) v v
    rw [initial_state_adjacency]
    exact P.path_acyclic v
  · intro v hv
    obtain ⟨i, rfl⟩ := hv
    have h := Relation.reflTransGen_iff_eq_or_transGen.mp (P.path_from_start i)
    change P.point i = G.input ∨ Relation.TransGen
      (constructionAdjacent (G.reverse P.globalReversal)
        (selectiveReversalEquiv P.globalReversal) (Set.range P.edge)) G.input (P.point i)
    rw [initial_state_adjacency]
    exact h
  · intro v hv
    obtain ⟨i, rfl⟩ := hv
    have h := Relation.reflTransGen_iff_eq_or_transGen.mp (P.path_to_end i)
    rcases h with heq | hpath
    · exact Or.inl heq.symm
    · right
      change Relation.TransGen
        (constructionAdjacent (G.reverse P.globalReversal)
          (selectiveReversalEquiv P.globalReversal) (Set.range P.edge)) (P.point i) G.output
      rw [initial_state_adjacency]
      exact hpath

theorem exists_initial_generalBridgelessState (G : FiniteBoundaryGraph)
    (hconn : GraphConnected G.src G.dst) : Nonempty (GeneralBridgelessState G) := by
  obtain ⟨P⟩ := exists_vertexSimpleIndexedPath G.src G.dst (hconn G.input G.output)
  exact ⟨initialGeneralBridgelessState G P⟩

end Problem56.PaperV6
