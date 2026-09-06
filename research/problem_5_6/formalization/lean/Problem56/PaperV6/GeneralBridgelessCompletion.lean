import Problem56.PaperV6.GeneralBridgelessState

namespace Problem56.PaperV6

theorem GeneralBridgelessState.all_vertices_active_of_all_used
    {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (hconn : GraphConnected G.src G.dst) (hall : ∀ e, e ∈ S.used) :
    ∀ v, v ∈ S.active := by
  intro v
  induction hconn G.input v with
  | refl => exact S.input_active
  | tail hp hab ih =>
    obtain ⟨e, hforward | hbackward⟩ := hab
    · exact hforward.2 ▸ (S.used_endpoints_active e (hall e)).2
    · exact hbackward.1 ▸ (S.used_endpoints_active e (hall e)).1

theorem GeneralBridgelessState.adjacency_eq_of_all_used
    {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (hall : ∀ e, e ∈ S.used) :
    constructionAdjacent S.current S.oldEdge S.used =
      directedAdjacent S.current.src S.current.dst := by
  classical
  funext a b
  apply propext
  constructor
  · rintro ⟨e, hs, ht, _⟩
    exact ⟨e, hs, ht⟩
  · rintro ⟨e, hs, ht⟩
    refine ⟨e, hs, ht, ?_⟩
    by_cases he : e ∈ Set.range S.oldEdge
    · obtain ⟨f, hf⟩ := he
      exact Or.inr ⟨f, hall f, hf⟩
    · exact Or.inl he

/-- Exhaustion is enough: connectivity promotes all original vertices to the
active set, and every current edge is then active. The partial DAG fields
therefore yield a full input-output DAG. -/
theorem GeneralBridgelessState.dag_of_all_used
    {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (hconn : GraphConnected G.src G.dst) (hall : ∀ e, e ∈ S.used) :
    MingoAdmissibleDAG S.current.src S.current.dst S.current.input S.current.output := by
  have hvertices := S.all_vertices_active_of_all_used hconn hall
  have hadj := S.adjacency_eq_of_all_used hall
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hadj] using S.partial_acyclic
  · intro v
    simpa only [hadj] using S.partial_from_input v (hvertices (S.projection v))
  · intro v
    simpa only [hadj] using S.partial_to_output v (hvertices (S.projection v))

theorem GeneralBridgelessState.endpoints_distinct
    {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (hne : G.input ≠ G.output) : S.current.input ≠ S.current.output := by
  intro heq
  apply hne
  exact S.input_projection.symm.trans ((congrArg S.projection heq).trans S.output_projection)

/-- Final extraction from a completed construction state. Existence of that
state is not assumed in either public expected target and remains to be built. -/
theorem GeneralBridgelessState.completed_modification
    {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (hconn : GraphConnected G.src G.dst) (hne : G.input ≠ G.output)
    (hall : ∀ e, e ∈ S.used) :
    ∃ H : FiniteBoundaryGraph, BoundaryModification G H ∧
      H.input ≠ H.output ∧ MingoAdmissibleDAG H.src H.dst H.input H.output :=
  ⟨S.current, S.history, S.endpoints_distinct hne, S.dag_of_all_used hconn hall⟩

end Problem56.PaperV6
