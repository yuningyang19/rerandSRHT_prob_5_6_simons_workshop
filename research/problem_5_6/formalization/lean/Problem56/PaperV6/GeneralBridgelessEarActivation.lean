import Problem56.PaperV6.GeneralBridgelessEarStateDAG
import Problem56.PaperV6.GeneralBridgelessProgressMeasure

namespace Problem56.PaperV6

theorem StateFreshEar.original_endpoints_new_active {G : FiniteBoundaryGraph}
    {S : GeneralBridgelessState G} (P : StateFreshEar S)
    (i : Fin (P.internalCount + 1)) :
    G.src (P.edge i) ∈ P.newActive ∧ G.dst (P.edge i) ∈ P.newActive := by
  have hs := S.source_projection (P.edge i)
  have ht := S.target_projection (P.edge i)
  rw [P.source i] at hs
  rw [P.target i] at ht
  cases h : S.reversed (P.edge i) with
  | false =>
    simp only [h, orientedTail, orientedHead] at hs ht
    exact ⟨Or.inr ⟨i.castSucc, hs⟩, Or.inr ⟨i.succ, ht⟩⟩
  | true =>
    simp only [h, orientedTail, orientedHead] at hs ht
    exact ⟨Or.inr ⟨i.succ, ht⟩, Or.inr ⟨i.castSucc, hs⟩⟩

/-- Activate a concrete correctly ordered fresh ear. The actual full graph is
unchanged at this step; its already constructed modification history is kept.
The new partial DAG and all invariant fields are derived from finite data. -/
noncomputable def GeneralBridgelessState.activateEar {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (P : StateFreshEar S) (horder : P.Ordered) :
    GeneralBridgelessState G := by
  refine { S with
    active := P.newActive
    used := P.newUsed
    input_active := Or.inl S.input_active
    output_active := Or.inl S.output_active
    used_endpoints_active := ?_
    outside_fiber_unique := ?_
    auxiliary_endpoints_active := ?_
    partial_acyclic := P.partial_acyclic horder
    partial_from_input := P.partial_from_input horder
    partial_to_output := P.partial_to_output horder }
  · intro e he
    rcases he with hold | ⟨i, hi⟩
    · exact ⟨Or.inl (S.used_endpoints_active e hold).1,
        Or.inl (S.used_endpoints_active e hold).2⟩
    · rw [← hi]
      exact P.original_endpoints_new_active i
  · intro v hv a b ha hb
    exact S.outside_fiber_unique v (fun h => hv (Or.inl h)) a b ha hb
  · intro e he
    exact ⟨Or.inl (S.auxiliary_endpoints_active e he).1,
      Or.inl (S.auxiliary_endpoints_active e he).2⟩

@[simp] theorem GeneralBridgelessState.activateEar_used {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (P : StateFreshEar S) (horder : P.Ordered) :
    (S.activateEar P horder).used = P.newUsed := rfl

@[simp] theorem GeneralBridgelessState.activateEar_active {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (P : StateFreshEar S) (horder : P.Ordered) :
    (S.activateEar P horder).active = P.newActive := rfl

theorem GeneralBridgelessState.activateEar_remaining_lt {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (P : StateFreshEar S) (horder : P.Ordered) :
    (S.activateEar P horder).remaining < S.remaining := by
  apply S.remaining_lt_of_used_subset (S.activateEar P horder)
  · intro e he
    exact Or.inl he
  · exact ⟨P.edge 0, Or.inr ⟨0, rfl⟩, P.edge_fresh 0⟩

end Problem56.PaperV6
