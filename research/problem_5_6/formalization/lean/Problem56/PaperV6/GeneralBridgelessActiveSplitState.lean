import Problem56.PaperV6.GeneralBridgelessActiveSplitDAG

namespace Problem56.PaperV6

theorem activeSplitCopy_eq_root_of_inactive {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (v : S.current.Vertex)
    (hv : S.projection v ∉ S.active) (c : ActiveSplitCopy S v) :
    c = activeSplitRoot S v := by
  apply Subtype.ext
  rcases c.2 with hfalse | hactive
  · exact hfalse
  · exact (hv hactive).elim

theorem activeSplit_outside_fiber_unique {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : G.Vertex) (hv : v ∉ S.active)
    (a b : (activeSplitGraph S R).Vertex)
    (ha : activeSplitProjection S R a = v) (hb : activeSplitProjection S R b = v) : a = b := by
  rcases a with ⟨a, ca⟩
  rcases b with ⟨b, cb⟩
  change S.projection a = v at ha
  change S.projection b = v at hb
  have hab := S.outside_fiber_unique v hv a b ha hb
  subst b
  have hnot : S.projection a ∉ S.active := by rw [ha]; exact hv
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [activeSplitCopy_eq_root_of_inactive S a hnot ca,
      activeSplitCopy_eq_root_of_inactive S a hnot cb]

/-- An actual permitted split of the full graph, performed only over active
original vertices. The invariant is preserved, including singleton inactive
fibers and the unchanged count of unused original edges. -/
noncomputable def GeneralBridgelessState.splitActive {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) : GeneralBridgelessState G := by
  classical
  refine {
    current := activeSplitGraph S R
    history := S.history.tail (ElementaryBoundaryModification.split S.current
      (ActiveSplitCopy S) (activeSplitRoot S) R.srcCopy R.dstCopy
      (activeSplitRoot S S.current.input)
      ⟨true, Or.inr (by rw [S.output_projection]; exact S.output_active)⟩)
    projection := activeSplitProjection S R
    projection_surjective := ?_
    oldEdge := activeSplitOldEdge S R
    oldEdge_injective := ?_
    reversed := S.reversed
    source_projection := ?_
    target_projection := ?_
    input_projection := S.input_projection
    output_projection := S.output_projection
    active := S.active
    used := S.used
    input_active := S.input_active
    output_active := S.output_active
    used_endpoints_active := S.used_endpoints_active
    outside_fiber_unique := activeSplit_outside_fiber_unique S R
    auxiliary_endpoints_active := ?_
    partial_acyclic := activeSplit_partial_acyclic S R
    partial_from_input := activeSplit_partial_from_input S R
    partial_to_output := activeSplit_partial_to_output S R }
  · intro v
    obtain ⟨w, hw⟩ := S.projection_surjective v
    exact ⟨⟨w, activeSplitRoot S w⟩, hw⟩
  · intro a b hab
    exact S.oldEdge_injective (Sum.inl.inj hab)
  · exact S.source_projection
  · exact S.target_projection
  · intro e he
    cases e with
    | inl e =>
      have hnot : e ∉ Set.range S.oldEdge := by
        rintro ⟨f, hf⟩
        exact he ⟨f, congrArg Sum.inl hf⟩
      exact S.auxiliary_endpoints_active e hnot
    | inr z =>
      exact ⟨activeSplit_proper_is_active S z, activeSplit_proper_is_active S z⟩

@[simp] theorem GeneralBridgelessState.splitActive_used {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) :
    (S.splitActive R).used = S.used := rfl

@[simp] theorem GeneralBridgelessState.splitActive_active {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) :
    (S.splitActive R).active = S.active := rfl

@[simp] theorem GeneralBridgelessState.splitActive_remaining {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) :
    (S.splitActive R).remaining = S.remaining := rfl

end Problem56.PaperV6
