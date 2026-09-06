import Problem56.PaperV6.GeneralBridgelessActiveSplitData

namespace Problem56.PaperV6

def activeSplitEdgeEmbed {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) :
    IncomingOutgoingEdge S.ActiveVertex S.ActiveEdge → (activeSplitGraph S R).Edge
  | Sum.inl e => Sum.inl e.1
  | Sum.inr z => Sum.inr ⟨activeSplitEmbed S R z.1, by
      intro h
      apply z.2
      exact congrArg Subtype.val h⟩

theorem activeSplitEdgeEmbed_src {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (e : IncomingOutgoingEdge S.ActiveVertex S.ActiveEdge) :
    activeSplitEmbed S R (incomingOutgoingSrc S.activeSrc e) =
      (activeSplitGraph S R).src (activeSplitEdgeEmbed S R e) := by
  cases e with
  | inl e =>
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact Subtype.ext (R.source_active e.1 e.2).symm
  | inr z =>
    apply Sigma.ext rfl
    apply heq_of_eq
    exact Subtype.ext rfl

theorem activeSplitEdgeEmbed_dst {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (e : IncomingOutgoingEdge S.ActiveVertex S.ActiveEdge) :
    activeSplitEmbed S R (incomingOutgoingDst S.activeDst e) =
      (activeSplitGraph S R).dst (activeSplitEdgeEmbed S R e) := by
  cases e with
  | inl e =>
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact Subtype.ext (R.target_active e.1 e.2).symm
  | inr z => rfl

theorem activeSplitEdgeEmbed_active {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (e : IncomingOutgoingEdge S.ActiveVertex S.ActiveEdge) :
    constructionActiveEdge (activeSplitGraph S R) (activeSplitOldEdge S R) S.used
      (activeSplitEdgeEmbed S R e) := by
  cases e with
  | inl e => exact (activeSplit_inl_active_iff S R e.1).2 e.2
  | inr z => exact activeSplit_inr_active S R _

theorem activeSplitEdgeEmbed_surjective_active {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (e : (activeSplitGraph S R).Edge)
    (he : constructionActiveEdge (activeSplitGraph S R) (activeSplitOldEdge S R) S.used e) :
    ∃ q : IncomingOutgoingEdge S.ActiveVertex S.ActiveEdge,
      activeSplitEdgeEmbed S R q = e := by
  cases e with
  | inl e => exact ⟨Sum.inl ⟨e, (activeSplit_inl_active_iff S R e).1 he⟩, rfl⟩
  | inr z =>
    let v : S.ActiveVertex := ⟨z.1.1, activeSplit_proper_is_active S z⟩
    refine ⟨incomingOutgoingIdentity v, ?_⟩
    apply congrArg Sum.inr
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact Subtype.ext (activeSplit_proper_is_true S z).symm

theorem activeSplitEmbed_step {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    {a b : IncomingOutgoingVertex S.ActiveVertex}
    (h : directedAdjacent (incomingOutgoingSrc S.activeSrc) (incomingOutgoingDst S.activeDst) a b) :
    constructionAdjacent (activeSplitGraph S R) (activeSplitOldEdge S R) S.used
      (activeSplitEmbed S R a) (activeSplitEmbed S R b) := by
  obtain ⟨e, hs, ht⟩ := h
  exact ⟨activeSplitEdgeEmbed S R e,
    (activeSplitEdgeEmbed_src S R e).symm.trans (congrArg (activeSplitEmbed S R) hs),
    (activeSplitEdgeEmbed_dst S R e).symm.trans (congrArg (activeSplitEmbed S R) ht),
    activeSplitEdgeEmbed_active S R e⟩

theorem activeSplitRetract_step {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    {a b : (activeSplitGraph S R).Vertex}
    (h : constructionAdjacent (activeSplitGraph S R) (activeSplitOldEdge S R) S.used a b) :
    directedAdjacent (incomingOutgoingSrc S.activeSrc) (incomingOutgoingDst S.activeDst)
      (activeSplitRetract S R a) (activeSplitRetract S R b) := by
  obtain ⟨e, hs, ht, he⟩ := h
  obtain ⟨q, hq⟩ := activeSplitEdgeEmbed_surjective_active S R e he
  rw [← hq, ← activeSplitEdgeEmbed_src] at hs
  rw [← hq, ← activeSplitEdgeEmbed_dst] at ht
  refine ⟨q, ?_, ?_⟩
  · simpa only [activeSplitRetract_embed] using congrArg (activeSplitRetract S R) hs
  · simpa only [activeSplitRetract_embed] using congrArg (activeSplitRetract S R) ht

theorem activeSplitEmbed_input {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) :
    activeSplitEmbed S R ⟨S.activeInput, false⟩ = (activeSplitGraph S R).input := by
  apply Sigma.ext rfl
  apply heq_of_eq
  exact Subtype.ext rfl

theorem activeSplitEmbed_output {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) :
    activeSplitEmbed S R ⟨S.activeOutput, true⟩ = (activeSplitGraph S R).output := by
  apply Sigma.ext rfl
  apply heq_of_eq
  exact Subtype.ext rfl

theorem activeSplit_partial_acyclic {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) (v : (activeSplitGraph S R).Vertex) :
    ¬ Relation.TransGen
      (constructionAdjacent (activeSplitGraph S R) (activeSplitOldEdge S R) S.used) v v := by
  classical
  have hdag := incomingOutgoing_mingoAdmissibleDAG
    S.activeSrc S.activeDst S.activeInput S.activeOutput S.activeGraph_dag
  intro hcycle
  exact hdag.1 _ (hcycle.lift (activeSplitRetract S R)
    (fun _ _ h => activeSplitRetract_step S R h))

theorem activeSplit_partial_from_input {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : (activeSplitGraph S R).Vertex) (hv : S.projection v.1 ∈ S.active) :
    v = (activeSplitGraph S R).input ∨ Relation.TransGen
      (constructionAdjacent (activeSplitGraph S R) (activeSplitOldEdge S R) S.used)
      (activeSplitGraph S R).input v := by
  classical
  have hdag := incomingOutgoing_mingoAdmissibleDAG
    S.activeSrc S.activeDst S.activeInput S.activeOutput S.activeGraph_dag
  rcases hdag.2.1 (activeSplitRetract S R v) with heq | hpath
  · left
    calc
      v = activeSplitEmbed S R (activeSplitRetract S R v) :=
        (activeSplitEmbed_retract S R v hv).symm
      _ = activeSplitEmbed S R ⟨S.activeInput, false⟩ := congrArg (activeSplitEmbed S R) heq
      _ = _ := activeSplitEmbed_input S R
  · right
    have h := hpath.lift (activeSplitEmbed S R) (fun _ _ h => activeSplitEmbed_step S R h)
    simpa only [Function.onFun, activeSplitEmbed_input, activeSplitEmbed_retract S R v hv] using h

theorem activeSplit_partial_to_output {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : (activeSplitGraph S R).Vertex) (hv : S.projection v.1 ∈ S.active) :
    v = (activeSplitGraph S R).output ∨ Relation.TransGen
      (constructionAdjacent (activeSplitGraph S R) (activeSplitOldEdge S R) S.used)
      v (activeSplitGraph S R).output := by
  classical
  have hdag := incomingOutgoing_mingoAdmissibleDAG
    S.activeSrc S.activeDst S.activeInput S.activeOutput S.activeGraph_dag
  rcases hdag.2.2 (activeSplitRetract S R v) with heq | hpath
  · left
    calc
      v = activeSplitEmbed S R (activeSplitRetract S R v) :=
        (activeSplitEmbed_retract S R v hv).symm
      _ = activeSplitEmbed S R ⟨S.activeOutput, true⟩ := congrArg (activeSplitEmbed S R) heq
      _ = _ := activeSplitEmbed_output S R
  · right
    have h := hpath.lift (activeSplitEmbed S R) (fun _ _ h => activeSplitEmbed_step S R h)
    simpa only [Function.onFun, activeSplitEmbed_output, activeSplitEmbed_retract S R v hv] using h

end Problem56.PaperV6
