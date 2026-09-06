import Problem56.PaperV6.GeneralBridgelessState

namespace Problem56.PaperV6

def reverseStateOldEdge {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (r : S.current.Edge → Bool) (e : G.Edge) : (S.current.reverse r).Edge :=
  selectiveReversalEquiv r (S.oldEdge e)

theorem reverseState_active_iff {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (r : S.current.Edge → Bool) (e : S.current.Edge) :
    constructionActiveEdge (S.current.reverse r) (reverseStateOldEdge S r) S.used
      (selectiveReversalEquiv r e) ↔ constructionActiveEdge S.current S.oldEdge S.used e := by
  let E := selectiveReversalEquiv r
  constructor
  · rintro (hnot | ⟨f, hf, hfe⟩)
    · left
      rintro ⟨f, hf⟩
      exact hnot ⟨f, congrArg E hf⟩
    · exact Or.inr ⟨f, hf, E.injective hfe⟩
  · rintro (hnot | ⟨f, hf, hfe⟩)
    · left
      rintro ⟨f, hf⟩
      exact hnot ⟨f, E.injective hf⟩
    · exact Or.inr ⟨f, hf, congrArg E hfe⟩

theorem reverseState_adjacency {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (r : S.current.Edge → Bool)
    (hfixed : ∀ e, constructionActiveEdge S.current S.oldEdge S.used e → r e = false) :
    constructionAdjacent (S.current.reverse r) (reverseStateOldEdge S r) S.used =
      constructionAdjacent S.current S.oldEdge S.used := by
  let E := selectiveReversalEquiv r
  have hs (e : S.current.Edge) (he : constructionActiveEdge S.current S.oldEdge S.used e) :
      (S.current.reverse r).src (E e) = S.current.src e := by
    change orientedTail S.current.src S.current.dst (e, r e) = _
    rw [hfixed e he]
    rfl
  have ht (e : S.current.Edge) (he : constructionActiveEdge S.current S.oldEdge S.used e) :
      (S.current.reverse r).dst (E e) = S.current.dst e := by
    change orientedHead S.current.src S.current.dst (e, r e) = _
    rw [hfixed e he]
    rfl
  funext a b
  apply propext
  constructor
  · rintro ⟨e, hsrc, hdst, he⟩
    let f := E.symm e
    have hef : E f = e := E.apply_symm_apply e
    have hf : constructionActiveEdge S.current S.oldEdge S.used f := by
      apply (reverseState_active_iff S r f).1
      change constructionActiveEdge (S.current.reverse r) (reverseStateOldEdge S r) S.used (E f)
      rw [hef]
      exact he
    refine ⟨f, ?_, ?_, hf⟩
    · exact (hs f hf).symm.trans (by simpa only [hef] using hsrc)
    · exact (ht f hf).symm.trans (by simpa only [hef] using hdst)
  · rintro ⟨e, hsrc, hdst, he⟩
    exact ⟨E e, (hs e he).trans hsrc, (ht e he).trans hdst,
      (reverseState_active_iff S r e).2 he⟩

/-- Reverse only unused edges of the current full graph. This is an actual
permitted graph/matrix modification; the partial active DAG is unchanged. -/
noncomputable def GeneralBridgelessState.reverseUnused {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (r : S.current.Edge → Bool)
    (hfixed : ∀ e, constructionActiveEdge S.current S.oldEdge S.used e → r e = false) :
    GeneralBridgelessState G := by
  classical
  let E := selectiveReversalEquiv r
  refine {
    current := S.current.reverse r
    history := S.history.tail (ElementaryBoundaryModification.reverse S.current r)
    projection := S.projection
    projection_surjective := S.projection_surjective
    oldEdge := reverseStateOldEdge S r
    oldEdge_injective := E.injective.comp S.oldEdge_injective
    reversed := fun e => Bool.xor (S.reversed e) (r (S.oldEdge e))
    source_projection := ?_
    target_projection := ?_
    input_projection := S.input_projection
    output_projection := S.output_projection
    active := S.active
    used := S.used
    input_active := S.input_active
    output_active := S.output_active
    used_endpoints_active := S.used_endpoints_active
    outside_fiber_unique := S.outside_fiber_unique
    auxiliary_endpoints_active := ?_
    partial_acyclic := ?_
    partial_from_input := ?_
    partial_to_output := ?_ }
  · intro e
    change S.projection (orientedTail S.current.src S.current.dst (S.oldEdge e, r (S.oldEdge e))) =
      orientedTail G.src G.dst (e, Bool.xor (S.reversed e) (r (S.oldEdge e)))
    have hs := S.source_projection e
    have ht := S.target_projection e
    cases ho : S.reversed e <;> cases hn : r (S.oldEdge e)
    all_goals simp_all [orientedTail, orientedHead]
  · intro e
    change S.projection (orientedHead S.current.src S.current.dst (S.oldEdge e, r (S.oldEdge e))) =
      orientedHead G.src G.dst (e, Bool.xor (S.reversed e) (r (S.oldEdge e)))
    have hs := S.source_projection e
    have ht := S.target_projection e
    cases ho : S.reversed e <;> cases hn : r (S.oldEdge e)
    all_goals simp_all [orientedTail, orientedHead]
  · intro e he
    let f := E.symm e
    have hef : E f = e := E.apply_symm_apply e
    have hnot : f ∉ Set.range S.oldEdge := by
      rintro ⟨g, hg⟩
      exact he ⟨g, (congrArg E hg).trans hef⟩
    have hends := S.auxiliary_endpoints_active f hnot
    rw [← hef]
    change S.projection (orientedTail S.current.src S.current.dst (f, r f)) ∈ S.active ∧
      S.projection (orientedHead S.current.src S.current.dst (f, r f)) ∈ S.active
    cases r f
    · exact hends
    · exact hends.symm
  · intro v
    change ¬ Relation.TransGen
      (constructionAdjacent (S.current.reverse r) (reverseStateOldEdge S r) S.used) v v
    rw [reverseState_adjacency S r hfixed]
    exact S.partial_acyclic v
  · intro v hv
    change v = S.current.input ∨ Relation.TransGen
      (constructionAdjacent (S.current.reverse r) (reverseStateOldEdge S r) S.used) S.current.input v
    rw [reverseState_adjacency S r hfixed]
    exact S.partial_from_input v hv
  · intro v hv
    change v = S.current.output ∨ Relation.TransGen
      (constructionAdjacent (S.current.reverse r) (reverseStateOldEdge S r) S.used) v S.current.output
    rw [reverseState_adjacency S r hfixed]
    exact S.partial_to_output v hv

@[simp] theorem GeneralBridgelessState.reverseUnused_remaining {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (r : S.current.Edge → Bool)
    (hfixed : ∀ e, constructionActiveEdge S.current S.oldEdge S.used e → r e = false) :
    (S.reverseUnused r hfixed).remaining = S.remaining := rfl

end Problem56.PaperV6
