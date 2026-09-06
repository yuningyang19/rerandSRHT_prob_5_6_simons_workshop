import Problem56.PaperV6.GeneralBridgelessEarStateData

namespace Problem56.PaperV6
namespace StateFreshEar

variable {G : FiniteBoundaryGraph} {S : GeneralBridgelessState G}

/-- An explicit strict topological rank on the already constructed active DAG.
This finite helper transports across a permitted reversal of unused edges;
the construction must supply the witness before activating an ear. -/
def Ordered (P : StateFreshEar S) : Prop :=
  ∃ rank : S.ActiveVertex → ℕ,
    (∀ e : S.ActiveEdge, rank (S.activeSrc e) < rank (S.activeDst e)) ∧
      rank P.start < rank P.finish

theorem vertexEmbed_step (P : StateFreshEar S)
    {a b : AdjoinedEarVertex S.ActiveVertex P.internalCount}
    (h : directedAdjacent
      (adjoinedEarSrc S.activeSrc P.start P.finish P.internalCount)
      (adjoinedEarDst S.activeDst P.start P.finish P.internalCount) a b) :
    constructionAdjacent S.current S.oldEdge P.newUsed (P.vertexEmbed a) (P.vertexEmbed b) := by
  obtain ⟨e, hs, ht⟩ := h
  exact ⟨P.edgeEmbed e, (P.edgeEmbed_src e).symm.trans (congrArg P.vertexEmbed hs),
    (P.edgeEmbed_dst e).symm.trans (congrArg P.vertexEmbed ht), P.edgeEmbed_active e⟩

theorem vertexRetract_step (P : StateFreshEar S) {a b : S.current.Vertex}
    (h : constructionAdjacent S.current S.oldEdge P.newUsed a b) :
    directedAdjacent
      (adjoinedEarSrc S.activeSrc P.start P.finish P.internalCount)
      (adjoinedEarDst S.activeDst P.start P.finish P.internalCount)
      (P.vertexRetract a) (P.vertexRetract b) := by
  obtain ⟨e, hs, ht, he⟩ := h
  obtain ⟨q, hq⟩ := P.edgeEmbed_surjective_active e he
  rw [← hq, ← P.edgeEmbed_src] at hs
  rw [← hq, ← P.edgeEmbed_dst] at ht
  refine ⟨q, ?_, ?_⟩
  · simpa only [vertexRetract_embed] using congrArg P.vertexRetract hs
  · simpa only [vertexRetract_embed] using congrArg P.vertexRetract ht

theorem adjoined_dag (P : StateFreshEar S) (horder : P.Ordered) :
    MingoAdmissibleDAG
      (adjoinedEarSrc S.activeSrc P.start P.finish P.internalCount)
      (adjoinedEarDst S.activeDst P.start P.finish P.internalCount)
      (Sum.inl S.activeInput) (Sum.inl S.activeOutput) := by
  classical
  obtain ⟨rank, hedge, hlt⟩ := horder
  exact adjoinedEar_mingoAdmissibleDAG S.activeSrc S.activeDst S.activeInput S.activeOutput
    S.activeGraph_dag rank hedge P.start P.finish hlt P.internalCount

theorem partial_acyclic (P : StateFreshEar S) (horder : P.Ordered) (v : S.current.Vertex) :
    ¬ Relation.TransGen (constructionAdjacent S.current S.oldEdge P.newUsed) v v := by
  intro hcycle
  exact (P.adjoined_dag horder).1 _
    (hcycle.lift P.vertexRetract (fun _ _ h => P.vertexRetract_step h))

theorem partial_from_input (P : StateFreshEar S) (horder : P.Ordered)
    (v : S.current.Vertex) (hv : S.projection v ∈ P.newActive) :
    v = S.current.input ∨
      Relation.TransGen (constructionAdjacent S.current S.oldEdge P.newUsed) S.current.input v := by
  rcases (P.adjoined_dag horder).2.1 (P.vertexRetract v) with heq | hpath
  · left
    calc
      v = P.vertexEmbed (P.vertexRetract v) := (P.vertexEmbed_retract v hv).symm
      _ = P.vertexEmbed (Sum.inl S.activeInput) := congrArg P.vertexEmbed heq
      _ = _ := rfl
  · right
    have h := hpath.lift P.vertexEmbed (fun _ _ h => P.vertexEmbed_step h)
    have hi : P.vertexEmbed (Sum.inl S.activeInput) = S.current.input := rfl
    simpa only [Function.onFun, hi, P.vertexEmbed_retract v hv] using h

theorem partial_to_output (P : StateFreshEar S) (horder : P.Ordered)
    (v : S.current.Vertex) (hv : S.projection v ∈ P.newActive) :
    v = S.current.output ∨
      Relation.TransGen (constructionAdjacent S.current S.oldEdge P.newUsed) v S.current.output := by
  rcases (P.adjoined_dag horder).2.2 (P.vertexRetract v) with heq | hpath
  · left
    calc
      v = P.vertexEmbed (P.vertexRetract v) := (P.vertexEmbed_retract v hv).symm
      _ = P.vertexEmbed (Sum.inl S.activeOutput) := congrArg P.vertexEmbed heq
      _ = _ := rfl
  · right
    have h := hpath.lift P.vertexEmbed (fun _ _ h => P.vertexEmbed_step h)
    have ho : P.vertexEmbed (Sum.inl S.activeOutput) = S.current.output := rfl
    simpa only [Function.onFun, ho, P.vertexEmbed_retract v hv] using h

end StateFreshEar
end Problem56.PaperV6
