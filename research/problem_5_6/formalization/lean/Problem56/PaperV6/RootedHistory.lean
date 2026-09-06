import Problem56.PaperV6.RootedHistoryBoundary

open scoped BigOperators Matrix Classical
namespace Problem56.PaperV6

 theorem boundaryEntriesPreserved_refl (G : FiniteBoundaryGraph) :
    BoundaryEntriesPreserved G G := by
  refine ⟨rfl, rfl, ?_⟩
  intro a b
  rfl

theorem boundaryEntriesPreserved_trans {G H K : FiniteBoundaryGraph}
    (hGH : BoundaryEntriesPreserved G H) (hHK : BoundaryEntriesPreserved H K) :
    BoundaryEntriesPreserved G K := by
  obtain ⟨hi, ho, hGH⟩ := hGH
  obtain ⟨hi', ho', hHK⟩ := hHK
  refine ⟨hi'.trans hi, ho'.trans ho, ?_⟩
  intro a b
  calc
    _ = boundaryGraphOperator H (Fin.cast hi.symm a) (Fin.cast ho.symm b) := by
      simpa only [Fin.cast_cast] using hHK (Fin.cast hi.symm a) (Fin.cast ho.symm b)
    _ = _ := hGH a b

theorem rooted_elementary : RootedElementaryExpected := by
  intro G H hmod
  cases hmod with
  | reverse rev =>
    have hb := graph_reversal_boundary G.Vertex G.Edge G.dim G.src G.dst G.matrix
      rev G.input G.output
    have hn := selectivelyReversedMatrix_norm_product_eq G.dim G.src G.dst G.matrix rev
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨rfl, rfl, ?_⟩
      intro a b
      exact congrFun (congrFun hb a) b
    · exact hn.le
    · intro hp
      exact ⟨hp, hn⟩
  | split copy root srcCopy dstCopy inputCopy outputCopy =>
    have hb := rooted_graph_boundary G.dim G.src G.dst G.matrix srcCopy dstCopy root
      G.input G.output inputCopy outputCopy
    have hn := rootedFiberSplitMatrix_norm_product_le
      G.dim G.src G.dst G.matrix srcCopy dstCopy root
    refine ⟨?_, hn, ?_⟩
    · refine ⟨rfl, rfl, ?_⟩
      intro a b
      exact congrFun (congrFun hb a) b
    · intro hp
      refine ⟨?_, rooted_graph_norm_product G.dim G.src G.dst G.matrix
        srcCopy dstCopy root hp⟩
      change ∀ v : FiberSplitVertex copy, 0 < G.dim v.1
      exact fun v ↦ hp v.1

theorem rooted_history : RootedHistoryExpected := by
  intro G H hmod
  change Relation.ReflTransGen ElementaryBoundaryModification G H at hmod
  induction hmod with
  | refl => exact ⟨boundaryEntriesPreserved_refl G, le_rfl, fun hp ↦ ⟨hp, rfl⟩⟩
  | @tail H K history step ih =>
    have hs := rooted_elementary H K step
    refine ⟨boundaryEntriesPreserved_trans ih.1 hs.1, hs.2.1.trans ih.2.1, ?_⟩
    intro hp
    obtain ⟨hH, heH⟩ := ih.2.2 hp
    obtain ⟨hK, heK⟩ := hs.2.2 hH
    exact ⟨hK, heK.trans heH⟩

/-- This theorem alone is a compositional bridge; the final consumer supplies
an actual closed construction of the permitted modification history. -/
theorem rooted_history_consequence : GeneralBridgelessConsequenceBridgeExpected := by
  intro htop ι ε _ _ _ dim src dst M u v hconn hdelete huv
  let G : FiniteBoundaryGraph :=
    { Vertex := ι, Edge := ε, vertexFintype := inferInstance,
      edgeFintype := inferInstance, vertexDecidableEq := inferInstance,
      dim := dim, src := src, dst := dst, matrix := M, input := u, output := v }
  obtain ⟨H, hmod, hio, hdag⟩ := htop G hconn hdelete huv
  obtain ⟨hb, hn, _⟩ := rooted_history G H hmod
  obtain ⟨hi, ho, hb⟩ := hb
  exact ⟨H.Vertex, H.Edge, H.vertexFintype, H.edgeFintype, H.vertexDecidableEq,
    H.dim, H.src, H.dst, H.matrix, H.input, H.output, hi, ho, hio, hdag, hb, hn⟩

end Problem56.PaperV6
