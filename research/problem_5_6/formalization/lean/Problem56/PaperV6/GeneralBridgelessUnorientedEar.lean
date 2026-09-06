import Problem56.PaperV6.GeneralBridgelessEarActivation
import Problem56.PaperV6.GeneralBridgelessReverseUnused

namespace Problem56.PaperV6

/-- A concrete fresh path in the current full graph, allowing either native
orientation on each edge. The construction below performs the actual reversals. -/
structure StateUnorientedEar {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G) where
  internalCount : ℕ
  point : Fin (internalCount + 2) → S.current.Vertex
  edge : Fin (internalCount + 1) → G.Edge
  reversed : Fin (internalCount + 1) → Bool
  point_injective : Function.Injective point
  edge_injective : Function.Injective edge
  edge_fresh : ∀ i, edge i ∉ S.used
  tail : ∀ i, orientedTail S.current.src S.current.dst (S.oldEdge (edge i), reversed i) = point i.castSucc
  head : ∀ i, orientedHead S.current.src S.current.dst (S.oldEdge (edge i), reversed i) = point i.succ
  start_active : S.projection (point 0) ∈ S.active
  finish_active : S.projection (point (Fin.last (internalCount + 1))) ∈ S.active
  internal_inactive : ∀ i : Fin internalCount,
    S.projection (point ⟨i.1 + 1, by omega⟩) ∉ S.active

namespace StateUnorientedEar

variable {G : FiniteBoundaryGraph} {S : GeneralBridgelessState G}

def start (P : StateUnorientedEar S) : S.ActiveVertex := ⟨P.point 0, P.start_active⟩
def finish (P : StateUnorientedEar S) : S.ActiveVertex :=
  ⟨P.point (Fin.last (P.internalCount + 1)), P.finish_active⟩

def reverse (P : StateUnorientedEar S) : StateUnorientedEar S where
  internalCount := P.internalCount
  point := fun i => P.point i.rev
  edge := fun i => P.edge i.rev
  reversed := fun i => !(P.reversed i.rev)
  point_injective := P.point_injective.comp Fin.rev_injective
  edge_injective := P.edge_injective.comp Fin.rev_injective
  edge_fresh := fun i => P.edge_fresh i.rev
  tail := by
    intro i
    rw [Fin.rev_castSucc]
    have h := P.head i.rev
    cases hb : P.reversed i.rev <;> simpa [hb, orientedTail, orientedHead] using h
  head := by
    intro i
    rw [Fin.rev_succ]
    have h := P.tail i.rev
    cases hb : P.reversed i.rev <;> simpa [hb, orientedTail, orientedHead] using h
  start_active := by simpa only [Fin.rev_zero] using P.finish_active
  finish_active := by simpa only [Fin.rev_last] using P.start_active
  internal_inactive := by
    intro i
    have hi : (⟨i.1 + 1, by omega⟩ : Fin (P.internalCount + 2)).rev =
        ⟨i.rev.1 + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hi]
    exact P.internal_inactive i.rev

noncomputable def reversal (P : StateUnorientedEar S) (e : S.current.Edge) : Bool := by
  classical
  exact if h : ∃ i, S.oldEdge (P.edge i) = e then P.reversed (Classical.choose h) else false

@[simp] theorem reversal_edge (P : StateUnorientedEar S) (i : Fin (P.internalCount + 1)) :
    P.reversal (S.oldEdge (P.edge i)) = P.reversed i := by
  classical
  have h : ∃ j, S.oldEdge (P.edge j) = S.oldEdge (P.edge i) := ⟨i, rfl⟩
  have hi : Classical.choose h = i :=
    P.edge_injective (S.oldEdge_injective (Classical.choose_spec h))
  simp only [reversal, dif_pos h, hi]

theorem reversal_fixed (P : StateUnorientedEar S) (e : S.current.Edge)
    (he : constructionActiveEdge S.current S.oldEdge S.used e) : P.reversal e = false := by
  classical
  have hnot : ¬ ∃ i, S.oldEdge (P.edge i) = e := by
    rintro ⟨i, hi⟩
    rcases he with haux | ⟨f, hf, hfe⟩
    · exact haux ⟨P.edge i, hi⟩
    · have hfi : f = P.edge i := S.oldEdge_injective (hfe.trans hi.symm)
      exact P.edge_fresh i (hfi ▸ hf)
  simp only [reversal, dif_neg hnot]

noncomputable def oriented (P : StateUnorientedEar S) :
    StateFreshEar (S.reverseUnused P.reversal P.reversal_fixed) where
  internalCount := P.internalCount
  point := P.point
  edge := P.edge
  point_injective := P.point_injective
  edge_fresh := P.edge_fresh
  source := by
    intro i
    change orientedTail S.current.src S.current.dst
      (S.oldEdge (P.edge i), P.reversal (S.oldEdge (P.edge i))) = P.point i.castSucc
    rw [P.reversal_edge]
    exact P.tail i
  target := by
    intro i
    change orientedHead S.current.src S.current.dst
      (S.oldEdge (P.edge i), P.reversal (S.oldEdge (P.edge i))) = P.point i.succ
    rw [P.reversal_edge]
    exact P.head i
  start_active := P.start_active
  finish_active := P.finish_active
  internal_inactive := P.internal_inactive

theorem oriented_ordered (P : StateUnorientedEar S)
    (rank : S.ActiveVertex → ℕ)
    (hedge : ∀ e : S.ActiveEdge, rank (S.activeSrc e) < rank (S.activeDst e))
    (horder : rank P.start < rank P.finish) : P.oriented.Ordered := by
  classical
  refine ⟨rank, ?_, horder⟩
  intro e
  let T := S.reverseUnused P.reversal P.reversal_fixed
  have hadj : constructionAdjacent T.current T.oldEdge T.used
      (T.current.src e.1) (T.current.dst e.1) := ⟨e.1, rfl, rfl, e.2⟩
  change constructionAdjacent (S.current.reverse P.reversal)
    (reverseStateOldEdge S P.reversal) S.used _ _ at hadj
  rw [reverseState_adjacency S P.reversal P.reversal_fixed] at hadj
  obtain ⟨f, hs, ht, hf⟩ := hadj
  have h := hedge ⟨f, hf⟩
  have hs' : S.activeSrc ⟨f, hf⟩ = T.activeSrc e := Subtype.ext hs
  have ht' : S.activeDst ⟨f, hf⟩ = T.activeDst e := Subtype.ext ht
  simpa only [hs', ht'] using h

theorem exists_progress (P : StateUnorientedEar S) :
    ∃ T : GeneralBridgelessState G, T.remaining < S.remaining := by
  classical
  let rank := distinctDAGRank S.activeSrc S.activeDst
  have hedge := distinctDAGRank_edge_lt S.activeSrc S.activeDst
    S.activeInput S.activeOutput S.activeGraph_dag
  have hne : P.start ≠ P.finish := by
    intro heq
    have h := P.point_injective (congrArg Subtype.val heq)
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  rcases distinctDAGRank_orders_endpoints S.activeSrc S.activeDst P.start P.finish hne with h | h
  · let R := S.reverseUnused P.reversal P.reversal_fixed
    have ho := P.oriented_ordered rank hedge h
    exact ⟨R.activateEar P.oriented ho, R.activateEar_remaining_lt P.oriented ho⟩
  · have hzero : (0 : Fin (P.internalCount + 2)).rev = Fin.last (P.internalCount + 1) :=
      Fin.rev_zero _
    have hstart : P.reverse.start = P.finish := by
      apply Subtype.ext
      change P.point ((0 : Fin (P.internalCount + 2)).rev) =
        P.point (Fin.last (P.internalCount + 1))
      rw [hzero]
    have hfinish : P.reverse.finish = P.start := by
      apply Subtype.ext
      change P.point ((Fin.last (P.internalCount + 1)).rev) = P.point 0
      rw [Fin.rev_last]
    have hreverse : rank P.reverse.start < rank P.reverse.finish := by
      rw [hstart, hfinish]
      exact h
    let R := S.reverseUnused P.reverse.reversal P.reverse.reversal_fixed
    have ho := P.reverse.oriented_ordered rank hedge hreverse
    exact ⟨R.activateEar P.reverse.oriented ho,
      R.activateEar_remaining_lt P.reverse.oriented ho⟩

end StateUnorientedEar
end Problem56.PaperV6
