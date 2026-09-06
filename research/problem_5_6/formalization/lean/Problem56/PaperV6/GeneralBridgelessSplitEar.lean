import Problem56.PaperV6.GeneralBridgelessSplitEarRouting
import Problem56.PaperV6.GeneralBridgelessUnorientedEar

namespace Problem56.PaperV6

theorem activeSplitVertex_ext {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (R : ActiveSplitRouting S) (a b : (activeSplitGraph S R).Vertex)
    (hv : a.1 = b.1) (hc : a.2.1 = b.2.1) : a = b := by
  rcases a with ⟨v, c⟩
  rcases b with ⟨w, d⟩
  dsimp only at hv hc
  subst w
  have hcd : c = d := Subtype.ext hc
  subst d
  rfl

namespace OriginalFreshEar

variable {G : FiniteBoundaryGraph} {S : GeneralBridgelessState G}

noncomputable def splitPoint (P : OriginalFreshEar S) (i : Fin (P.internalCount + 2)) :
    (activeSplitGraph S P.splitRouting).Vertex := by
  classical
  refine ⟨P.currentPoint i, ?_⟩
  exact if h : i = Fin.last (P.internalCount + 1) then
    ⟨true, Or.inr (by rw [P.currentPoint_projection, h]; exact P.finish_active)⟩
  else activeSplitRoot S _

@[simp] theorem splitPoint_fst (P : OriginalFreshEar S) (i : Fin (P.internalCount + 2)) :
    (P.splitPoint i).1 = P.currentPoint i := rfl

theorem splitPoint_side (P : OriginalFreshEar S) (i : Fin (P.internalCount + 2)) :
    (P.splitPoint i).2.1 = if i = Fin.last (P.internalCount + 1) then true else false := by
  classical
  simp only [splitPoint]
  split <;> rfl

theorem splitPoint_projection (P : OriginalFreshEar S) (i : Fin (P.internalCount + 2)) :
    activeSplitProjection S P.splitRouting (P.splitPoint i) = P.point i :=
  P.currentPoint_projection i

theorem splitPoint_injective (P : OriginalFreshEar S) : Function.Injective P.splitPoint := by
  classical
  intro i j hij
  have hp : P.point i = P.point j := by
    simpa only [P.splitPoint_projection] using congrArg (activeSplitProjection S P.splitRouting) hij
  rcases P.point_eq_or_endpoints i j hp with heq | ⟨hi, hj⟩ | ⟨hj, hi⟩
  · exact heq
  · exfalso
    have hs := congrArg (fun v : (activeSplitGraph S P.splitRouting).Vertex => v.2.1) hij
    rw [P.splitPoint_side, P.splitPoint_side, hi, hj] at hs
    have hn : (0 : Fin (P.internalCount + 2)) ≠ Fin.last (P.internalCount + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    simp only [hn, ↓reduceIte] at hs
    exact Bool.noConfusion hs
  · exfalso
    have hs := congrArg (fun v : (activeSplitGraph S P.splitRouting).Vertex => v.2.1) hij
    rw [P.splitPoint_side, P.splitPoint_side, hi, hj] at hs
    have hn : (0 : Fin (P.internalCount + 2)) ≠ Fin.last (P.internalCount + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    simp only [hn, ↓reduceIte] at hs
    exact Bool.noConfusion hs

theorem split_tail (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    orientedTail (activeSplitGraph S P.splitRouting).src (activeSplitGraph S P.splitRouting).dst
      (activeSplitOldEdge S P.splitRouting (P.edge i), P.currentReversed i) = P.splitPoint i.castSucc := by
  classical
  apply activeSplitVertex_ext S P.splitRouting
  · rw [P.splitPoint_fst, P.currentPoint_castSucc]
    cases hb : P.currentReversed i
    · change S.current.src (S.oldEdge (P.edge i)) = P.currentTail i
      simp only [currentTail, hb, orientedTail]
    · change S.current.dst (S.oldEdge (P.edge i)) = P.currentTail i
      simp only [currentTail, hb, orientedTail]
  · have hn : i.castSucc ≠ Fin.last (P.internalCount + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      omega
    rw [P.splitPoint_side, if_neg hn]
    cases hb : P.currentReversed i
    · change (P.splitRouting.srcCopy (S.oldEdge (P.edge i))).1 = false
      rw [P.splitRouting_source]
      simp only [hb, Bool.false_eq_true, and_false, ↓reduceIte]
    · change (P.splitRouting.dstCopy (S.oldEdge (P.edge i))).1 = false
      rw [P.splitRouting_target]
      simp only [hb, Bool.true_eq_false, and_false, ↓reduceIte]

theorem split_head (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    orientedHead (activeSplitGraph S P.splitRouting).src (activeSplitGraph S P.splitRouting).dst
      (activeSplitOldEdge S P.splitRouting (P.edge i), P.currentReversed i) = P.splitPoint i.succ := by
  classical
  apply activeSplitVertex_ext S P.splitRouting
  · rw [P.splitPoint_fst, P.currentPoint_succ]
    cases hb : P.currentReversed i
    · change S.current.dst (S.oldEdge (P.edge i)) = P.currentHead i
      simp only [currentHead, hb, orientedHead]
    · change S.current.src (S.oldEdge (P.edge i)) = P.currentHead i
      simp only [currentHead, hb, orientedHead]
  · rw [P.splitPoint_side]
    cases hb : P.currentReversed i
    · change (P.splitRouting.dstCopy (S.oldEdge (P.edge i))).1 = _
      rw [P.splitRouting_target]
      simp only [hb, and_true, ← Fin.succ_last, Fin.succ_inj]
    · change (P.splitRouting.srcCopy (S.oldEdge (P.edge i))).1 = _
      rw [P.splitRouting_source]
      simp only [hb, and_true, ← Fin.succ_last, Fin.succ_inj]

/-- The selected original ear becomes a vertex-simple current ear after one
actual permitted active-vertex split, including the closed-ear case. -/
noncomputable def splitEar (P : OriginalFreshEar S) : StateUnorientedEar (S.splitActive P.splitRouting) where
  internalCount := P.internalCount
  point := P.splitPoint
  edge := P.edge
  reversed := P.currentReversed
  point_injective := P.splitPoint_injective
  edge_injective := P.edge_injective
  edge_fresh := P.edge_fresh
  tail := P.split_tail
  head := P.split_head
  start_active := by
    change activeSplitProjection S P.splitRouting (P.splitPoint 0) ∈ S.active
    rw [P.splitPoint_projection]
    exact P.start_active
  finish_active := by
    change activeSplitProjection S P.splitRouting (P.splitPoint _) ∈ S.active
    rw [P.splitPoint_projection]
    exact P.finish_active
  internal_inactive := by
    intro i
    change activeSplitProjection S P.splitRouting (P.splitPoint _) ∉ S.active
    rw [P.splitPoint_projection]
    exact P.internal_inactive i

theorem exists_progress (P : OriginalFreshEar S) :
    ∃ T : GeneralBridgelessState G, T.remaining < S.remaining :=
  P.splitEar.exists_progress

end OriginalFreshEar
end Problem56.PaperV6
