import Problem56.PaperV6.GeneralBridgelessCurrentEar
import Problem56.PaperV6.GeneralBridgelessActiveSplitState

namespace Problem56.PaperV6
namespace OriginalFreshEar

variable {G : FiniteBoundaryGraph} {S : GeneralBridgelessState G}

theorem edge_not_active (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    ¬ constructionActiveEdge S.current S.oldEdge S.used (S.oldEdge (P.edge i)) := by
  rintro (haux | ⟨f, hf, hfe⟩)
  · exact haux ⟨P.edge i, rfl⟩
  · exact P.edge_fresh i ((S.oldEdge_injective hfe) ▸ hf)

theorem last_source_active (P : OriginalFreshEar S)
    (h : P.currentReversed (Fin.last P.internalCount) = true) :
    S.projection (S.current.src (S.oldEdge (P.edge (Fin.last P.internalCount)))) ∈ S.active := by
  have hp := P.currentHead_projection (Fin.last P.internalCount)
  simp only [currentHead, h, orientedHead, Fin.succ_last] at hp
  rw [hp]
  exact P.finish_active

theorem last_target_active (P : OriginalFreshEar S)
    (h : P.currentReversed (Fin.last P.internalCount) = false) :
    S.projection (S.current.dst (S.oldEdge (P.edge (Fin.last P.internalCount)))) ∈ S.active := by
  have hp := P.currentHead_projection (Fin.last P.internalCount)
  simp only [currentHead, h, orientedHead, Fin.succ_last] at hp
  rw [hp]
  exact P.finish_active

/-- Keep all old active incidences in their standard incoming/outgoing copies.
The new ear uses false copies until its last incidence, which uses true. This
separates the endpoints even for a closed original ear or a single loop. -/
noncomputable def splitRouting (P : OriginalFreshEar S) : ActiveSplitRouting S := by
  classical
  refine {
    srcCopy := fun e => if ha : constructionActiveEdge S.current S.oldEdge S.used e then
      ⟨true, Or.inr (S.active_edge_endpoints e ha).1⟩
      else if hl : e = S.oldEdge (P.edge (Fin.last P.internalCount)) ∧
          P.currentReversed (Fin.last P.internalCount) = true then
        ⟨true, Or.inr (by rw [hl.1]; exact P.last_source_active hl.2)⟩
      else activeSplitRoot S _
    dstCopy := fun e => if hl : e = S.oldEdge (P.edge (Fin.last P.internalCount)) ∧
          P.currentReversed (Fin.last P.internalCount) = false then
        ⟨true, Or.inr (by rw [hl.1]; exact P.last_target_active hl.2)⟩
      else activeSplitRoot S _
    source_active := ?_
    target_active := ?_ }
  · intro e he
    simp only [dif_pos he]
  · intro e he
    have hn : ¬ (e = S.oldEdge (P.edge (Fin.last P.internalCount)) ∧
        P.currentReversed (Fin.last P.internalCount) = false) := by
      rintro ⟨hl, _⟩
      exact P.edge_not_active _ (hl ▸ he)
    simp only [dif_neg hn, activeSplitRoot]

theorem splitRouting_source (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    (P.splitRouting.srcCopy (S.oldEdge (P.edge i))).1 =
      if i = Fin.last P.internalCount ∧ P.currentReversed i = true then true else false := by
  classical
  have hi : S.oldEdge (P.edge i) = S.oldEdge (P.edge (Fin.last P.internalCount)) ↔
      i = Fin.last P.internalCount :=
    ⟨fun h => P.edge_injective (S.oldEdge_injective h), fun h => congrArg (fun j => S.oldEdge (P.edge j)) h⟩
  simp only [splitRouting, dif_neg (P.edge_not_active i), hi]
  by_cases h : i = Fin.last P.internalCount
  · subst i
    simp only [true_and]
    split <;> rfl
  · simp only [h, false_and, ↓reduceDIte, ↓reduceIte, activeSplitRoot]

theorem splitRouting_target (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    (P.splitRouting.dstCopy (S.oldEdge (P.edge i))).1 =
      if i = Fin.last P.internalCount ∧ P.currentReversed i = false then true else false := by
  classical
  have hi : S.oldEdge (P.edge i) = S.oldEdge (P.edge (Fin.last P.internalCount)) ↔
      i = Fin.last P.internalCount :=
    ⟨fun h => P.edge_injective (S.oldEdge_injective h), fun h => congrArg (fun j => S.oldEdge (P.edge j)) h⟩
  simp only [splitRouting, hi]
  by_cases h : i = Fin.last P.internalCount
  · subst i
    simp only [true_and]
    split <;> rfl
  · simp only [h, false_and, ↓reduceDIte, ↓reduceIte, activeSplitRoot]

end OriginalFreshEar
end Problem56.PaperV6
