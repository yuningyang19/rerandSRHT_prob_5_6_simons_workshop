import Problem56.PaperV6.GeneralBridgelessOriginalEar

namespace Problem56.PaperV6
namespace OriginalFreshEar

variable {G : FiniteBoundaryGraph} {S : GeneralBridgelessState G}

def currentReversed (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) : Bool :=
  Bool.xor (S.reversed (P.edge i)) (P.reversed i)

def currentTail (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) : S.current.Vertex :=
  orientedTail S.current.src S.current.dst (S.oldEdge (P.edge i), P.currentReversed i)

def currentHead (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) : S.current.Vertex :=
  orientedHead S.current.src S.current.dst (S.oldEdge (P.edge i), P.currentReversed i)

theorem currentTail_projection (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    S.projection (P.currentTail i) = P.point i.castSucc := by
  have hs := S.source_projection (P.edge i)
  have ht := S.target_projection (P.edge i)
  have hp := P.tail i
  cases ho : S.reversed (P.edge i) <;> cases hn : P.reversed i
  all_goals simp_all [currentTail, currentReversed, orientedTail, orientedHead]

theorem currentHead_projection (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    S.projection (P.currentHead i) = P.point i.succ := by
  have hs := S.source_projection (P.edge i)
  have ht := S.target_projection (P.edge i)
  have hp := P.head i
  cases ho : S.reversed (P.edge i) <;> cases hn : P.reversed i
  all_goals simp_all [currentHead, currentReversed, orientedTail, orientedHead]

def currentPoint (P : OriginalFreshEar S) (i : Fin (P.internalCount + 2)) : S.current.Vertex :=
  if h : i.1 < P.internalCount + 1 then P.currentTail ⟨i.1, h⟩
  else P.currentHead (Fin.last P.internalCount)

@[simp] theorem currentPoint_castSucc (P : OriginalFreshEar S)
    (i : Fin (P.internalCount + 1)) : P.currentPoint i.castSucc = P.currentTail i := by
  simp [currentPoint, i.isLt]

@[simp] theorem currentPoint_last (P : OriginalFreshEar S) :
    P.currentPoint (Fin.last (P.internalCount + 1)) = P.currentHead (Fin.last P.internalCount) := by
  simp [currentPoint]

theorem currentPoint_projection (P : OriginalFreshEar S) (i : Fin (P.internalCount + 2)) :
    S.projection (P.currentPoint i) = P.point i := by
  by_cases h : i.1 < P.internalCount + 1
  · have hi : (⟨i.1, h⟩ : Fin (P.internalCount + 1)).castSucc = i := rfl
    simp only [currentPoint, dif_pos h, P.currentTail_projection, hi]
  · have hi : i = Fin.last (P.internalCount + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    simpa only [currentPoint_last, Fin.succ_last] using P.currentHead_projection (Fin.last P.internalCount)

theorem currentPoint_succ (P : OriginalFreshEar S) (i : Fin (P.internalCount + 1)) :
    P.currentPoint i.succ = P.currentHead i := by
  by_cases h : i.1 < P.internalCount
  · have hout : P.point i.succ ∉ S.active := P.internal_inactive ⟨i.1, h⟩
    exact S.outside_fiber_unique (P.point i.succ) hout _ _
      (P.currentPoint_projection i.succ) (P.currentHead_projection i)
  · have hi : i = Fin.last P.internalCount := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    simpa only [Fin.succ_last] using P.currentPoint_last

theorem point_eq_or_endpoints (P : OriginalFreshEar S)
    (i j : Fin (P.internalCount + 2)) (h : P.point i = P.point j) :
    i = j ∨ (i = 0 ∧ j = Fin.last (P.internalCount + 1)) ∨
      (j = 0 ∧ i = Fin.last (P.internalCount + 1)) := by
  by_cases hi : i.1 = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst i
    by_cases hj0 : j.1 = 0
    · exact Or.inl (Fin.ext hj0).symm
    · by_cases hjl : j.1 = P.internalCount + 1
      · exact Or.inr (Or.inl ⟨rfl, Fin.ext hjl⟩)
      · exfalso
        let k : Fin P.internalCount := ⟨j.1 - 1, by omega⟩
        have hj : (⟨k.1 + 1, by omega⟩ : Fin (P.internalCount + 2)) = j := by
          apply Fin.ext
          dsimp [k]
          omega
        apply P.internal_inactive k
        rw [hj, ← h]
        exact P.start_active
  · by_cases hj : j.1 = 0
    · have hj0 : j = 0 := Fin.ext hj
      subst j
      by_cases hil : i.1 = P.internalCount + 1
      · exact Or.inr (Or.inr ⟨rfl, Fin.ext hil⟩)
      · exfalso
        let k : Fin P.internalCount := ⟨i.1 - 1, by omega⟩
        have hik : (⟨k.1 + 1, by omega⟩ : Fin (P.internalCount + 2)) = i := by
          apply Fin.ext
          dsimp [k]
          omega
        apply P.internal_inactive k
        rw [hik, h]
        exact P.start_active
    · left
      let i' : Fin (P.internalCount + 1) := ⟨i.1 - 1, by omega⟩
      let j' : Fin (P.internalCount + 1) := ⟨j.1 - 1, by omega⟩
      have hi' : i'.succ = i := Fin.ext (by dsimp [i']; omega)
      have hj' : j'.succ = j := Fin.ext (by dsimp [j']; omega)
      have h' : i' = j' := P.return_injective (by simpa only [hi', hj'] using h)
      exact hi'.symm.trans ((congrArg Fin.succ h').trans hj')

end OriginalFreshEar
end Problem56.PaperV6
