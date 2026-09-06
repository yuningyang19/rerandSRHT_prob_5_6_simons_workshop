import Problem56.PaperV6.GeneralBridgelessIndexedPaths
import Problem56.PaperV6.GeneralBridgelessDAGSplit

namespace Problem56.PaperV6
namespace VertexSimpleIndexedPath

variable {ι ε : Type*} {src dst : ε → ι} {a b : ι}

noncomputable def globalReversal (P : VertexSimpleIndexedPath src dst a b) (e : ε) : Bool := by
  classical
  exact if h : ∃ i, P.edge i = e then P.reversed (Classical.choose h) else false

theorem globalReversal_edge (P : VertexSimpleIndexedPath src dst a b) (i : Fin P.length) :
    P.globalReversal (P.edge i) = P.reversed i := by
  classical
  have h : ∃ j, P.edge j = P.edge i := ⟨i, rfl⟩
  simp only [globalReversal, dif_pos h]
  exact congrArg P.reversed (P.edge_injective (Classical.choose_spec h))

def pathAdjacent (P : VertexSimpleIndexedPath src dst a b) (x y : ι) : Prop :=
  ∃ i : Fin P.length, P.point i.castSucc = x ∧ P.point i.succ = y

noncomputable def pointRank (P : VertexSimpleIndexedPath src dst a b) (v : ι) : ℕ := by
  classical
  exact if h : v ∈ Set.range P.point then (Classical.choose h).1 else 0

theorem pointRank_point (P : VertexSimpleIndexedPath src dst a b)
    (i : Fin (P.length + 1)) : P.pointRank (P.point i) = i.1 := by
  classical
  have h : P.point i ∈ Set.range P.point := ⟨i, rfl⟩
  simp only [pointRank, dif_pos h]
  exact congrArg Fin.val (P.point_injective (Classical.choose_spec h))

theorem path_acyclic (P : VertexSimpleIndexedPath src dst a b) (v : ι) :
    ¬ Relation.TransGen P.pathAdjacent v v := by
  intro hcycle
  have hstrict : ∀ i : Fin P.length,
      P.pointRank (P.point i.castSucc) < P.pointRank (P.point i.succ) := by
    intro i
    rw [P.pointRank_point, P.pointRank_point]
    simp
  exact (Nat.lt_irrefl _) (transGen_strict_rank
    (fun i : Fin P.length => P.point i.castSucc)
    (fun i : Fin P.length => P.point i.succ) P.pointRank hstrict hcycle)

theorem path_from_start (P : VertexSimpleIndexedPath src dst a b)
    (i : Fin (P.length + 1)) : Relation.ReflTransGen P.pathAdjacent a (P.point i) := by
  induction i using Fin.induction with
  | zero => rw [P.first]
  | succ i ih => exact ih.tail ⟨i, rfl, rfl⟩

theorem path_to_end (P : VertexSimpleIndexedPath src dst a b)
    (i : Fin (P.length + 1)) : Relation.ReflTransGen P.pathAdjacent (P.point i) b := by
  induction i using Fin.reverseInduction with
  | last => rw [P.last]
  | cast i ih => exact ih.head ⟨i, rfl, rfl⟩

theorem edge_endpoints_mem (P : VertexSimpleIndexedPath src dst a b)
    (i : Fin P.length) : src (P.edge i) ∈ Set.range P.point ∧
      dst (P.edge i) ∈ Set.range P.point := by
  have ht := P.tail i
  have hh := P.head i
  cases h : P.reversed i with
  | false =>
    simp only [h, orientedTail, orientedHead] at ht hh
    exact ⟨⟨i.castSucc, ht.symm⟩, ⟨i.succ, hh.symm⟩⟩
  | true =>
    simp only [h, orientedTail, orientedHead] at ht hh
    exact ⟨⟨i.succ, hh.symm⟩, ⟨i.castSucc, ht.symm⟩⟩

end VertexSimpleIndexedPath
end Problem56.PaperV6
