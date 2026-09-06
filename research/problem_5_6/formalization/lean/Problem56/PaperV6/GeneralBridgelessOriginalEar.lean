import Problem56.PaperV6.GeneralBridgelessIndexedPaths
import Problem56.PaperV6.GeneralBridgelessState

namespace Problem56.PaperV6

/-- Indexed original fresh-ear data. The return vertices are simple; the first
and last vertices may coincide, as required for a closed ear or a loop. -/
structure OriginalFreshEar {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G) where
  internalCount : ℕ
  point : Fin (internalCount + 2) → G.Vertex
  edge : Fin (internalCount + 1) → G.Edge
  reversed : Fin (internalCount + 1) → Bool
  return_injective : Function.Injective (fun i : Fin (internalCount + 1) => point i.succ)
  edge_injective : Function.Injective edge
  edge_fresh : ∀ i, edge i ∉ S.used
  tail : ∀ i, orientedTail G.src G.dst (edge i, reversed i) = point i.castSucc
  head : ∀ i, orientedHead G.src G.dst (edge i, reversed i) = point i.succ
  start_active : point 0 ∈ S.active
  finish_active : point (Fin.last (internalCount + 1)) ∈ S.active
  internal_inactive : ∀ i : Fin internalCount, point ⟨i.1 + 1, by omega⟩ ∉ S.active

theorem exists_originalFreshEar {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (hconn : GraphConnected G.src G.dst) (hbridge : EveryEdgeDeletionConnected G.src G.dst)
    (hfresh : ∃ e : G.Edge, e ∉ S.used) : Nonempty (OriginalFreshEar S) := by
  classical
  obtain ⟨x, z, y, e, l, hx, hy, he, henter, hchain, hlast, hnodup⟩ :=
    exists_fresh_ear_path G.src G.dst hconn hbridge S.active S.used
      S.used_endpoints_active ⟨G.input, S.input_active⟩ hfresh
  let rp : Fin (l.length + 1) → G.Vertex := (z :: l).get
  have hstep (i : Fin l.length) :
      rp i.castSucc ∉ S.active ∧ ∃ q : OrientedIndexedEdge G.Edge,
        q.1 ∉ S.used ∧ q.1 ≠ e ∧
          orientedTail G.src G.dst q = rp i.castSucc ∧
          orientedHead G.src G.dst q = rp i.succ := by
    have h := List.isChain_iff_getElem.mp hchain i.1 (by simp)
    obtain ⟨hout, f, hfresh, hne, hforward | hbackward⟩ := h
    · exact ⟨hout, (f, false), hfresh, hne, hforward⟩
    · exact ⟨hout, (f, true), hfresh, hne, hbackward.2, hbackward.1⟩
  let q : Fin l.length → OrientedIndexedEdge G.Edge := fun i => Classical.choose (hstep i).2
  have hq (i : Fin l.length) := Classical.choose_spec (hstep i).2
  let ret : VertexSimpleIndexedPath G.src G.dst z y := {
    length := l.length
    point := rp
    edge := fun i => (q i).1
    reversed := fun i => (q i).2
    first := rfl
    last := by simpa [rp, List.getLast_eq_getElem] using hlast
    point_injective := hnodup.injective_get
    tail := fun i => (hq i).2.2.1
    head := fun i => (hq i).2.2.2 }
  obtain ⟨b, hb⟩ : ∃ b : Bool,
      orientedTail G.src G.dst (e, b) = x ∧ orientedHead G.src G.dst (e, b) = z := by
    rcases henter with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h.2, h.1⟩
  let point : Fin (l.length + 2) → G.Vertex := Fin.cases x rp
  let edge : Fin (l.length + 1) → G.Edge := Fin.cases e ret.edge
  let reversed : Fin (l.length + 1) → Bool := Fin.cases b ret.reversed
  refine ⟨{
    internalCount := l.length
    point := point
    edge := edge
    reversed := reversed
    return_injective := ?_
    edge_injective := ?_
    edge_fresh := ?_
    tail := ?_
    head := ?_
    start_active := hx
    finish_active := ?_
    internal_inactive := ?_ }⟩
  · simpa [point] using ret.point_injective
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        rfl
      · intro hij
        exfalso
        exact (hq j).2.1 (by simpa [edge, ret] using hij.symm)
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exfalso
        exact (hq i).2.1 (by simpa [edge, ret] using hij)
      · intro hij
        exact congrArg Fin.succ (ret.edge_injective (by simpa [edge] using hij))
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact he
    · exact (hq i).1
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hb.1
    · simpa [edge, reversed, point, ret] using ret.tail i
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hb.2
    · simpa [edge, reversed, point, ret] using ret.head i
  · have hl : rp (Fin.last l.length) = y := by
      simpa [rp, List.getLast_eq_getElem] using hlast
    simpa [point, ← Fin.succ_last] using hl ▸ hy
  · intro i
    exact (hstep i).1

end Problem56.PaperV6
