import Problem56.PaperV6.GeneralBridgelessEars

namespace Problem56.PaperV6

/-- A vertex-simple path with all original edge indices and orientations
retained. The injectivity of the edge map is proved below from this data. -/
structure VertexSimpleIndexedPath {ι ε : Type*} (src dst : ε → ι) (a b : ι) where
  length : ℕ
  point : Fin (length + 1) → ι
  edge : Fin length → ε
  reversed : Fin length → Bool
  first : point 0 = a
  last : point (Fin.last length) = b
  point_injective : Function.Injective point
  tail : ∀ i, orientedTail src dst (edge i, reversed i) = point i.castSucc
  head : ∀ i, orientedHead src dst (edge i, reversed i) = point i.succ

theorem VertexSimpleIndexedPath.edge_injective {ι ε : Type*}
    {src dst : ε → ι} {a b : ι} (P : VertexSimpleIndexedPath src dst a b) :
    Function.Injective P.edge := by
  intro i j hij
  have hti := P.tail i
  have hhi := P.head i
  have htj := P.tail j
  have hhj := P.head j
  rw [hij] at hti hhi
  cases hi : P.reversed i <;> cases hj : P.reversed j
  all_goals simp only [hi, hj, orientedTail, orientedHead] at hti hhi htj hhj
  · have hpoints : P.point i.castSucc = P.point j.castSucc := by
      simpa [hi, hj, orientedTail] using hti.symm.trans htj
    exact Fin.ext (congrArg (fun z : Fin (P.length + 1) => z.1)
      (P.point_injective hpoints))
  · have hpoints₁ : P.point i.castSucc = P.point j.succ := by
      simpa [hi, hj, orientedTail, orientedHead] using hti.symm.trans hhj
    have hpoints₂ : P.point i.succ = P.point j.castSucc := by
      simpa [hi, hj, orientedTail, orientedHead] using hhi.symm.trans htj
    have h₁ := congrArg Fin.val (P.point_injective hpoints₁)
    have h₂ := congrArg Fin.val (P.point_injective hpoints₂)
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega
  · have hpoints₁ : P.point i.castSucc = P.point j.succ := by
      simpa [hi, hj, orientedTail, orientedHead] using hti.symm.trans hhj
    have hpoints₂ : P.point i.succ = P.point j.castSucc := by
      simpa [hi, hj, orientedTail, orientedHead] using hhi.symm.trans htj
    have h₁ := congrArg Fin.val (P.point_injective hpoints₁)
    have h₂ := congrArg Fin.val (P.point_injective hpoints₂)
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega
  · have hpoints : P.point i.castSucc = P.point j.castSucc := by
      simpa [hi, hj, orientedTail] using hti.symm.trans htj
    exact Fin.ext (congrArg (fun z : Fin (P.length + 1) => z.1)
      (P.point_injective hpoints))

theorem exists_vertexSimpleIndexedPath {ι ε : Type*} (src dst : ε → ι)
    {a b : ι} (h : Relation.ReflTransGen (graphAdjacent src dst) a b) :
    Nonempty (VertexSimpleIndexedPath src dst a b) := by
  classical
  obtain ⟨l, hchain, hlast, hnodup⟩ := exists_simple_chain_of_walk _ h
  let point : Fin (l.length + 1) → ι := (a :: l).get
  have hstep : ∀ i : Fin l.length, ∃ q : OrientedIndexedEdge ε,
      orientedTail src dst q = point i.castSucc ∧
        orientedHead src dst q = point i.succ := by
    intro i
    have hadj : graphAdjacent src dst (point i.castSucc) (point i.succ) := by
      exact List.isChain_iff_getElem.mp hchain i.1 (by simp)
    obtain ⟨e, hforward | hbackward⟩ := hadj
    · exact ⟨(e, false), hforward⟩
    · exact ⟨(e, true), hbackward.2, hbackward.1⟩
  let q : Fin l.length → OrientedIndexedEdge ε := fun i => Classical.choose (hstep i)
  refine ⟨{
    length := l.length
    point := point
    edge := fun i => (q i).1
    reversed := fun i => (q i).2
    first := rfl
    last := ?_
    point_injective := hnodup.injective_get
    tail := fun i => (Classical.choose_spec (hstep i)).1
    head := fun i => (Classical.choose_spec (hstep i)).2 }⟩
  simpa [point, List.getLast_eq_getElem] using hlast

end Problem56.PaperV6
