import Problem56.ContractedCoreCount
import Problem56.IndexedEulerCircuit

/-!
# Indexed Euler and half-edge infrastructure for the contracted-core encoding

The equality multigraph has one indexed edge for every cyclic occurrence.
This module deliberately keeps the edge index and the endpoint side in every
port.  Thus parallel occurrences remain distinct, and the two incidences of a
loop are represented by different half-edge ports.

This is definitions-only infrastructure toward I20.  It does not import the
admitted statement layer and it does not postulate a contracted-core decoder.
-/

namespace Problem56

/-- The source vertex of the equality-multigraph edge at cyclic occurrence
`e`. -/
def equalityEdgeSrc {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (e : Fin (2 * p)) : EqualityVertex Q.1 :=
  equalityVertexAt Q.1 e

/-- The target vertex of the equality-multigraph edge at cyclic occurrence
`e`. -/
def equalityEdgeDst {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (e : Fin (2 * p)) : EqualityVertex Q.1 :=
  equalityVertexAt Q.1 (cyclicSucc e)

/-- A half-edge is an indexed edge occurrence together with its endpoint side.
`false` is the source port and `true` is the target port. -/
abbrev EqualityHalfEdge (p : ℕ) := Fin (2 * p) × Bool

/-- The vertex incident to a particular indexed half-edge port. -/
def equalityHalfEdgeVertex {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    EqualityHalfEdge p → EqualityVertex Q.1
  | (e, false) => equalityEdgeSrc Q e
  | (e, true) => equalityEdgeDst Q e

/-- The tail half-edge used by an oriented occurrence.  With the Boolean
orientation convention from `IndexedEulerCircuit`, this is the oriented pair
itself. -/
def orientedTailHalfEdge {p : ℕ}
    (q : OrientedIndexedEdge (Fin (2 * p))) : EqualityHalfEdge p := q

/-- The head half-edge of an oriented occurrence is the opposite endpoint
side of the same indexed edge. -/
def orientedHeadHalfEdge {p : ℕ} :
    OrientedIndexedEdge (Fin (2 * p)) → EqualityHalfEdge p
  | (e, b) => (e, !b)

@[simp] theorem equalityHalfEdgeVertex_orientedTail {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (q : OrientedIndexedEdge (Fin (2 * p))) :
    equalityHalfEdgeVertex Q (orientedTailHalfEdge q) =
      orientedTail (equalityEdgeSrc Q) (equalityEdgeDst Q) q := by
  rcases q with ⟨e, b⟩
  cases b <;> rfl

@[simp] theorem equalityHalfEdgeVertex_orientedHead {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (q : OrientedIndexedEdge (Fin (2 * p))) :
    equalityHalfEdgeVertex Q (orientedHeadHalfEdge q) =
      orientedHead (equalityEdgeSrc Q) (equalityEdgeDst Q) q := by
  rcases q with ⟨e, b⟩
  cases b <;> rfl

/-- Traversing an edge always uses two distinct endpoint ports, including when
the edge is a loop. -/
theorem oriented_tail_head_halfEdges_ne {p : ℕ}
    (q : OrientedIndexedEdge (Fin (2 * p))) :
    orientedTailHalfEdge q ≠ orientedHeadHalfEdge q := by
  rcases q with ⟨e, b⟩
  cases b <;> simp [orientedTailHalfEdge, orientedHeadHalfEdge]

/-- All half-edge ports incident to `u`. -/
abbrev EqualityPortsAt {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) :=
  {h : EqualityHalfEdge p // equalityHalfEdgeVertex Q h = u}

/-- Splitting an incident half-edge by its side gives the disjoint source and
target incidence fibers.  In particular, a loop contributes once to each
summand instead of being collapsed. -/
def equalityPortsAtEquiv {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) :
    EqualityPortsAt Q u ≃
      {e : Fin (2 * p) // equalityEdgeSrc Q e = u} ⊕
        {e : Fin (2 * p) // equalityEdgeDst Q e = u} where
  toFun h := by
    rcases h with ⟨⟨e, b⟩, hb⟩
    cases b
    · exact Sum.inl ⟨e, hb⟩
    · exact Sum.inr ⟨e, hb⟩
  invFun z := by
    rcases z with e | e
    · exact ⟨(e.1, false), e.2⟩
    · exact ⟨(e.1, true), e.2⟩
  left_inv h := by
    rcases h with ⟨⟨e, b⟩, hb⟩
    cases b <;> rfl
  right_inv z := by
    rcases z with e | e <;> cases e <;> rfl

/-- The number of indexed half-edge ports at a vertex is its multigraph
degree. -/
theorem equalityPortsAt_card_eq_graphDegree {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1) :
    Fintype.card (EqualityPortsAt Q u) =
      graphDegree (equalityEdgeSrc Q) (equalityEdgeDst Q) u := by
  classical
  rw [Fintype.card_congr (equalityPortsAtEquiv Q u), Fintype.card_sum]
  rw [graphDegree]
  congr 1
  · exact Fintype.card_of_subtype _ (fun e ↦ by simp)
  · exact Fintype.card_of_subtype _ (fun e ↦ by simp)

/-- Every equality vertex has exactly twice its block cardinality many
half-edge ports. -/
theorem equalityPortsAt_card {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1) :
    Fintype.card (EqualityPortsAt Q u) = 2 * u.1.card := by
  rw [equalityPortsAt_card_eq_graphDegree]
  exact selector_quotient_degree hp Q u

/-- The disjoint union of the port fibers over the retained vertices.  The
vertex is retained together with the port, so a returning doubled link can
use two different ports at the same retained vertex. -/
abbrev EqualityRetainedPorts {p s t : ℕ} (Q : SelectorEqualityData p s t) :=
  Σ u : {u : EqualityVertex Q.1 // u ∈ equalityRetainedVertices Q},
    EqualityPortsAt Q u.1

/-- The retained port count is exactly the sum of the retained multigraph
degrees. -/
theorem equalityRetainedPorts_card {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) :
    Fintype.card (EqualityRetainedPorts Q) =
      ∑ u ∈ equalityRetainedVertices Q, 2 * u.1.card := by
  classical
  simp only [EqualityRetainedPorts, Fintype.card_sigma]
  simp_rw [equalityPortsAt_card hp Q]
  rw [Finset.univ_eq_attach]
  simpa using Finset.sum_attach (equalityRetainedVertices Q)
    (fun u : EqualityVertex Q.1 ↦ 2 * u.1.card)

/-- The source-sharp conditional budget from `ContractedCoreCount`, now stated
as a bound on an actual type of indexed, two-sided retained ports. -/
theorem equalityRetainedPorts_card_le_of_terminal_port_budget
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (hports :
      2 * (equalityTerminalVerticesOutsideCore Q).card ≤
        equalityExceptionalDegree Q.1) :
    Fintype.card (EqualityRetainedPorts Q) ≤ 36 * (s + t) := by
  rw [equalityRetainedPorts_card hp Q]
  exact equality_retained_degree_le_of_terminal_port_budget hp Q hports

/-- The two ports of a loop occurrence are distinct even though they are
incident to the same vertex. -/
theorem equality_loop_has_two_distinct_ports {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (e : Fin (2 * p))
    (hloop : equalityEdgeSrc Q e = equalityEdgeDst Q e) :
    equalityHalfEdgeVertex Q (e, false) = equalityEdgeSrc Q e ∧
      equalityHalfEdgeVertex Q (e, true) = equalityEdgeSrc Q e ∧
      (e, false) ≠ (e, true) := by
  simp [equalityHalfEdgeVertex, hloop]

/-- Ports belonging to different indexed edge occurrences remain distinct.
This applies in particular to parallel edges with the same endpoints. -/
theorem equality_ports_ne_of_edge_ne {p : ℕ}
    {e f : Fin (2 * p)} (hef : e ≠ f) (b c : Bool) :
    ((e, b) : EqualityHalfEdge p) ≠ ((f, c) : EqualityHalfEdge p) := by
  intro h
  exact hef (congrArg Prod.fst h)

/-- The indexed equality multigraph is connected and Eulerian, so it admits an
Euler circuit whose edge projection contains every cyclic occurrence exactly
once. -/
theorem equalityGraph_indexedEulerCircuit {p s t : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p s t) :
    Nonempty (IndexedEulerCircuit (equalityEdgeSrc Q) (equalityEdgeDst Q)) := by
  classical
  have hparts : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  obtain ⟨B, hB⟩ := hparts
  letI : Nonempty (EqualityVertex Q.1) := ⟨⟨B, hB⟩⟩
  apply exists_indexed_euler_circuit
  · exact selector_quotient_graph_connected hp Q
  · intro u
    change Even (graphDegree
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) u)
    rw [selector_quotient_degree hp Q u]
    exact ⟨u.1.card, by omega⟩

/-- Since `p ≥ 2`, the equality graph has an edge, and its packaged Euler
circuit can be chosen nonempty. -/
theorem equalityGraph_nonempty_indexedEulerCircuit {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    ∃ C : IndexedEulerCircuit (equalityEdgeSrc Q) (equalityEdgeDst Q),
      C.trail.steps ≠ [] := by
  classical
  let e₀ : Fin (2 * p) := ⟨0, by omega⟩
  have hpositive : 0 < graphDegree (equalityEdgeSrc Q) (equalityEdgeDst Q)
      (equalityVertexAt Q.1 e₀) := by
    change 0 < graphDegree
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e))
      (equalityVertexAt Q.1 e₀)
    rw [selector_quotient_degree hp Q]
    have hmem : e₀ ∈ (equalityVertexAt Q.1 e₀).1 := by
      exact Q.1.mem_part (Finset.mem_univ _)
    have hcard : 0 < (equalityVertexAt Q.1 e₀).1.card :=
      Finset.card_pos.mpr ⟨e₀, hmem⟩
    omega
  have heven : ∀ u, Even
      (graphDegree (equalityEdgeSrc Q) (equalityEdgeDst Q) u) := by
    intro u
    change Even (graphDegree
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) u)
    rw [selector_quotient_degree hp Q u]
    exact ⟨u.1.card, by omega⟩
  exact exists_nonempty_indexed_euler_circuit_of_positive_degree
    (equalityEdgeSrc Q) (equalityEdgeDst Q)
    (selector_quotient_graph_connected hp Q) heven
    (equalityVertexAt Q.1 e₀) hpositive

#print axioms equalityPortsAt_card
#print axioms equalityRetainedPorts_card
#print axioms equalityRetainedPorts_card_le_of_terminal_port_budget
#print axioms equality_loop_has_two_distinct_ports
#print axioms equality_ports_ne_of_edge_ne
#print axioms oriented_tail_head_halfEdges_ne
#print axioms equalityGraph_indexedEulerCircuit
#print axioms equalityGraph_nonempty_indexedEulerCircuit

end Problem56
