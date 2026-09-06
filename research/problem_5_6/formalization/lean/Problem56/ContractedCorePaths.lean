import Problem56.ContractedCoreEuler

/-!
# Local doubled-path data for the contracted-core encoding

This module turns the local I19 classification into indexed data suitable for
the global maximal-path contraction required by I20.  Edge fibers are subtypes
of `Fin (2 * p)`, so parallel occurrences are retained.  Endpoint ports remain
the two-sided `EqualityHalfEdge` objects from `ContractedCoreEuler`.

The global theorem that maximal internal doubled paths give a disjoint,
reconstructible family of retained-port links is intentionally not assumed
here.
-/

namespace Problem56

/-- Indexed equality-edge occurrences between two vertices, with either
orientation allowed. -/
abbrev EqualityEdgesBetween {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u v : EqualityVertex Q.1) :=
  {e : Fin (2 * p) //
    (equalityEdgeSrc Q e = u ∧ equalityEdgeDst Q e = v) ∨
      (equalityEdgeSrc Q e = v ∧ equalityEdgeDst Q e = u)}

/-- The indexed edge fiber has exactly the multiplicity used in the source
classification. -/
theorem equalityEdgesBetween_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityVertex Q.1) :
    Fintype.card (EqualityEdgesBetween Q u v) =
      equalityEdgeMultiplicity Q.1 u.1 v.1 := by
  classical
  rw [equalityEdgeMultiplicity]
  apply Fintype.card_of_subtype
  intro e
  simp [equalityEdgeSrc, equalityEdgeDst, equalityVertexAt, Subtype.ext_iff]

/-- The port of an edge between distinct vertices which is incident to the
first named vertex. -/
noncomputable def equalityPortAtFirst {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityVertex Q.1)
    (e : EqualityEdgesBetween Q u v) : EqualityPortsAt Q u := by
  classical
  by_cases hs : equalityEdgeSrc Q e.1 = u
  · exact ⟨(e.1, false), hs⟩
  · have ht : equalityEdgeDst Q e.1 = u := by
      rcases e.2 with h | h
      · exact (hs h.1).elim
      · exact h.2
    exact ⟨(e.1, true), ht⟩

/-- Different parallel edge occurrences give different ports at their common
endpoint. -/
theorem equalityPortAtFirst_injective {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityVertex Q.1) :
    Function.Injective (equalityPortAtFirst Q u v) := by
  intro e f hef
  have hedge (g : EqualityEdgesBetween Q u v) :
      ((equalityPortAtFirst Q u v g).1).1 = g.1 := by
    classical
    unfold equalityPortAtFirst
    split <;> rfl
  apply Subtype.ext
  rw [← hedge e, ← hedge f]
  exact congrArg (fun h : EqualityHalfEdge p ↦ h.1) (congrArg Subtype.val hef)

/-- A multiplicity-two edge fiber supplies two genuinely distinct indexed
ports at its first endpoint. -/
noncomputable def equalityIndexedPortPair {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityVertex Q.1)
    (hcard : Fintype.card (EqualityEdgesBetween Q u v) = 2) :
    Fin 2 ↪ EqualityPortsAt Q u where
  toFun i := equalityPortAtFirst Q u v
    ((Fintype.equivFinOfCardEq hcard).symm i)
  inj' := (equalityPortAtFirst_injective Q u v).comp
    (Fintype.equivFinOfCardEq hcard).symm.injective

/-- Complete local data at a removed internal vertex. -/
structure EqualityInternalDoubledNeighbors {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1) where
  left : EqualityVertex Q.1
  right : EqualityVertex Q.1
  left_ne_right : left ≠ right
  left_ne_self : left ≠ u
  right_ne_self : right ≠ u
  left_multiplicity : equalityEdgeMultiplicity Q.1 u.1 left.1 = 2
  right_multiplicity : equalityEdgeMultiplicity Q.1 u.1 right.1 = 2
  no_other_neighbor : ∀ a : EqualityVertex Q.1,
    a ≠ u → a ≠ left → a ≠ right →
      equalityEdgeMultiplicity Q.1 u.1 a.1 = 0

/-- Every unretained vertex is an internal point of a doubled path with two
distinct neighbors. -/
theorem equalityInternalDoubledNeighbors_nonempty {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∉ equalityRetainedVertices Q) :
    Nonempty (EqualityInternalDoubledNeighbors Q u) := by
  classical
  rcases equality_internal_of_not_mem_retained hp Q u hu with
    ⟨_hloop, C, hC, D, hD, hCD, hCB, hDB, hmultC, hmultD, hother⟩
  let c : EqualityVertex Q.1 := ⟨C, hC⟩
  let d : EqualityVertex Q.1 := ⟨D, hD⟩
  refine ⟨
    { left := c
      right := d
      left_ne_right := ?_
      left_ne_self := ?_
      right_ne_self := ?_
      left_multiplicity := hmultC
      right_multiplicity := hmultD
      no_other_neighbor := ?_ }⟩
  · intro h
    exact hCD (congrArg Subtype.val h)
  · intro h
    exact hCB (congrArg Subtype.val h)
  · intro h
    exact hDB (congrArg Subtype.val h)
  · intro a hau hac had
    apply hother a.1 a.2
    · intro h
      exact hau (Subtype.ext h)
    · intro h
      exact hac (Subtype.ext h)
    · intro h
      exact had (Subtype.ext h)

/-- A canonical choice of the local doubled-neighbor package.  Choice is kept
local and is not exposed by I20's public signature. -/
noncomputable def equalityInternalDoubledNeighbors {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∉ equalityRetainedVertices Q) :
    EqualityInternalDoubledNeighbors Q u :=
  Classical.choice (equalityInternalDoubledNeighbors_nonempty hp Q u hu)

/-- The two distinct indexed edge fibers on the left side of a removed
internal vertex. -/
theorem equalityInternal_left_edge_card {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∉ equalityRetainedVertices Q) :
    Fintype.card
      (EqualityEdgesBetween Q u (equalityInternalDoubledNeighbors hp Q u hu).left) = 2 := by
  rw [equalityEdgesBetween_card]
  exact (equalityInternalDoubledNeighbors hp Q u hu).left_multiplicity

/-- The two distinct indexed edge fibers on the right side of a removed
internal vertex. -/
theorem equalityInternal_right_edge_card {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∉ equalityRetainedVertices Q) :
    Fintype.card
      (EqualityEdgesBetween Q u (equalityInternalDoubledNeighbors hp Q u hu).right) = 2 := by
  rw [equalityEdgesBetween_card]
  exact (equalityInternalDoubledNeighbors hp Q u hu).right_multiplicity

/-- Adjacency along one of the doubled links which can pass through a removed
internal vertex. -/
def EqualityDoubledAdjacent {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u v : EqualityVertex Q.1) : Prop :=
  u ≠ v ∧ equalityEdgeMultiplicity Q.1 u.1 v.1 = 2

theorem equalityEdgeMultiplicity_symm_local {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B C : Finset (Fin q)) :
    equalityEdgeMultiplicity P B C = equalityEdgeMultiplicity P C B := by
  unfold equalityEdgeMultiplicity
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem EqualityDoubledAdjacent.symm {p s t : ℕ}
    {Q : SelectorEqualityData p s t} {u v : EqualityVertex Q.1}
    (h : EqualityDoubledAdjacent Q u v) : EqualityDoubledAdjacent Q v u := by
  refine ⟨h.1.symm, ?_⟩
  rw [equalityEdgeMultiplicity_symm_local]
  exact h.2

/-- A nonloop indexed graph adjacency has positive multiplicity. -/
theorem equalityEdgeMultiplicity_pos_of_graphAdjacent {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityVertex Q.1)
    (huv : u ≠ v)
    (h : graphAdjacent (equalityEdgeSrc Q) (equalityEdgeDst Q) u v) :
    0 < equalityEdgeMultiplicity Q.1 u.1 v.1 := by
  classical
  rcases h with ⟨e, h | h⟩
  · rw [equalityEdgeMultiplicity]
    apply Finset.card_pos.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩⟩
    constructor
    · exact congrArg Subtype.val h.1
    · exact congrArg Subtype.val h.2
  · rw [equalityEdgeMultiplicity]
    apply Finset.card_pos.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩⟩
    constructor
    · exact congrArg Subtype.val h.1
    · exact congrArg Subtype.val h.2

/-- Every nonloop graph step out of a removed vertex uses one of its two
multiplicity-two neighbor fibers. -/
theorem equalityDoubledAdjacent_of_internal_graphAdjacent {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∉ equalityRetainedVertices Q)
    (v : EqualityVertex Q.1) (huv : u ≠ v)
    (h : graphAdjacent (equalityEdgeSrc Q) (equalityEdgeDst Q) u v) :
    EqualityDoubledAdjacent Q u v := by
  let d := equalityInternalDoubledNeighbors hp Q u hu
  have hpos := equalityEdgeMultiplicity_pos_of_graphAdjacent Q u v huv h
  refine ⟨huv, ?_⟩
  by_cases hvleft : v = d.left
  · simpa [hvleft, d] using d.left_multiplicity
  by_cases hvright : v = d.right
  · simpa [hvright, d] using d.right_multiplicity
  have hzero := d.no_other_neighbor v huv.symm hvleft hvright
  omega

/-- Along any graph walk starting outside the retained set, either a retained
vertex has already been reached by doubled steps, or the current endpoint is
still outside and the whole prefix consists of doubled steps.  Self-loop steps
are ignored; they cannot advance the first-retained-vertex search. -/
theorem equalityGraph_path_reaches_retained_or_doubled_prefix
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (x z : EqualityVertex Q.1) (hx : x ∉ equalityRetainedVertices Q)
    (hwalk : Relation.ReflTransGen
      (graphAdjacent (equalityEdgeSrc Q) (equalityEdgeDst Q)) x z) :
    (∃ r, r ∈ equalityRetainedVertices Q ∧
      Relation.ReflTransGen (EqualityDoubledAdjacent Q) x r) ∨
      (z ∉ equalityRetainedVertices Q ∧
        Relation.ReflTransGen (EqualityDoubledAdjacent Q) x z) := by
  induction hwalk with
  | refl => exact Or.inr ⟨hx, Relation.ReflTransGen.refl⟩
  | @tail y w _ hyw ih =>
      rcases ih with hfound | ⟨hy, hdouble⟩
      · exact Or.inl hfound
      · by_cases hw : w ∈ equalityRetainedVertices Q
        · have hyw_ne : y ≠ w := by
            intro heq
            subst w
            exact hy hw
          have hstep := equalityDoubledAdjacent_of_internal_graphAdjacent
            hp Q y hy w hyw_ne hyw
          exact Or.inl ⟨w, hw, hdouble.tail hstep⟩
        · by_cases hyw_eq : y = w
          · subst w
            exact Or.inr ⟨hw, hdouble⟩
          · have hstep := equalityDoubledAdjacent_of_internal_graphAdjacent
              hp Q y hy w hyw_eq hyw
            exact Or.inr ⟨hw, hdouble.tail hstep⟩

/-- If the exceptional parameter is nonzero, every removed internal vertex is
connected to a retained vertex by a finite doubled path.  This rules out an
isolated cycle consisting entirely of removed vertices. -/
theorem equalityInternal_reaches_retained_by_doubled_path
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (u : EqualityVertex Q.1)
    (hu : u ∉ equalityRetainedVertices Q) :
    ∃ r, r ∈ equalityRetainedVertices Q ∧
      Relation.ReflTransGen (EqualityDoubledAdjacent Q) u r := by
  classical
  obtain ⟨r, hr⟩ := equality_retained_vertices_nonempty_of_parameter_ne_zero
    hp Q ha
  have hwalk : Relation.ReflTransGen
      (graphAdjacent (equalityEdgeSrc Q) (equalityEdgeDst Q)) u r :=
    selector_quotient_graph_connected hp Q u r
  rcases equalityGraph_path_reaches_retained_or_doubled_prefix
      hp Q u r hu hwalk with hfound | ⟨hrnot, _⟩
  · exact hfound
  · exact (hrnot hr).elim

/-- Complete local neighbor data at a retained loop terminal. -/
structure EqualityLoopTerminalNeighbor {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1) where
  neighbor : EqualityVertex Q.1
  neighbor_ne : neighbor ≠ u
  loop_count : equalityLoopsAt Q.1 u.1 = 1
  edge_multiplicity : equalityEdgeMultiplicity Q.1 u.1 neighbor.1 = 2
  no_other_neighbor : ∀ a : EqualityVertex Q.1,
    a ≠ u → a ≠ neighbor → equalityEdgeMultiplicity Q.1 u.1 a.1 = 0

/-- Complete local neighbor data at a retained four-edge terminal. -/
structure EqualityFourTerminalNeighbor {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1) where
  neighbor : EqualityVertex Q.1
  neighbor_ne : neighbor ≠ u
  loop_count : equalityLoopsAt Q.1 u.1 = 0
  edge_multiplicity : equalityEdgeMultiplicity Q.1 u.1 neighbor.1 = 4
  no_other_neighbor : ∀ a : EqualityVertex Q.1,
    a ≠ u → a ≠ neighbor → equalityEdgeMultiplicity Q.1 u.1 a.1 = 0

/-- A terminal outside the exceptional core carries one of the two exact
source terminal packages. -/
theorem equalityTerminalNeighbor_nonempty {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∈ equalityTerminalVerticesOutsideCore Q) :
    Nonempty
      (EqualityLoopTerminalNeighbor Q u ⊕ EqualityFourTerminalNeighbor Q u) := by
  classical
  have htype := (Finset.mem_filter.mp hu).2.2
  rcases htype with hloop | hfour
  · rcases hloop with ⟨hloops, C, hC, hCB, hmult, hother⟩
    let c : EqualityVertex Q.1 := ⟨C, hC⟩
    exact ⟨Sum.inl
      { neighbor := c
        neighbor_ne := by
          intro h
          exact hCB (congrArg Subtype.val h)
        loop_count := hloops
        edge_multiplicity := hmult
        no_other_neighbor := by
          intro a hau hac
          apply hother a.1 a.2
          · intro h
            exact hau (Subtype.ext h)
          · intro h
            exact hac (Subtype.ext h) }⟩
  · rcases hfour with ⟨hloops, C, hC, hCB, hmult, hother⟩
    let c : EqualityVertex Q.1 := ⟨C, hC⟩
    exact ⟨Sum.inr
      { neighbor := c
        neighbor_ne := by
          intro h
          exact hCB (congrArg Subtype.val h)
        loop_count := hloops
        edge_multiplicity := hmult
        no_other_neighbor := by
          intro a hau hac
          apply hother a.1 a.2
          · intro h
            exact hau (Subtype.ext h)
          · intro h
            exact hac (Subtype.ext h) }⟩

/-- A canonical choice of the exact terminal-neighbor package. -/
noncomputable def equalityTerminalNeighbor {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∈ equalityTerminalVerticesOutsideCore Q) :
    EqualityLoopTerminalNeighbor Q u ⊕ EqualityFourTerminalNeighbor Q u :=
  Classical.choice (equalityTerminalNeighbor_nonempty Q u hu)

/-- The terminal's unique nonloop neighbor is joined by exactly two or four
separately indexed edge occurrences. -/
theorem equalityTerminal_neighbor_edge_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (hu : u ∈ equalityTerminalVerticesOutsideCore Q) :
    (∃ d : EqualityLoopTerminalNeighbor Q u,
        Fintype.card (EqualityEdgesBetween Q u d.neighbor) = 2) ∨
      (∃ d : EqualityFourTerminalNeighbor Q u,
        Fintype.card (EqualityEdgesBetween Q u d.neighbor) = 4) := by
  rcases equalityTerminalNeighbor Q u hu with d | d
  · left
    refine ⟨d, ?_⟩
    rw [equalityEdgesBetween_card]
    exact d.edge_multiplicity
  · right
    refine ⟨d, ?_⟩
    rw [equalityEdgesBetween_card]
    exact d.edge_multiplicity

#print axioms equalityEdgesBetween_card
#print axioms equalityPortAtFirst_injective
#print axioms equalityIndexedPortPair
#print axioms equalityInternalDoubledNeighbors
#print axioms equalityInternal_left_edge_card
#print axioms equalityInternal_right_edge_card
#print axioms equalityDoubledAdjacent_of_internal_graphAdjacent
#print axioms equalityGraph_path_reaches_retained_or_doubled_prefix
#print axioms equalityInternal_reaches_retained_by_doubled_path
#print axioms equalityTerminalNeighbor
#print axioms equalityTerminal_neighbor_edge_card

end Problem56
