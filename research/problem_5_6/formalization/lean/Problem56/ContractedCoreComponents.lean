import Problem56.ContractedCoreTerminalBudget
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Maximal removed components for the contracted-core encoding

The vertices removed by the source contraction are exactly the internal
degree-four equality vertices.  This file represents a maximal doubled link
as a connected component of the finite support graph induced on those removed
vertices.  Component supports give a canonical disjoint cover without choosing
an orientation or collapsing indexed edge occurrences.
-/

namespace Problem56

open SimpleGraph

/-- Equality vertices removed by the contracted-core construction. -/
abbrev EqualityRemovedVertex {p s t : ℕ} (Q : SelectorEqualityData p s t) :=
  {u : EqualityVertex Q.1 // u ∉ equalityRetainedVertices Q}

/-- The support graph induced on removed internal vertices.  Its connected
components are the maximal doubled-link interiors. -/
def equalityRemovedGraph {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    SimpleGraph (EqualityRemovedVertex Q) where
  Adj u v := (equalitySupportGraph Q).Adj u.1 v.1
  symm.symm _ _ h := (equalitySupportGraph Q).symm.symm _ _ h

noncomputable instance equalityRemovedGraphLocallyFinite {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (equalityRemovedGraph Q).LocallyFinite :=
  fun _ ↦ Fintype.ofFinite _

@[simp] theorem equalityRemovedGraph_adj {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityRemovedVertex Q) :
    (equalityRemovedGraph Q).Adj u v ↔
      (equalitySupportGraph Q).Adj u.1 v.1 :=
  Iff.rfl

/-- Every support edge out of a removed vertex has multiplicity exactly two. -/
theorem equalityDoubledAdjacent_of_removed_supportAdjacent
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityRemovedVertex Q) (v : EqualityVertex Q.1)
    (h : (equalitySupportGraph Q).Adj u.1 v) :
    EqualityDoubledAdjacent Q u.1 v := by
  let d := equalityInternalDoubledNeighbors hp Q u.1 u.2
  refine ⟨h.1, ?_⟩
  by_cases hvleft : v = d.left
  · simpa only [hvleft, d] using d.left_multiplicity
  by_cases hvright : v = d.right
  · simpa only [hvright, d] using d.right_multiplicity
  have hzero := d.no_other_neighbor v h.1.symm hvleft hvright
  have hpos := h.2
  omega

/-- A removed vertex has exactly its two source-classified neighbors in the
full support graph. -/
theorem equalitySupportGraph_degree_eq_two_of_removed
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityRemovedVertex Q) :
    (equalitySupportGraph Q).degree u.1 = 2 := by
  classical
  let d := equalityInternalDoubledNeighbors hp Q u.1 u.2
  have hneighbors : (equalitySupportGraph Q).neighborFinset u.1 =
      {d.left, d.right} := by
    ext v
    constructor
    · intro hv
      have hadj := ((equalitySupportGraph Q).mem_neighborFinset u.1 v).mp hv
      by_cases hvleft : v = d.left
      · simp [hvleft]
      by_cases hvright : v = d.right
      · simp [hvright]
      have hz := d.no_other_neighbor v hadj.1.symm hvleft hvright
      have hpos := hadj.2
      omega
    · intro hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · apply ((equalitySupportGraph Q).mem_neighborFinset u.1 d.left).mpr
        exact ⟨d.left_ne_self.symm, by rw [d.left_multiplicity]; omega⟩
      · apply ((equalitySupportGraph Q).mem_neighborFinset u.1 d.right).mpr
        exact ⟨d.right_ne_self.symm, by rw [d.right_multiplicity]; omega⟩
  rw [← (equalitySupportGraph Q).card_neighborFinset_eq_degree,
    hneighbors]
  simp [d.left_ne_right]

/-- Every removed-graph edge is a genuine doubled adjacency. -/
theorem equalityRemovedGraph_adj_doubled {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    {u v : EqualityRemovedVertex Q}
    (h : (equalityRemovedGraph Q).Adj u v) :
    EqualityDoubledAdjacent Q u.1 v.1 :=
  equalityDoubledAdjacent_of_removed_supportAdjacent hp Q u v.1 h

/-- Connected-component supports cover every removed vertex. -/
theorem equalityRemovedComponent_cover {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    ⋃ c : (equalityRemovedGraph Q).ConnectedComponent, c.supp = Set.univ :=
  (equalityRemovedGraph Q).iUnion_connectedComponentSupp

/-- Distinct maximal removed components have disjoint vertex supports. -/
theorem equalityRemovedComponent_pairwise_disjoint {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    Pairwise fun c d : (equalityRemovedGraph Q).ConnectedComponent ↦
      Disjoint c.supp d.supp :=
  (equalityRemovedGraph Q).pairwise_disjoint_supp_connectedComponent

noncomputable instance equalityRemovedConnectedComponentFintype
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    Fintype (equalityRemovedGraph Q).ConnectedComponent :=
  Fintype.ofFinite _

noncomputable instance equalityRemovedComponentFintype {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) : Fintype c :=
  Fintype.ofFinite c

noncomputable instance equalityRemovedComponentGraphDecidableAdj
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    DecidableRel c.toSimpleGraph.Adj :=
  Classical.decRel _

/-! ## Component supports and link lengths -/

/-- A removed vertex is equivalently a vertex in its unique connected
component.  This is the exact disjoint decomposition used to assign the
positive lengths of contracted doubled links. -/
def equalityRemovedComponentVertexEquiv {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (Σ c : (equalityRemovedGraph Q).ConnectedComponent, c) ≃
      EqualityRemovedVertex Q where
  toFun z := z.2.1
  invFun w :=
    ⟨(equalityRemovedGraph Q).connectedComponentMk w,
      ⟨w, ConnectedComponent.connectedComponentMk_mem⟩⟩
  left_inv := by
    rintro ⟨c, ⟨w, hw⟩⟩
    have hc : (equalityRemovedGraph Q).connectedComponentMk w = c :=
      (ConnectedComponent.mem_supp_iff c w).mp hw
    subst c
    rfl
  right_inv w := rfl

/-- The sum of component lengths is exactly the number of removed internal
vertices. -/
theorem equalityRemovedComponent_sum_card
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    (∑ c : (equalityRemovedGraph Q).ConnectedComponent, Fintype.card c) =
      Fintype.card (EqualityRemovedVertex Q) := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (equalityRemovedComponentVertexEquiv Q)

/-- There are at most `p` removed vertices in total. -/
theorem equalityRemovedVertex_card_le_p
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    Fintype.card (EqualityRemovedVertex Q) ≤ p := by
  let emb : EqualityRemovedVertex Q ↪ EqualityVertex Q.1 :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hcard := Fintype.card_le_of_injective emb emb.injective
  have hvertex : Fintype.card (EqualityVertex Q.1) = Q.1.parts.card := by
    rw [Fintype.card_subtype]
    simp
  rw [hvertex, Q.2.2.1] at hcard
  omega

/-- All positive contracted-link lengths together use at most `p` original
vertices. -/
theorem equalityRemovedComponent_total_length_le_p
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    (∑ c : (equalityRemovedGraph Q).ConnectedComponent, Fintype.card c) ≤
      p := by
  rw [equalityRemovedComponent_sum_card]
  exact equalityRemovedVertex_card_le_p Q

/-- In particular, the length of each contracted component lies in the
source-prescribed range. -/
theorem equalityRemovedComponent_length_le_p
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fintype.card c ≤ p := by
  let emb : c ↪ EqualityRemovedVertex Q :=
    ⟨Subtype.val, Subtype.val_injective⟩
  exact (Fintype.card_le_of_injective emb emb.injective).trans
    (equalityRemovedVertex_card_le_p Q)

/-! ## Boundary incidences of a removed component -/

/-- Retained equality vertices, as a finite type. -/
abbrev EqualityRetainedVertex {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :=
  {u : EqualityVertex Q.1 // u ∈ equalityRetainedVertices Q}

/-- Retained support neighbors of a removed internal vertex. -/
noncomputable def equalityRetainedNeighborFinset {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityRemovedVertex Q) :
    Finset (EqualityRetainedVertex Q) := by
  classical
  exact Finset.univ.filter fun r ↦
    (equalitySupportGraph Q).Adj u.1 r.1

@[simp] theorem mem_equalityRetainedNeighborFinset {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityRemovedVertex Q)
    (r : EqualityRetainedVertex Q) :
    r ∈ equalityRetainedNeighborFinset Q u ↔
      (equalitySupportGraph Q).Adj u.1 r.1 := by
  classical
  simp [equalityRetainedNeighborFinset]

/-- The two support neighbors of a removed vertex split disjointly into
removed neighbors and retained boundary neighbors. -/
theorem equality_removed_degree_add_retainedNeighbor_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityRemovedVertex Q) :
    (equalityRemovedGraph Q).degree u +
      (equalityRetainedNeighborFinset Q u).card = 2 := by
  classical
  let remEmb : EqualityRemovedVertex Q ↪ EqualityVertex Q.1 :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let retEmb : EqualityRetainedVertex Q ↪ EqualityVertex Q.1 :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A := ((equalityRemovedGraph Q).neighborFinset u).map remEmb
  let B := (equalityRetainedNeighborFinset Q u).map retEmb
  have hpartition : (equalitySupportGraph Q).neighborFinset u.1 = A ∪ B := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, A, B,
      Finset.mem_map, remEmb, retEmb, Function.Embedding.coeFn_mk]
    constructor
    · intro hadj
      by_cases hv : v ∈ equalityRetainedVertices Q
      · right
        let r : EqualityRetainedVertex Q := ⟨v, hv⟩
        exact ⟨r, (mem_equalityRetainedNeighborFinset Q u r).mpr hadj, rfl⟩
      · left
        let w : EqualityRemovedVertex Q := ⟨v, hv⟩
        exact ⟨w, by simpa only [equalityRemovedGraph_adj] using hadj, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨r, hr, rfl⟩)
      · simpa only [equalityRemovedGraph_adj] using hw
      · exact (mem_equalityRetainedNeighborFinset Q u r).mp hr
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    rcases Finset.mem_map.mp hvA with ⟨w, hw, hvw⟩
    rcases Finset.mem_map.mp hvB with ⟨r, hr, hvr⟩
    have hwr : w.1 = r.1 := hvw.trans hvr.symm
    exact w.2 (hwr.symm ▸ r.2)
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [← hpartition] at hcard
  simp only [A, B, Finset.card_map] at hcard
  rw [(equalitySupportGraph_degree_eq_two_of_removed hp Q u).symm,
    ← (equalitySupportGraph Q).card_neighborFinset_eq_degree,
    ← (equalityRemovedGraph Q).card_neighborFinset_eq_degree]
  exact hcard.symm

/-- Along a doubled path starting at a removed vertex, either a retained
boundary edge has already been crossed or the current endpoint is still in
the same removed-graph reachability class. -/
theorem equalityDoubled_path_boundary_or_removed_prefix
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (x : EqualityRemovedVertex Q) (z : EqualityVertex Q.1)
    (hpath : Relation.ReflTransGen (EqualityDoubledAdjacent Q) x.1 z) :
    (∃ w : EqualityRemovedVertex Q,
        Relation.ReflTransGen (equalityRemovedGraph Q).Adj x w ∧
          ∃ r : EqualityRetainedVertex Q,
            (equalitySupportGraph Q).Adj w.1 r.1) ∨
      ∃ w : EqualityRemovedVertex Q, w.1 = z ∧
        Relation.ReflTransGen (equalityRemovedGraph Q).Adj x w := by
  induction hpath with
  | refl => exact Or.inr ⟨x, rfl, Relation.ReflTransGen.refl⟩
  | @tail y z _ hyz ih =>
      rcases ih with hfound | ⟨y', hy', hxy'⟩
      · exact Or.inl hfound
      · by_cases hz : z ∈ equalityRetainedVertices Q
        · left
          let r : EqualityRetainedVertex Q := ⟨z, hz⟩
          refine ⟨y', hxy', r, ?_⟩
          have hsupp : (equalitySupportGraph Q).Adj y z :=
            ⟨hyz.1, by rw [hyz.2]; omega⟩
          simpa only [hy'] using hsupp
        · right
          let z' : EqualityRemovedVertex Q := ⟨z, hz⟩
          refine ⟨z', rfl, hxy'.tail ?_⟩
          change (equalitySupportGraph Q).Adj y'.1 z
          have hsupp : (equalitySupportGraph Q).Adj y z :=
            ⟨hyz.1, by rw [hyz.2]; omega⟩
          simpa only [hy'] using hsupp

/-- A boundary incidence records a removed vertex in a fixed maximal
component together with one retained support neighbor. -/
abbrev EqualityComponentBoundaryIncidence {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :=
  Σ w : c,
    {r : EqualityRetainedVertex Q //
      r ∈ equalityRetainedNeighborFinset Q w.1}

/-- Positive exceptional parameter excludes a closed removed cycle: every
maximal removed component has at least one retained boundary incidence. -/
theorem equalityComponentBoundaryIncidence_nonempty
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Nonempty (EqualityComponentBoundaryIncidence Q c) := by
  classical
  obtain ⟨x, hxc⟩ := c.nonempty_supp
  obtain ⟨r, hr, hpath⟩ :=
    equalityInternal_reaches_retained_by_doubled_path hp Q ha x.1 x.2
  rcases equalityDoubled_path_boundary_or_removed_prefix Q x r hpath with
    ⟨w, hxw, b, hwb⟩ | ⟨w, hwr, hxw⟩
  · have hreach : (equalityRemovedGraph Q).Reachable x w := by
      rw [SimpleGraph.reachable_iff_reflTransGen]
      exact hxw
    have hwc : w ∈ c.supp := by
      have hcomp := ConnectedComponent.sound hreach
      rw [ConnectedComponent.mem_supp_iff, ← hcomp]
      exact hxc
    let wc : c := ⟨w, hwc⟩
    refine ⟨⟨wc, b, ?_⟩⟩
    exact (mem_equalityRetainedNeighborFinset Q w b).mpr hwb
  · have : r ∉ equalityRetainedVertices Q := by
      simpa only [← hwr] using w.2
    exact (this hr).elim

/-- Inside a connected-component support, every removed neighbor remains in
that support, so the component graph has the same degree as the ambient
removed graph. -/
theorem equalityComponent_degree_eq_removedDegree
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) (w : c) :
    c.toSimpleGraph.degree w = (equalityRemovedGraph Q).degree w.1 := by
  classical
  let emb : c ↪ EqualityRemovedVertex Q :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hneighbors : (c.toSimpleGraph.neighborFinset w).map emb =
      (equalityRemovedGraph Q).neighborFinset w.1 := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_map.mp hv with ⟨z, hz, rfl⟩
      have hadj := (c.toSimpleGraph.mem_neighborFinset w z).mp hz
      apply ((equalityRemovedGraph Q).mem_neighborFinset w.1 z.1).mpr
      exact hadj
    · intro hv
      have hadj := ((equalityRemovedGraph Q).mem_neighborFinset w.1 v).mp hv
      have hvc : v ∈ c.supp := c.mem_supp_of_adj_mem_supp w.2 hadj
      let z : c := ⟨v, hvc⟩
      apply Finset.mem_map.mpr
      refine ⟨z, ?_, rfl⟩
      apply (c.toSimpleGraph.mem_neighborFinset w z).mpr
      exact hadj
  calc
    c.toSimpleGraph.degree w = (c.toSimpleGraph.neighborFinset w).card := by
      rw [c.toSimpleGraph.card_neighborFinset_eq_degree]
    _ = ((c.toSimpleGraph.neighborFinset w).map emb).card :=
      (Finset.card_map _).symm
    _ = ((equalityRemovedGraph Q).neighborFinset w.1).card :=
      congrArg Finset.card hneighbors
    _ = (equalityRemovedGraph Q).degree w.1 :=
      (equalityRemovedGraph Q).card_neighborFinset_eq_degree (v := w.1)

/-- Every maximal removed component has exactly two retained support-edge
incidences.  Thus it is a path interior rather than a closed cycle; the two
incidences may lead to the same retained vertex. -/
theorem equalityComponentBoundaryIncidence_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fintype.card (EqualityComponentBoundaryIncidence Q c) = 2 := by
  classical
  let n := Fintype.card c
  let e := c.toSimpleGraph.edgeFinset.card
  let b := Fintype.card (EqualityComponentBoundaryIncidence Q c)
  have hboundary : b =
      ∑ w : c, (equalityRetainedNeighborFinset Q w.1).card := by
    simp only [b, Fintype.card_sigma,
      Fintype.card_subtype]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Finset.filter_mem_eq_inter]
    congr 1
    ext r
    simp
  have hpoint (w : c) :
      c.toSimpleGraph.degree w +
        (equalityRetainedNeighborFinset Q w.1).card = 2 := by
    rw [show c.toSimpleGraph.degree w =
        (equalityRemovedGraph Q).degree w.1 by
      exact equalityComponent_degree_eq_removedDegree Q c w]
    exact equality_removed_degree_add_retainedNeighbor_card hp Q w.1
  have hsplit :
      (∑ w : c, c.toSimpleGraph.degree w) + b = 2 * n := by
    rw [hboundary, ← Finset.sum_add_distrib]
    calc
      (∑ w : c,
          (c.toSimpleGraph.degree w +
            (equalityRetainedNeighborFinset Q w.1).card)) =
          ∑ _w : c, 2 := by
        apply Finset.sum_congr rfl
        intro w _
        exact hpoint w
      _ = 2 * n := by simp [n, Nat.mul_comm]
  have hhandshake : (∑ w : c, c.toSimpleGraph.degree w) = 2 * e := by
    simpa only [e] using c.toSimpleGraph.sum_degrees_eq_twice_card_edges
  have hvert_le : n ≤ e + 1 := by
    have h := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    simpa only [n, e, Nat.card_eq_fintype_card,
      ← c.toSimpleGraph.edgeFinset_card] using h
  have hbpos : 0 < b := by
    exact Fintype.card_pos_iff.mpr
      (equalityComponentBoundaryIncidence_nonempty hp Q ha c)
  omega

/-- The induced support on every removed component is a finite tree.  Together
with the degree split above, this rules out hidden cyclic interiors and is the
graph-theoretic path certificate behind contraction. -/
theorem equalityRemovedComponent_isTree
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    c.toSimpleGraph.IsTree := by
  classical
  let n := Fintype.card c
  let e := c.toSimpleGraph.edgeFinset.card
  have hboundary :
      (∑ w : c, (equalityRetainedNeighborFinset Q w.1).card) = 2 := by
    rw [← equalityComponentBoundaryIncidence_card hp Q ha c]
    simp only [EqualityComponentBoundaryIncidence, Fintype.card_sigma,
      Fintype.card_subtype]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Finset.filter_mem_eq_inter]
    congr 1
    ext r
    simp
  have hpoint (w : c) :
      c.toSimpleGraph.degree w +
        (equalityRetainedNeighborFinset Q w.1).card = 2 := by
    rw [equalityComponent_degree_eq_removedDegree Q c w]
    exact equality_removed_degree_add_retainedNeighbor_card hp Q w.1
  have hsum :
      (∑ w : c, c.toSimpleGraph.degree w) +
          ∑ w : c, (equalityRetainedNeighborFinset Q w.1).card =
        2 * n := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : c,
          (c.toSimpleGraph.degree w +
            (equalityRetainedNeighborFinset Q w.1).card)) =
          ∑ _w : c, 2 := by
        apply Finset.sum_congr rfl
        intro w _
        exact hpoint w
      _ = 2 * n := by simp [n, Nat.mul_comm]
  have hsplit : (∑ w : c, c.toSimpleGraph.degree w) + 2 = 2 * n :=
    (congrArg ((∑ w : c, c.toSimpleGraph.degree w) + ·)
      hboundary.symm).trans hsum
  have hhandshake : (∑ w : c, c.toSimpleGraph.degree w) = 2 * e := by
    simpa only [e] using c.toSimpleGraph.sum_degrees_eq_twice_card_edges
  have hedge : e + 1 = n := by omega
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨c.connected_toSimpleGraph, ?_⟩
  simpa only [Nat.card_eq_fintype_card, n, e,
    ← c.toSimpleGraph.edgeFinset_card] using hedge

/-- Every removed-component vertex has support degree at most two. -/
theorem equalityRemovedComponent_degree_le_two
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) (w : c) :
    c.toSimpleGraph.degree w ≤ 2 := by
  rw [equalityComponent_degree_eq_removedDegree Q c w]
  have h := equality_removed_degree_add_retainedNeighbor_card hp Q w.1
  omega

/-! ## Global indexed boundary ports -/

/-- Boundary incidences over all maximal removed components.  The component
coordinate is retained explicitly so later code can attach one contracted
link to each component without making an arbitrary choice. -/
abbrev EqualityAllComponentBoundaryIncidence {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :=
  Σ c : (equalityRemovedGraph Q).ConnectedComponent,
    EqualityComponentBoundaryIncidence Q c

/-- The indexed boundary ports belonging to one fixed removed component. -/
abbrev EqualityComponentBoundaryPorts {p s t : ℕ}
    (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :=
  Σ z : EqualityComponentBoundaryIncidence Q c,
    EqualityEdgesBetween Q z.2.1.1 z.1.1.1

/-- Each support incidence carries its full indexed edge fiber.  This is the
port-level object needed for counting parallel boundary occurrences. -/
abbrev EqualityAllComponentBoundaryPorts {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :=
  Σ z : EqualityAllComponentBoundaryIncidence Q,
    EqualityEdgesBetween Q z.2.2.1.1 z.2.1.1.1

/-- There are exactly two boundary incidences per maximal removed component. -/
theorem equalityAllComponentBoundaryIncidence_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Fintype.card (EqualityAllComponentBoundaryIncidence Q) =
      2 * Fintype.card (equalityRemovedGraph Q).ConnectedComponent := by
  classical
  simp only [EqualityAllComponentBoundaryIncidence, Fintype.card_sigma,
    equalityComponentBoundaryIncidence_card hp Q ha]
  simp [Nat.mul_comm]

/-- Every boundary support incidence is doubled, even when both incidences of
a component land at the same retained vertex. -/
theorem equalityComponentBoundary_edge_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (z : EqualityAllComponentBoundaryIncidence Q) :
    Fintype.card (EqualityEdgesBetween Q z.2.2.1.1 z.2.1.1.1) = 2 := by
  rw [equalityEdgesBetween_card, equalityEdgeMultiplicity_symm_local]
  exact (equalityDoubledAdjacent_of_removed_supportAdjacent hp Q
    z.2.1.1 z.2.2.1.1
    ((mem_equalityRetainedNeighborFinset Q z.2.1.1 z.2.2.1).mp
      z.2.2.2)).2

/-- A fixed component has exactly four indexed retained boundary ports. -/
theorem equalityComponentBoundaryPorts_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fintype.card (EqualityComponentBoundaryPorts Q c) = 4 := by
  classical
  rw [Fintype.card_sigma]
  have hedge (z : EqualityComponentBoundaryIncidence Q c) :
      Fintype.card (EqualityEdgesBetween Q z.2.1.1 z.1.1.1) = 2 :=
    equalityComponentBoundary_edge_card hp Q ⟨c, z⟩
  simp_rw [hedge]
  rw [Finset.sum_const, Finset.card_univ,
    equalityComponentBoundaryIncidence_card hp Q ha c, nsmul_eq_mul]
  norm_num

/-- Choosing finite enumerations exhibits the two boundary incidences and the
two parallel indexed occurrences at each incidence as `Fin 2 × Fin 2`.
No edge occurrence is quotiented by its endpoints. -/
noncomputable def equalityComponentBoundaryPortsEquivFinPairs
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    EqualityComponentBoundaryPorts Q c ≃ Fin 2 × Fin 2 :=
  (Equiv.sigmaEquivProdOfEquiv fun z :
      EqualityComponentBoundaryIncidence Q c ↦
    Fintype.equivFinOfCardEq
      (equalityComponentBoundary_edge_card hp Q ⟨c, z⟩)).trans
    (Equiv.prodCongr
      (Fintype.equivFinOfCardEq
        (equalityComponentBoundaryIncidence_card hp Q ha c))
      (Equiv.refl (Fin 2)))

/-- Counting indexed boundary occurrences gives four ports per removed
component: two support incidences, each of multiplicity two. -/
theorem equalityAllComponentBoundaryPorts_card
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Fintype.card (EqualityAllComponentBoundaryPorts Q) =
      4 * Fintype.card (equalityRemovedGraph Q).ConnectedComponent := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [equalityComponentBoundary_edge_card hp Q]
  rw [Finset.sum_const, Finset.card_univ,
    equalityAllComponentBoundaryIncidence_card hp Q ha, nsmul_eq_mul]
  all_goals simp [Nat.cast_id]
  omega

/-- Forget the removed endpoint and component while retaining the actual
indexed half-edge at the retained endpoint.  Disjoint retained/removed vertex
classes make this map injective, including for parallel occurrences. -/
noncomputable def equalityAllComponentBoundaryPortsEmbedding
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    EqualityAllComponentBoundaryPorts Q ↪ EqualityRetainedPorts Q where
  toFun x :=
    ⟨x.1.2.2.1, equalityPortAtFirst Q x.1.2.2.1.1 x.1.2.1.1.1 x.2⟩
  inj' := by
    intro x y hxy
    rcases x with ⟨⟨c, ⟨w, r⟩⟩, e⟩
    rcases y with ⟨⟨d, ⟨z, q⟩⟩, f⟩
    have hrq : r.1 = q.1 := congrArg Sigma.fst hxy
    have hedge_of (a b : EqualityVertex Q.1)
        (g : EqualityEdgesBetween Q a b) :
        ((equalityPortAtFirst Q a b g).1).1 = g.1 := by
      unfold equalityPortAtFirst
      split <;> rfl
    have hef : e.1 = f.1 := by
      rw [← hedge_of r.1.1 w.1.1 e, ← hedge_of q.1.1 z.1.1 f]
      exact congrArg (fun h : EqualityRetainedPorts Q ↦ h.2.1.1) hxy
    have hf' :
        (equalityEdgeSrc Q e.1 = q.1.1 ∧
            equalityEdgeDst Q e.1 = z.1.1) ∨
          (equalityEdgeSrc Q e.1 = z.1.1 ∧
            equalityEdgeDst Q e.1 = q.1.1) := by
      simpa only [← hef] using f.2
    have hwz0 : w.1.1 = z.1.1 := by
      rcases e.2 with he | he <;> rcases hf' with hf | hf
      · exact he.2.symm.trans hf.2
      · exact (z.1.2 ((hf.1.symm.trans he.1) ▸ r.1.2)).elim
      · exact (w.1.2 ((he.1.symm.trans hf.1) ▸ q.1.2)).elim
      · exact he.1.symm.trans hf.1
    have hwz : w.1 = z.1 := Subtype.ext hwz0
    have hcd : c = d :=
      ConnectedComponent.eq_of_common_vertex w.2 (hwz.symm ▸ z.2)
    subst d
    have hwz' : w = z := Subtype.ext hwz
    subst z
    have hrq' : r = q := Subtype.ext hrq
    subst q
    have hef' : e = f := Subtype.ext hef
    subst f
    rfl

/-- Reassociate global boundary ports and enumerate the two incidences and two
parallel occurrences of each component. -/
noncomputable def
    equalityAllComponentBoundaryPortsEquivComponentFinPairs
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityAllComponentBoundaryPorts Q ≃
      Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2 :=
  (Equiv.sigmaAssoc fun
      (c : (equalityRemovedGraph Q).ConnectedComponent)
      (z : EqualityComponentBoundaryIncidence Q c) ↦
        EqualityEdgesBetween Q z.2.1.1 z.1.1.1).trans
    (Equiv.sigmaCongrRight fun c ↦
      equalityComponentBoundaryPortsEquivFinPairs hp Q ha c)

/-- The source's four distinguished ports per positive-length contracted link
form one globally disjoint component-indexed family inside the retained port
set. -/
noncomputable def equalityRemovedComponentFinPortsEmbedding
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2) ↪
      EqualityRetainedPorts Q :=
  (equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha).symm.toEmbedding.trans
    (equalityAllComponentBoundaryPortsEmbedding Q)

/-- The retained-port budget therefore controls the number of maximal
removed doubled-link interiors. -/
theorem equalityRemovedComponent_card_le_nine_parameter
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Fintype.card (equalityRemovedGraph Q).ConnectedComponent ≤
      9 * (s + t) := by
  have hinj := Fintype.card_le_of_injective
    (equalityAllComponentBoundaryPortsEmbedding Q)
    (equalityAllComponentBoundaryPortsEmbedding Q).injective
  rw [equalityAllComponentBoundaryPorts_card hp Q ha] at hinj
  have hports := equalityRetainedPorts_card_le_of_parameter_pos hp Q ha
  omega

/-- Enumerate positive-length contracted links inside the `9(s+t)` padded
link-length slots of `ContractedCoreCode`. -/
noncomputable def equalityRemovedComponentEmbeddingFinNineParameter
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (equalityRemovedGraph Q).ConnectedComponent ↪ Fin (9 * (s + t)) :=
  (Fintype.equivFin
      (equalityRemovedGraph Q).ConnectedComponent).toEmbedding.trans
    (Fin.castLEEmb
      (equalityRemovedComponent_card_le_nine_parameter hp Q ha))

/-- A component length is a valid value in the source's `Fin (4p+1)` coding
alphabet. -/
noncomputable def equalityRemovedComponentLengthCode
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) : Fin (4 * p + 1) :=
  ⟨Fintype.card c, by
    have h := equalityRemovedComponent_length_le_p Q c
    omega⟩

@[simp] theorem equalityRemovedComponentLengthCode_val
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    (equalityRemovedComponentLengthCode Q c).1 = Fintype.card c :=
  rfl

#print axioms equalityDoubledAdjacent_of_removed_supportAdjacent
#print axioms equalitySupportGraph_degree_eq_two_of_removed
#print axioms equalityRemovedGraph_adj_doubled
#print axioms equalityRemovedComponent_cover
#print axioms equalityRemovedComponent_pairwise_disjoint
#print axioms equalityRemovedComponentVertexEquiv
#print axioms equalityRemovedComponent_sum_card
#print axioms equalityRemovedVertex_card_le_p
#print axioms equalityRemovedComponent_total_length_le_p
#print axioms equalityRemovedComponent_length_le_p
#print axioms equality_removed_degree_add_retainedNeighbor_card
#print axioms equalityDoubled_path_boundary_or_removed_prefix
#print axioms equalityComponentBoundaryIncidence_nonempty
#print axioms equalityComponent_degree_eq_removedDegree
#print axioms equalityComponentBoundaryIncidence_card
#print axioms equalityRemovedComponent_isTree
#print axioms equalityRemovedComponent_degree_le_two
#print axioms equalityAllComponentBoundaryIncidence_card
#print axioms equalityComponentBoundary_edge_card
#print axioms equalityComponentBoundaryPorts_card
#print axioms equalityComponentBoundaryPortsEquivFinPairs
#print axioms equalityAllComponentBoundaryPorts_card
#print axioms equalityAllComponentBoundaryPortsEmbedding
#print axioms equalityAllComponentBoundaryPortsEquivComponentFinPairs
#print axioms equalityRemovedComponentFinPortsEmbedding
#print axioms equalityRemovedComponent_card_le_nine_parameter
#print axioms equalityRemovedComponentEmbeddingFinNineParameter
#print axioms equalityRemovedComponentLengthCode

end Problem56
