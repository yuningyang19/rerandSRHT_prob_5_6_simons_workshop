import Problem56.ContractedCorePaths
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Terminal-to-core port budget

This file develops the finite tree-counting lemma needed for the source-sharp
terminal budget in I20.  It works with a genuine boundary-degree count rather
than a leaf bound with an extraneous additive two.
-/

namespace Problem56

open SimpleGraph

/-- Number of tree edges leaving `E`, counted at their endpoint in `E`. -/
def treeBoundaryDegree {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E : Finset V) : ℕ :=
  ∑ u ∈ E, (T.neighborFinset u \ E).card

/-- In a finite tree with a nonempty retained set `E`, if every vertex outside
`E` has degree at most two, then the number of outside leaves is at most the
number of tree edges crossing from `E` to its complement. -/
theorem tree_outside_leaves_le_boundaryDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (E : Finset V) (hT : T.IsTree)
    (hE : E.Nonempty) (hdegree : ∀ v ∉ E, T.degree v ≤ 2) :
    ((Finset.univ : Finset V).filter fun v ↦ v ∉ E ∧ T.degree v = 1).card ≤
      treeBoundaryDegree T E := by
  classical
  let O := (Finset.univ : Finset V) \ E
  let L := O.filter fun v ↦ T.degree v = 1
  have hEsub : E ⊆ (Finset.univ : Finset V) := Finset.subset_univ E
  have hcard_split : O.card + E.card = Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    simpa only [O, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card hEsub
  have hpositive (v : V) (hvO : v ∈ O) : 0 < T.degree v := by
    obtain ⟨e, heE⟩ := hE
    have hve : v ≠ e := by
      intro h
      subst e
      exact (Finset.mem_sdiff.mp hvO).2 heE
    letI : Nontrivial V := ⟨⟨v, e, hve⟩⟩
    exact (T.degree_pos (v := v)).mpr (hT.preconnected.not_isIsolated v)
  have hout_degree (v : V) (hvO : v ∈ O) :
      T.degree v = 1 ∨ T.degree v = 2 := by
    have hvnot : v ∉ E := (Finset.mem_sdiff.mp hvO).2
    have hle := hdegree v hvnot
    have hpos := hpositive v hvO
    omega
  have hout_sum : (∑ v ∈ O, T.degree v) + L.card = 2 * O.card := by
    calc
      (∑ v ∈ O, T.degree v) + L.card =
          ∑ v ∈ O, (T.degree v + if T.degree v = 1 then 1 else 0) := by
            rw [show L.card = ∑ v ∈ O,
                if T.degree v = 1 then 1 else 0 by
              simp only [L, Finset.card_eq_sum_ones, Finset.sum_filter]]
            rw [Finset.sum_add_distrib]
      _ = ∑ _v ∈ O, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rcases hout_degree v hv with hone | htwo
        · simp [hone]
        · simp [htwo]
      _ = 2 * O.card := by simp [Nat.mul_comm]
  let H : SimpleGraph {v : V // v ∈ E} := T.induce (↑E : Set V)
  have hHacyclic : H.IsAcyclic := hT.isAcyclic.induce _
  letI : Nonempty {v : V // v ∈ E} :=
    ⟨⟨hE.choose, hE.choose_spec⟩⟩
  obtain ⟨S, hHS, _hStop, hStree⟩ :=
    (SimpleGraph.connected_top :
      (⊤ : SimpleGraph {v : V // v ∈ E}).Connected).exists_isTree_le_of_le_of_isAcyclic
      (H := H) le_top hHacyclic
  have hHedge_le : H.edgeFinset.card ≤ S.edgeFinset.card :=
    Finset.card_le_card (edgeFinset_mono hHS)
  have hScard := (S.isTree_iff_connected_and_card.mp hStree).2
  have hSedge : S.edgeFinset.card + 1 = E.card := by
    simpa only [Nat.card_eq_fintype_card, ← S.edgeFinset_card,
      Fintype.card_coe] using hScard
  have hHedge : H.edgeFinset.card + 1 ≤ E.card := by omega
  have hinside :
      (∑ u ∈ E, (T.neighborFinset u ∩ E).card) =
        2 * H.edgeFinset.card := by
    calc
      (∑ u ∈ E, (T.neighborFinset u ∩ E).card) =
          ∑ u : {u : V // u ∈ E}, H.degree u := by
            rw [← Finset.sum_attach]
            apply Finset.sum_congr rfl
            intro u _
            rw [← H.card_neighborFinset_eq_degree]
            let emb : {v : V // v ∈ E} ↪ V :=
              Function.Embedding.subtype (fun v ↦ v ∈ E)
            rw [← Finset.card_map emb]
            apply congrArg Finset.card
            ext v
            simp [emb, H]
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hEdegree :
      (∑ u ∈ E, T.degree u) =
        (∑ u ∈ E, (T.neighborFinset u ∩ E).card) +
          treeBoundaryDegree T E := by
    rw [treeBoundaryDegree, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← T.card_neighborFinset_eq_degree]
    exact (Finset.card_inter_add_card_sdiff (T.neighborFinset u) E).symm
  have hsum_split := Finset.sum_sdiff hEsub (f := fun v ↦ T.degree v)
  change (∑ v ∈ O, T.degree v) + ∑ v ∈ E, T.degree v =
    ∑ v : V, T.degree v at hsum_split
  have hhandshake := T.sum_degrees_eq_twice_card_edges
  have hTcard := (T.isTree_iff_connected_and_card.mp hT).2
  rw [T.edgeFinset_card, ← Nat.card_eq_fintype_card] at hhandshake
  have hLdef :
      ((Finset.univ : Finset V).filter fun v ↦ v ∉ E ∧ T.degree v = 1) = L := by
    ext v
    simp [L, O]
  rw [hLdef]
  rw [hinside] at hEdegree
  rw [hhandshake] at hsum_split
  omega

/-! ## The finite support graph of the equality multigraph -/

/-- The loop-free support graph obtained by forgetting only edge
multiplicities.  Indexed parallel occurrences are still available separately
through `EqualityEdgesBetween`. -/
def equalitySupportGraph {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    SimpleGraph (EqualityVertex Q.1) where
  Adj u v := u ≠ v ∧ 0 < equalityEdgeMultiplicity Q.1 u.1 v.1
  symm.symm u v h :=
    ⟨h.1.symm, by
      rw [equalityEdgeMultiplicity_symm_local]
      exact h.2⟩

noncomputable instance equalitySupportGraphLocallyFinite {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (equalitySupportGraph Q).LocallyFinite :=
  fun _ ↦ Fintype.ofFinite _

@[simp] theorem equalitySupportGraph_adj {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u v : EqualityVertex Q.1) :
    (equalitySupportGraph Q).Adj u v ↔
      u ≠ v ∧ 0 < equalityEdgeMultiplicity Q.1 u.1 v.1 :=
  Iff.rfl

/-- The support graph is connected because every indexed equality-graph step
either stays at its current vertex (a loop) or gives a support edge. -/
theorem equalitySupportGraph_preconnected {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (equalitySupportGraph Q).Preconnected := by
  intro u v
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hconn := selector_quotient_graph_connected hp Q u v
  exact Relation.ReflTransGen.lift' id (fun a b h ↦ by
    by_cases hab : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ⟨hab, equalityEdgeMultiplicity_pos_of_graphAdjacent Q a b hab h⟩)
    u v hconn

/-- Outside the exceptional core, the support degree is at most two.  This is
the simple-graph shadow of the exact internal/terminal classification. -/
theorem equalitySupportGraph_degree_le_two_of_nonexceptional
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1)
    (hu : u.1 ∉ equalityExceptionalVertices Q.1) :
    (equalitySupportGraph Q).degree u ≤ 2 := by
  classical
  rw [← (equalitySupportGraph Q).card_neighborFinset_eq_degree]
  rcases equality_degree_four_local_classification hp Q u.1 u.2 hu with
    hint | hloop | hfour
  · rcases hint with
      ⟨_, C, hC, D, hD, hCD, hCu, hDu, hCm, hDm, hother⟩
    let c : EqualityVertex Q.1 := ⟨C, hC⟩
    let d : EqualityVertex Q.1 := ⟨D, hD⟩
    calc
      ((equalitySupportGraph Q).neighborFinset u).card ≤
          ({c, d} : Finset (EqualityVertex Q.1)).card := by
        apply Finset.card_le_card
        intro v hv
        have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
        by_cases hvc : v = c
        · simp [hvc]
        by_cases hvd : v = d
        · simp [hvd]
        have hvu : v.1 ≠ u.1 := by
          intro h
          exact hadj.1 (Subtype.ext h.symm)
        have hvC : v.1 ≠ C := by
          intro h
          exact hvc (Subtype.ext h)
        have hvD : v.1 ≠ D := by
          intro h
          exact hvd (Subtype.ext h)
        have hz := hother v.1 v.2 hvu hvC hvD
        have hpos := hadj.2
        change 0 < equalityEdgeMultiplicity Q.1 u.1 v.1 at hpos
        omega
      _ ≤ 2 := by simp [c, d, hCD]
  · rcases hloop with ⟨_, C, hC, hCu, hCm, hother⟩
    let c : EqualityVertex Q.1 := ⟨C, hC⟩
    calc
      ((equalitySupportGraph Q).neighborFinset u).card ≤
          ({c} : Finset (EqualityVertex Q.1)).card := by
        apply Finset.card_le_card
        intro v hv
        have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
        by_cases hvc : v = c
        · simp [hvc]
        have hvu : v.1 ≠ u.1 := by
          intro h
          exact hadj.1 (Subtype.ext h.symm)
        have hvC : v.1 ≠ C := by
          intro h
          exact hvc (Subtype.ext h)
        have hz := hother v.1 v.2 hvu hvC
        have hpos := hadj.2
        change 0 < equalityEdgeMultiplicity Q.1 u.1 v.1 at hpos
        omega
      _ ≤ 2 := by simp
  · rcases hfour with ⟨_, C, hC, hCu, hCm, hother⟩
    let c : EqualityVertex Q.1 := ⟨C, hC⟩
    calc
      ((equalitySupportGraph Q).neighborFinset u).card ≤
          ({c} : Finset (EqualityVertex Q.1)).card := by
        apply Finset.card_le_card
        intro v hv
        have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
        by_cases hvc : v = c
        · simp [hvc]
        have hvu : v.1 ≠ u.1 := by
          intro h
          exact hadj.1 (Subtype.ext h.symm)
        have hvC : v.1 ≠ C := by
          intro h
          exact hvc (Subtype.ext h)
        have hz := hother v.1 v.2 hvu hvC
        have hpos := hadj.2
        change 0 < equalityEdgeMultiplicity Q.1 u.1 v.1 at hpos
        omega
      _ ≤ 2 := by simp

/-- Every retained terminal outside the exceptional core is a leaf of the
support graph. -/
theorem equalitySupportGraph_degree_eq_one_of_terminal
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1)
    (hu : u ∈ equalityTerminalVerticesOutsideCore Q) :
    (equalitySupportGraph Q).degree u = 1 := by
  classical
  rw [← (equalitySupportGraph Q).card_neighborFinset_eq_degree]
  rcases equalityTerminalNeighbor Q u hu with d | d
  · have hneighbors :
        (equalitySupportGraph Q).neighborFinset u = {d.neighbor} := by
      ext v
      constructor
      · intro hv
        have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
        by_cases hvd : v = d.neighbor
        · simp [hvd]
        have hvu : v ≠ u := hadj.1.symm
        have hz := d.no_other_neighbor v hvu hvd
        have hpos := hadj.2
        omega
      · intro hv
        have hvd : v = d.neighbor := Finset.mem_singleton.mp hv
        subst v
        apply ((equalitySupportGraph Q).mem_neighborFinset u d.neighbor).mpr
        exact ⟨d.neighbor_ne.symm, by rw [d.edge_multiplicity]; omega⟩
    rw [hneighbors]
    simp
  · have hneighbors :
        (equalitySupportGraph Q).neighborFinset u = {d.neighbor} := by
      ext v
      constructor
      · intro hv
        have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
        by_cases hvd : v = d.neighbor
        · simp [hvd]
        have hvu : v ≠ u := hadj.1.symm
        have hz := d.no_other_neighbor v hvu hvd
        have hpos := hadj.2
        omega
      · intro hv
        have hvd : v = d.neighbor := Finset.mem_singleton.mp hv
        subst v
        apply ((equalitySupportGraph Q).mem_neighborFinset u d.neighbor).mpr
        exact ⟨d.neighbor_ne.symm, by rw [d.edge_multiplicity]; omega⟩
    rw [hneighbors]
    simp

/-- Seen from a nonexceptional endpoint, every support edge has multiplicity
at least two. -/
theorem equalityEdgeMultiplicity_ge_two_of_nonexceptional_adj
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u v : EqualityVertex Q.1)
    (hv : v.1 ∉ equalityExceptionalVertices Q.1)
    (huv : (equalitySupportGraph Q).Adj u v) :
    2 ≤ equalityEdgeMultiplicity Q.1 u.1 v.1 := by
  have hposvu : 0 < equalityEdgeMultiplicity Q.1 v.1 u.1 := by
    rw [equalityEdgeMultiplicity_symm_local]
    exact huv.2
  rcases equality_degree_four_local_classification hp Q v.1 v.2 hv with
    hint | hloop | hfour
  · rcases hint with
      ⟨_, C, hC, D, hD, hCD, hCv, hDv, hCm, hDm, hother⟩
    by_cases huC : u.1 = C
    · rw [equalityEdgeMultiplicity_symm_local, huC, hCm]
    by_cases huD : u.1 = D
    · rw [equalityEdgeMultiplicity_symm_local, huD, hDm]
    have huv' : u.1 ≠ v.1 := by
      intro h
      exact huv.1 (Subtype.ext h)
    have hz := hother u.1 u.2 huv' huC huD
    omega
  · rcases hloop with ⟨_, C, hC, hCv, hCm, hother⟩
    by_cases huC : u.1 = C
    · rw [equalityEdgeMultiplicity_symm_local, huC, hCm]
    have huv' : u.1 ≠ v.1 := by
      intro h
      exact huv.1 (Subtype.ext h)
    have hz := hother u.1 u.2 huv' huC
    omega
  · rcases hfour with ⟨_, C, hC, hCv, hCm, hother⟩
    by_cases huC : u.1 = C
    · rw [equalityEdgeMultiplicity_symm_local, huC, hCm]
      omega
    have huv' : u.1 ≠ v.1 := by
      intro h
      exact huv.1 (Subtype.ext h)
    have hz := hother u.1 u.2 huv' huC
    omega

/-- For any spanning tree of the support graph, terminals outside the
exceptional core inject into the tree leaves lying outside that core. -/
theorem equalityTerminal_card_le_treeBoundaryDegree
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (T : SimpleGraph (EqualityVertex Q.1))
    [DecidableRel T.Adj]
    (hTG : T ≤ equalitySupportGraph Q) (hT : T.IsTree) :
    (equalityTerminalVerticesOutsideCore Q).card ≤
      treeBoundaryDegree T (equalityExceptionalCoreVertices Q) := by
  classical
  let E := equalityExceptionalCoreVertices Q
  have hE : E.Nonempty := by
    simpa only [E] using
      equality_exceptional_core_nonempty_of_parameter_ne_zero hp Q ha
  have hdegree (v : EqualityVertex Q.1) (hv : v ∉ E) :
      T.degree v ≤ 2 := by
    have hvnonexceptional :
        v.1 ∉ equalityExceptionalVertices Q.1 := by
      simpa only [E, equalityExceptionalCoreVertices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    exact (T.degree_le_of_le hTG).trans
      (equalitySupportGraph_degree_le_two_of_nonexceptional hp Q v
        hvnonexceptional)
  have hleaf := tree_outside_leaves_le_boundaryDegree T E hT hE hdegree
  calc
    (equalityTerminalVerticesOutsideCore Q).card ≤
        ((Finset.univ : Finset (EqualityVertex Q.1)).filter fun v ↦
          v ∉ E ∧ T.degree v = 1).card := by
      apply Finset.card_le_card
      intro v hvterminal
      have hvnonexceptional :
          v.1 ∉ equalityExceptionalVertices Q.1 :=
        (Finset.mem_filter.mp hvterminal).2.1
      have hvE : v ∉ E := by
        simpa only [E, equalityExceptionalCoreVertices, Finset.mem_filter,
          Finset.mem_univ, true_and]
      have hGdegree :=
        equalitySupportGraph_degree_eq_one_of_terminal Q v hvterminal
      have hTle : T.degree v ≤ 1 := by
        exact (T.degree_le_of_le hTG).trans_eq hGdegree
      obtain ⟨e, heE⟩ := hE
      have hve : v ≠ e := by
        intro h
        subst e
        exact hvE heE
      letI : Nontrivial (EqualityVertex Q.1) := ⟨⟨v, e, hve⟩⟩
      have hTpos : 0 < T.degree v :=
        (T.degree_pos (v := v)).mpr (hT.preconnected.not_isIsolated v)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ v, hvE, by omega⟩
    _ ≤ treeBoundaryDegree T E := hleaf

/-! ## Distinct neighbor fibers consume distinct half-edge ports -/

/-- All indexed edge occurrences joining `u` to a vertex in `N`. -/
abbrev EqualityNeighborIndexedEdges {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (u : EqualityVertex Q.1)
    (N : Finset (EqualityVertex Q.1)) :=
  Σ v : {v : EqualityVertex Q.1 // v ∈ N}, EqualityEdgesBetween Q u v.1

/-- Edge fibers belonging to distinct nonself neighbors occupy distinct ports
at `u`. -/
noncomputable def equalityNeighborIndexedEdgesEmbedding
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (N : Finset (EqualityVertex Q.1))
    (hN : ∀ v ∈ N, v ≠ u) :
    EqualityNeighborIndexedEdges Q u N ↪ EqualityPortsAt Q u where
  toFun x := equalityPortAtFirst Q u x.1.1 x.2
  inj' := by
    intro x y hxy
    rcases x with ⟨v, e⟩
    rcases y with ⟨w, f⟩
    have hedge_of (z : EqualityVertex Q.1)
        (g : EqualityEdgesBetween Q u z) :
        ((equalityPortAtFirst Q u z g).1).1 = g.1 := by
      classical
      unfold equalityPortAtFirst
      split <;> rfl
    have hef : e.1 = f.1 := by
      rw [← hedge_of v.1 e, ← hedge_of w.1 f]
      exact congrArg (fun z : EqualityPortsAt Q u ↦ z.1.1) hxy
    have hf' :
        (equalityEdgeSrc Q e.1 = u ∧ equalityEdgeDst Q e.1 = w.1) ∨
          (equalityEdgeSrc Q e.1 = w.1 ∧ equalityEdgeDst Q e.1 = u) := by
      simpa only [← hef] using f.2
    have hvw : v.1 = w.1 := by
      rcases e.2 with he | he <;> rcases hf' with hf | hf
      · exact he.2.symm.trans hf.2
      · exact ((hN w.1 w.2) (he.1.symm.trans hf.1).symm).elim
      · exact ((hN v.1 v.2) (he.1.symm.trans hf.1)).elim
      · exact he.1.symm.trans hf.1
    have hvw' : v = w := Subtype.ext hvw
    subst w
    have heq : e = f :=
      equalityPortAtFirst_injective Q u v.1 hxy
    subst f
    rfl

/-- The sum of all indexed multiplicities toward a nonself neighbor set is at
most the total number of half-edge ports at the base vertex. -/
theorem equality_neighbor_multiplicity_sum_le_ports
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (N : Finset (EqualityVertex Q.1))
    (hN : ∀ v ∈ N, v ≠ u) :
    (∑ v ∈ N, equalityEdgeMultiplicity Q.1 u.1 v.1) ≤
      Fintype.card (EqualityPortsAt Q u) := by
  classical
  let emb := equalityNeighborIndexedEdgesEmbedding Q u N hN
  have hcard := Fintype.card_le_of_injective emb emb.injective
  simp only [EqualityNeighborIndexedEdges, Fintype.card_sigma] at hcard
  simp_rw [equalityEdgesBetween_card] at hcard
  have hsum :
      (∑ v : {v : EqualityVertex Q.1 // v ∈ N},
        equalityEdgeMultiplicity Q.1 u.1 v.1.1) =
        ∑ v ∈ N, equalityEdgeMultiplicity Q.1 u.1 v.1 := by
    rw [Finset.univ_eq_attach]
    simpa using Finset.sum_attach N
      (fun v : EqualityVertex Q.1 ↦
        equalityEdgeMultiplicity Q.1 u.1 v.1)
  rwa [hsum] at hcard

/-- Summing block degrees over the subtype-valued exceptional core recovers
the source definition of `equalityExceptionalDegree`. -/
theorem equalityExceptionalCore_degree_sum {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (∑ u ∈ equalityExceptionalCoreVertices Q, 2 * u.1.card) =
      equalityExceptionalDegree Q.1 := by
  classical
  unfold equalityExceptionalDegree
  apply Finset.sum_bij (fun u _ ↦ u.1)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u₁ hu₁ u₂ hu₂ h
    exact Subtype.ext h
  · intro B hB
    have hBpart : B ∈ Q.1.parts := by
      rcases Finset.mem_union.mp hB with hodd | hlarge
      · exact (Finset.mem_filter.mp hodd).1
      · exact (Finset.mem_filter.mp hlarge).1
    let u : EqualityVertex Q.1 := ⟨B, hBpart⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hB⟩, rfl⟩
  · intro u hu
    rfl

/-- Each tree boundary neighbor of an exceptional vertex consumes at least
two distinct indexed ports, and different neighbors consume disjoint edge
fibers. -/
theorem twice_treeBoundaryDegree_le_exceptionalDegree
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (T : SimpleGraph (EqualityVertex Q.1)) [DecidableRel T.Adj]
    (hTG : T ≤ equalitySupportGraph Q) :
    2 * treeBoundaryDegree T (equalityExceptionalCoreVertices Q) ≤
      equalityExceptionalDegree Q.1 := by
  classical
  let E := equalityExceptionalCoreVertices Q
  have hpoint (u : EqualityVertex Q.1) (huE : u ∈ E) :
      2 * (T.neighborFinset u \ E).card ≤ 2 * u.1.card := by
    let N := T.neighborFinset u \ E
    have hNself (v : EqualityVertex Q.1) (hvN : v ∈ N) : v ≠ u := by
      have hvneighbor : v ∈ T.neighborFinset u :=
        (Finset.mem_sdiff.mp hvN).1
      exact (((T.mem_neighborFinset u v).mp hvneighbor).ne).symm
    have hports := equality_neighbor_multiplicity_sum_le_ports Q u N hNself
    rw [equalityPortsAt_card hp Q u] at hports
    calc
      2 * N.card = ∑ _v ∈ N, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ N, equalityEdgeMultiplicity Q.1 u.1 v.1 := by
        apply Finset.sum_le_sum
        intro v hvN
        have hvneighbor : v ∈ T.neighborFinset u :=
          (Finset.mem_sdiff.mp hvN).1
        have hvnotE : v ∉ E := (Finset.mem_sdiff.mp hvN).2
        have hvnonexceptional :
            v.1 ∉ equalityExceptionalVertices Q.1 := by
          simpa only [E, equalityExceptionalCoreVertices,
            Finset.mem_filter, Finset.mem_univ, true_and] using hvnotE
        have hTadj := (T.mem_neighborFinset u v).mp hvneighbor
        exact equalityEdgeMultiplicity_ge_two_of_nonexceptional_adj
          hp Q u v hvnonexceptional (hTG hTadj)
      _ ≤ 2 * u.1.card := hports
  change 2 * treeBoundaryDegree T E ≤ equalityExceptionalDegree Q.1
  rw [treeBoundaryDegree, Finset.mul_sum]
  calc
    (∑ u ∈ E, 2 * (T.neighborFinset u \ E).card) ≤
        ∑ u ∈ E, 2 * u.1.card := by
      apply Finset.sum_le_sum
      intro u huE
      exact hpoint u huE
    _ = equalityExceptionalDegree Q.1 := by
      simpa only [E] using equalityExceptionalCore_degree_sum Q

/-- When the exceptional parameter is positive, the source-sharp terminal
port budget follows from a spanning tree of the support graph. -/
theorem equality_terminal_port_budget_of_parameter_pos
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    2 * (equalityTerminalVerticesOutsideCore Q).card ≤
      equalityExceptionalDegree Q.1 := by
  classical
  have hparts : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  obtain ⟨B, hB⟩ := hparts
  letI : Nonempty (EqualityVertex Q.1) := ⟨⟨B, hB⟩⟩
  have hconnected : (equalitySupportGraph Q).Connected :=
    ⟨equalitySupportGraph_preconnected hp Q⟩
  obtain ⟨T, hTG, hT⟩ := hconnected.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  have hterminal :=
    equalityTerminal_card_le_treeBoundaryDegree hp Q ha T hTG hT
  have hboundary :=
    twice_treeBoundaryDegree_le_exceptionalDegree hp Q T hTG
  omega

/-- Positive exceptional parameter closes the conditional retained-vertex
budget from `ContractedCoreCount`. -/
theorem equality_retained_card_le_of_parameter_pos
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    (equalityRetainedVertices Q).card ≤ 8 * (s + t) :=
  equality_retained_card_le_of_terminal_port_budget hp Q
    (equality_terminal_port_budget_of_parameter_pos hp Q ha)

/-- Positive exceptional parameter also closes the retained indexed-port
budget used by the eventual contracted-link code. -/
theorem equalityRetainedPorts_card_le_of_parameter_pos
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Fintype.card (EqualityRetainedPorts Q) ≤ 36 * (s + t) :=
  equalityRetainedPorts_card_le_of_terminal_port_budget hp Q
    (equality_terminal_port_budget_of_parameter_pos hp Q ha)

/-- Forgetting the retained vertex leaves the underlying indexed half-edge;
incidence recovers that vertex, so this map is injective. -/
def equalityRetainedPortsEmbedding {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    EqualityRetainedPorts Q ↪ EqualityHalfEdge p where
  toFun z := z.2.1
  inj' := by
    intro x y hxy
    rcases x with ⟨u, h⟩
    rcases y with ⟨v, k⟩
    change h.1 = k.1 at hxy
    have huv0 : u.1 = v.1 := by
      rw [← h.2, ← k.2, hxy]
    have huv : u = v := Subtype.ext huv0
    subst v
    have hk : h = k := Subtype.ext hxy
    subst k
    rfl

/-- There are only `4p` indexed half-edge ports in the entire equality
multigraph, so the retained port set obeys the same absolute bound. -/
theorem equalityRetainedPorts_card_le_four_p {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    Fintype.card (EqualityRetainedPorts Q) ≤ 4 * p := by
  have hcard := Fintype.card_le_of_injective
    (equalityRetainedPortsEmbedding Q) (equalityRetainedPortsEmbedding Q).injective
  simp only [EqualityHalfEdge, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool] at hcard
  omega

/-- Retained vertices form a subset of the `p-s` equality blocks and hence
there are at most `p` of them. -/
theorem equalityRetainedVertices_card_le_p {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    (equalityRetainedVertices Q).card ≤ p := by
  classical
  have hsub : (equalityRetainedVertices Q).card ≤
      Fintype.card (EqualityVertex Q.1) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have htypecard : Fintype.card (EqualityVertex Q.1) = Q.1.parts.card := by
    rw [Fintype.card_subtype]
    simp
  rw [htypecard, Q.2.2.1] at hsub
  omega

#print axioms tree_outside_leaves_le_boundaryDegree
#print axioms equalitySupportGraph_preconnected
#print axioms equalitySupportGraph_degree_le_two_of_nonexceptional
#print axioms equalitySupportGraph_degree_eq_one_of_terminal
#print axioms equalityEdgeMultiplicity_ge_two_of_nonexceptional_adj
#print axioms equalityTerminal_card_le_treeBoundaryDegree
#print axioms equalityNeighborIndexedEdgesEmbedding
#print axioms equality_neighbor_multiplicity_sum_le_ports
#print axioms equalityExceptionalCore_degree_sum
#print axioms twice_treeBoundaryDegree_le_exceptionalDegree
#print axioms equality_terminal_port_budget_of_parameter_pos
#print axioms equality_retained_card_le_of_parameter_pos
#print axioms equalityRetainedPorts_card_le_of_parameter_pos
#print axioms equalityRetainedPortsEmbedding
#print axioms equalityRetainedPorts_card_le_four_p
#print axioms equalityRetainedVertices_card_le_p

end Problem56
