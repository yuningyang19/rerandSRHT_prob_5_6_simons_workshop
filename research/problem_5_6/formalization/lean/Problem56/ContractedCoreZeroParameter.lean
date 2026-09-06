import Problem56.ContractedCorePathOrder
import Problem56.ContractedCoreTransition
import Problem56.ContractedCoreWordReconstruction

/-!
# The zero-exceptional-parameter branch

When `s + t = 0`, I19 says that the equality multigraph has one of two
underlying doubled degree-two shapes.  The closed family is a doubled cycle
(with the `p = 2` member represented by four parallel edges), while the open
family is a doubled path with one loop at each endpoint.  This file isolates
that dichotomy and the port-conjugacy interface needed to encode the original
cyclic Euler transition by `8 * p * 3 ^ p` choices.

The source half-edge type is retained throughout, so loops and indexed
parallel edges are never identified.
-/

namespace Problem56

open SimpleGraph

noncomputable section

/-- The closed zero-parameter family.  For `p > 2` every vertex is internal;
for `p = 2` the same doubled-cycle convention is the four-parallel-edge
multigraph. -/
def ZeroParameterClosedFamily {p : ℕ} (Q : SelectorEqualityData p 0 0) : Prop :=
  (∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B) ∨
    (p = 2 ∧ ∀ B ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 B)

/-- The open zero-parameter family: a doubled path with a loop at each of its
two distinct endpoints and internal vertices in between. -/
def ZeroParameterOpenFamily {p : ℕ} (Q : SelectorEqualityData p 0 0) : Prop :=
  ∃ U ∈ Q.1.parts, ∃ V ∈ Q.1.parts, U ≠ V ∧
    IsEqualityLoopTerminal Q.1 U ∧ IsEqualityLoopTerminal Q.1 V ∧
    ∀ B ∈ Q.1.parts, B ≠ U → B ≠ V → IsEqualityInternal Q.1 B

/-- Source-faithful two-family classification at zero exceptional parameter.
The impossible one-block case is eliminated using `p ≥ 2`, while the
two-block four-edge case is retained explicitly as the degenerate closed
cycle. -/
theorem zero_parameter_two_family_classification {p : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p 0 0) :
    ZeroParameterClosedFamily Q ∨ ZeroParameterOpenFamily Q := by
  have hE : equalityExceptionalVertices Q.1 = ∅ :=
    equality_exceptional_empty_of_parameter_eq_zero hp Q rfl
  rcases equality_exceptional_empty_classification hp Q hE with
    hall | hopen | hfour | hone
  · exact Or.inl (Or.inl hall)
  · exact Or.inr hopen
  · left
    right
    have hparts : Q.1.parts.card = p := by simpa using Q.2.2.1
    exact ⟨by omega, hfour.2⟩
  · have hparts : Q.1.parts.card = p := by simpa using Q.2.2.1
    omega

private theorem equalitySupportGraph_degree_eq_two_of_internal
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (u : EqualityVertex Q.1) (hu : IsEqualityInternal Q.1 u.1) :
    (equalitySupportGraph Q).degree u = 2 := by
  classical
  rcases hu with
    ⟨_, C, hC, D, hD, hCD, hCu, hDu, hCm, hDm, hother⟩
  let c : EqualityVertex Q.1 := ⟨C, hC⟩
  let d : EqualityVertex Q.1 := ⟨D, hD⟩
  have hneighbors : (equalitySupportGraph Q).neighborFinset u = {c, d} := by
    ext v
    constructor
    · intro hv
      have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
      by_cases hvc : v = c
      · simp [hvc]
      by_cases hvd : v = d
      · simp [hvd]
      have hvu : v.1 ≠ u.1 := by
        intro h
        exact hadj.1 (Subtype.ext h.symm)
      have hvC : v.1 ≠ C := fun h ↦ hvc (Subtype.ext h)
      have hvD : v.1 ≠ D := fun h ↦ hvd (Subtype.ext h)
      have hz := hother v.1 v.2 hvu hvC hvD
      have hpos := hadj.2
      exact (by omega : False).elim
    · intro hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ((equalitySupportGraph Q).mem_neighborFinset u c).mpr
          ⟨by exact fun h ↦ hCu (congrArg Subtype.val h.symm), by
            change 0 < equalityEdgeMultiplicity Q.1 u.1 C
            rw [hCm]
            omega⟩
      · exact ((equalitySupportGraph Q).mem_neighborFinset u d).mpr
          ⟨by exact fun h ↦ hDu (congrArg Subtype.val h.symm), by
            change 0 < equalityEdgeMultiplicity Q.1 u.1 D
            rw [hDm]
            omega⟩
  rw [← (equalitySupportGraph Q).card_neighborFinset_eq_degree,
    hneighbors]
  simp [c, d, hCD]

private theorem equalitySupportGraph_degree_eq_one_of_loop_terminal
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (u : EqualityVertex Q.1) (hu : IsEqualityLoopTerminal Q.1 u.1) :
    (equalitySupportGraph Q).degree u = 1 := by
  classical
  rcases hu with ⟨_, C, hC, hCu, hCm, hother⟩
  let c : EqualityVertex Q.1 := ⟨C, hC⟩
  have hneighbors : (equalitySupportGraph Q).neighborFinset u = {c} := by
    ext v
    constructor
    · intro hv
      have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
      by_cases hvc : v = c
      · simp [hvc]
      have hvu : v.1 ≠ u.1 := by
        intro h
        exact hadj.1 (Subtype.ext h.symm)
      have hvC : v.1 ≠ C := fun h ↦ hvc (Subtype.ext h)
      have hz := hother v.1 v.2 hvu hvC
      have hpos := hadj.2
      exact (by omega : False).elim
    · intro hv
      have hvc : v = c := Finset.mem_singleton.mp hv
      subst v
      exact ((equalitySupportGraph Q).mem_neighborFinset u c).mpr
        ⟨by exact fun h ↦ hCu (congrArg Subtype.val h.symm), by
          change 0 < equalityEdgeMultiplicity Q.1 u.1 C
          rw [hCm]
          omega⟩
  rw [← (equalitySupportGraph Q).card_neighborFinset_eq_degree,
    hneighbors]
  simp

private theorem equalitySupportGraph_degree_eq_one_of_four_terminal
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (u : EqualityVertex Q.1) (hu : IsEqualityFourEdgeTerminal Q.1 u.1) :
    (equalitySupportGraph Q).degree u = 1 := by
  classical
  rcases hu with ⟨_, C, hC, hCu, hCm, hother⟩
  let c : EqualityVertex Q.1 := ⟨C, hC⟩
  have hneighbors : (equalitySupportGraph Q).neighborFinset u = {c} := by
    ext v
    constructor
    · intro hv
      have hadj := ((equalitySupportGraph Q).mem_neighborFinset u v).mp hv
      by_cases hvc : v = c
      · simp [hvc]
      have hvu : v.1 ≠ u.1 := by
        intro h
        exact hadj.1 (Subtype.ext h.symm)
      have hvC : v.1 ≠ C := fun h ↦ hvc (Subtype.ext h)
      have hz := hother v.1 v.2 hvu hvC
      have hpos := hadj.2
      exact (by omega : False).elim
    · intro hv
      have hvc : v = c := Finset.mem_singleton.mp hv
      subst v
      exact ((equalitySupportGraph Q).mem_neighborFinset u c).mpr
        ⟨by exact fun h ↦ hCu (congrArg Subtype.val h.symm), by
          change 0 < equalityEdgeMultiplicity Q.1 u.1 C
          rw [hCm]
          omega⟩
  rw [← (equalitySupportGraph Q).card_neighborFinset_eq_degree,
    hneighbors]
  simp

private theorem zeroParameterEqualityVertex_card {p : ℕ}
    (Q : SelectorEqualityData p 0 0) :
    Fintype.card (EqualityVertex Q.1) = p := by
  simpa only [EqualityVertex, Fintype.card_coe, Nat.sub_zero] using Q.2.2.1

private theorem simpleGraph_degree_eq_of_fintypes {V : Type*}
    (G : SimpleGraph V) (v : V)
    (f₁ f₂ : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree V G v f₁ = @SimpleGraph.degree V G v f₂ := by
  unfold SimpleGraph.degree
  apply congrArg Finset.card
  ext w
  simp only [SimpleGraph.mem_neighborFinset]

private theorem cycleGraph_isCycles_of_three_le {p : ℕ} (hp : 3 ≤ p) :
    (cycleGraph p).IsCycles := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hp
  intro v _hv
  rw [Set.ncard_eq_toFinset_card', ← (cycleGraph (n + 3)).neighborFinset_def,
    (cycleGraph (n + 3)).card_neighborFinset_eq_degree,
    cycleGraph_degree_three_le]

/-- A closed all-internal support graph is cyclically ordered.  The special
two-vertex member is handled separately as a four-parallel-edge graph. -/
structure ZeroParameterClosedVertexOrder {p : ℕ}
    (Q : SelectorEqualityData p 0 0) where
  vertexAt : Fin p ≃ EqualityVertex Q.1
  adjacent_iff_cycle : ∀ i j : Fin p,
    (equalitySupportGraph Q).Adj (vertexAt i) (vertexAt j) ↔
      (cycleGraph p).Adj i j

/-- For `p ≥ 3`, the all-internal closed family is a single spanning
cycle, with the exact cycle-graph adjacency law. -/
theorem zeroParameterClosedVertexOrder_nonempty {p : ℕ} (hp : 3 ≤ p)
    (Q : SelectorEqualityData p 0 0)
    (hall : ∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B) :
    Nonempty (ZeroParameterClosedVertexOrder Q) := by
  classical
  have hparts : Q.1.parts.card = p := by simpa using Q.2.2.1
  have hpartsNonempty : Q.1.parts.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hparts
    simp at hparts
    omega
  obtain ⟨U, hU⟩ := hpartsNonempty
  let u : EqualityVertex Q.1 := ⟨U, hU⟩
  let G := equalitySupportGraph Q
  letI : Nonempty (EqualityVertex Q.1) := ⟨u⟩
  have hdegree_eq (w : EqualityVertex Q.1)
      (f : Fintype (G.neighborSet w)) :
      @SimpleGraph.degree _ G w f =
        @SimpleGraph.degree _ G w
          (equalitySupportGraphLocallyFinite Q w) :=
    simpleGraph_degree_eq_of_fintypes G w f
      (equalitySupportGraphLocallyFinite Q w)
  have hdegree (w : EqualityVertex Q.1) : G.degree w = 2 :=
    equalitySupportGraph_degree_eq_two_of_internal Q w (hall w.1 w.2)
  have hcycles : G.IsCycles := by
    intro w _hw
    rw [Set.ncard_eq_toFinset_card', ← G.neighborFinset_def,
      G.card_neighborFinset_eq_degree, hdegree_eq, hdegree]
  have hconnected : G.Connected :=
    ⟨equalitySupportGraph_preconnected (by omega) Q⟩
  let c := G.connectedComponentMk u
  have hcsupp : c.supp = Set.univ := by
    ext w
    simp only [Set.mem_univ, iff_true, ConnectedComponent.mem_supp_iff, c]
    exact ConnectedComponent.eq.mpr (hconnected.preconnected w u)
  have huNeighbor : (G.neighborSet u).Nonempty := by
    rw [← G.degree_pos_iff_nonempty, hdegree_eq, hdegree]
    omega
  obtain ⟨w, hwCycle, hwVerts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := c) (ConnectedComponent.connectedComponentMk_mem) huNeighbor
  have hwSupport (x : EqualityVertex Q.1) : x ∈ w.support := by
    rw [← w.mem_verts_toSubgraph, hwVerts, hcsupp]
    exact Set.mem_univ x
  have hwTailHamiltonian : w.tail.IsHamiltonian := by
    apply hwCycle.isPath_tail.isHamiltonian_of_mem
    intro x
    by_cases hxu : x = u
    · subst x
      rw [w.support_tail_of_not_nil hwCycle.not_nil]
      exact Walk.end_mem_tail_support hwCycle.not_nil
    · have hx := hwSupport x
      rw [← w.cons_support_tail hwCycle.not_nil] at hx
      simpa [hxu] using hx
  have hwLength : w.length = p := by
    have htailLength := hwTailHamiltonian.length_eq
    rw [zeroParameterEqualityVertex_card Q] at htailLength
    have hlen := w.length_tail_add_one hwCycle.not_nil
    omega
  obtain ⟨copy⟩ :=
    (cycleGraph_isContained_iff (by omega : 2 < p)).mpr
      ⟨u, w, hwCycle, hwLength⟩
  have hcopyBijective : Function.Bijective copy :=
    (Fintype.bijective_iff_injective_and_card copy).mpr
      ⟨copy.injective, by
        rw [Fintype.card_fin, zeroParameterEqualityVertex_card Q]⟩
  let vertexAt : Fin p ≃ EqualityVertex Q.1 :=
    Equiv.ofBijective copy hcopyBijective
  have hsourceCycles := cycleGraph_isCycles_of_three_le hp
  have hadj_iff (i j : Fin p) :
      G.Adj (vertexAt i) (vertexAt j) ↔ (cycleGraph p).Adj i j := by
    constructor
    · intro hij
      have hiNonempty : ((cycleGraph p).neighborSet i).Nonempty := by
        rw [← (cycleGraph p).degree_pos_iff_nonempty]
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hp
        rw [cycleGraph_degree_three_le]
        omega
      obtain ⟨k, hik⟩ := hiNonempty
      have hmapik : G.Adj (vertexAt i) (vertexAt k) :=
        copy.toHom.map_adj hik
      by_cases hjk : j = k
      · simpa [hjk] using hik
      obtain ⟨l, hkl, hil⟩ := hsourceCycles.other_adj_of_adj hik
      have hmapil : G.Adj (vertexAt i) (vertexAt l) :=
        copy.toHom.map_adj hil
      have hjmap : vertexAt k ≠ vertexAt j := by
        intro h
        exact hjk (vertexAt.injective h.symm)
      have hlmap : vertexAt k ≠ vertexAt l := by
        exact vertexAt.injective.ne hkl
      have htUnique := hcycles.existsUnique_ne_adj hmapik
      have hjl : vertexAt j = vertexAt l :=
        htUnique.unique ⟨hjmap, hij⟩ ⟨hlmap, hmapil⟩
      exact vertexAt.injective hjl ▸ hil
    · exact copy.toHom.map_adj
  exact ⟨⟨vertexAt, hadj_iff⟩⟩

/-- An open-family graph is ordered from one loop terminal to the other. -/
structure ZeroParameterOpenVertexOrder {p : ℕ}
    (Q : SelectorEqualityData p 0 0) where
  left : EqualityVertex Q.1
  right : EqualityVertex Q.1
  left_ne_right : left ≠ right
  left_loop : IsEqualityLoopTerminal Q.1 left.1
  right_loop : IsEqualityLoopTerminal Q.1 right.1
  vertexAt : Fin p ≃ EqualityVertex Q.1
  vertexAt_zero : vertexAt ⟨0, by
      rw [← zeroParameterEqualityVertex_card Q]
      exact Fintype.card_pos_iff.mpr ⟨left⟩⟩ = left
  vertexAt_last : vertexAt ⟨p - 1, by
      rw [← zeroParameterEqualityVertex_card Q]
      have hpos := Fintype.card_pos_iff.mpr ⟨right⟩
      omega⟩ = right
  interior : ∀ i : Fin p, i.val ≠ 0 → i.val + 1 ≠ p →
    IsEqualityInternal Q.1 (vertexAt i).1
  adjacent_iff_successive : ∀ i j : Fin p,
    (equalitySupportGraph Q).Adj (vertexAt i) (vertexAt j) ↔
      i.1 + 1 = j.1 ∨ j.1 + 1 = i.1

/-- The loop-ended family really is a spanning path, including `p = 2`.
This is the vertex-order half of the open-family canonicalization. -/
theorem zeroParameterOpenVertexOrder_nonempty {p : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p 0 0) (hopen : ZeroParameterOpenFamily Q) :
    Nonempty (ZeroParameterOpenVertexOrder Q) := by
  classical
  rcases hopen with
    ⟨U, hU, V, hV, hUV, hUloop, hVloop, hinterior⟩
  let u : EqualityVertex Q.1 := ⟨U, hU⟩
  let v : EqualityVertex Q.1 := ⟨V, hV⟩
  have huv : u ≠ v := fun h ↦ hUV (congrArg Subtype.val h)
  let G := equalitySupportGraph Q
  letI : Nonempty (EqualityVertex Q.1) := ⟨u⟩
  have hdegree_eq (w : EqualityVertex Q.1)
      (f : Fintype (G.neighborSet w)) :
      @SimpleGraph.degree _ G w f =
        @SimpleGraph.degree _ G w
          (equalitySupportGraphLocallyFinite Q w) :=
    simpleGraph_degree_eq_of_fintypes G w f
      (equalitySupportGraphLocallyFinite Q w)
  have hconnected : G.Connected :=
    ⟨equalitySupportGraph_preconnected hp Q⟩
  have huDegree : G.degree u = 1 :=
    equalitySupportGraph_degree_eq_one_of_loop_terminal Q u hUloop
  have hvDegree : G.degree v = 1 :=
    equalitySupportGraph_degree_eq_one_of_loop_terminal Q v hVloop
  have hdegree : ∀ w, G.degree w ≤ 2 := by
    intro w
    by_cases hwu : w = u
    · subst w
      omega
    by_cases hwv : w = v
    · subst w
      omega
    have hwU : w.1 ≠ U := fun h ↦ hwu (Subtype.ext h)
    have hwV : w.1 ≠ V := fun h ↦ hwv (Subtype.ext h)
    rw [equalitySupportGraph_degree_eq_two_of_internal Q w
      (hinterior w.1 w.2 hwU hwV)]
  have hsum : (∑ w, G.degree w) = 2 * p - 2 := by
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun w ↦ G.degree w) (Finset.mem_univ u)]
    have hvMem : v ∈ (Finset.univ : Finset (EqualityVertex Q.1)).erase u := by
      simp [huv.symm]
    rw [← Finset.sum_erase_add
      ((Finset.univ : Finset (EqualityVertex Q.1)).erase u)
      (fun w ↦ G.degree w) hvMem]
    rw [huDegree, hvDegree]
    have hrest :
        (∑ w ∈ ((Finset.univ : Finset (EqualityVertex Q.1)).erase u).erase v,
          G.degree w) =
          ∑ _w ∈ ((Finset.univ : Finset (EqualityVertex Q.1)).erase u).erase v,
            2 := by
      apply Finset.sum_congr rfl
      intro w hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
      have hwu : w ≠ u := by
        have := hw.2
        simpa only [ne_eq] using this
      have hwv : w ≠ v := hw.1
      have hwU : w.1 ≠ U := fun h ↦ hwu (Subtype.ext h)
      have hwV : w.1 ≠ V := fun h ↦ hwv (Subtype.ext h)
      exact equalitySupportGraph_degree_eq_two_of_internal Q w
        (hinterior w.1 w.2 hwU hwV)
    rw [hrest]
    simp only [Finset.sum_const_nat, Nat.card_pos, smul_eq_mul]
    rw [Finset.card_erase_of_mem hvMem,
      Finset.card_erase_of_mem (Finset.mem_univ u)]
    rw [Finset.card_univ, zeroParameterEqualityVertex_card Q]
    omega
  have hedgeCard : G.edgeFinset.card = p - 1 := by
    have hhandshake :
        (∑ w, @SimpleGraph.degree _ G w
          (equalitySupportGraphLocallyFinite Q w)) =
            2 * G.edgeFinset.card := by
      simpa only [hdegree_eq] using G.sum_degrees_eq_twice_card_edges
    rw [hsum] at hhandshake
    omega
  have htree : G.IsTree := by
    apply (SimpleGraph.isTree_iff_connected_and_card).mpr
    constructor
    · exact hconnected
    · have hedgeSucc : G.edgeFinset.card + 1 = p := by omega
      simpa only [Nat.card_eq_fintype_card,
        zeroParameterEqualityVertex_card Q,
        ← G.edgeFinset_card] using hedgeSucc
  let w : G.Walk u v := (htree.existsUnique_path u v).choose
  have hwPath : w.IsPath := (htree.existsUnique_path u v).choose_spec.1
  have hwHamiltonian : w.IsHamiltonian := by
    apply walk_isHamiltonian_of_isTree_of_degree_le_two hwPath htree huv
    · rw [hdegree_eq]
      exact huDegree.le
    · rw [hdegree_eq]
      exact hvDegree.le
    · intro x
      rw [hdegree_eq]
      exact hdegree x
  have hsupportLength : w.support.length = p := by
    rw [hwHamiltonian.length_support, zeroParameterEqualityVertex_card Q]
  let vertexAt : Fin p ≃ EqualityVertex Q.1 :=
    (finCongr hsupportLength.symm).trans hwHamiltonian.supportGetEquiv
  have vertexAt_getVert (i : Fin p) : vertexAt i = w.getVert i.1 := by
    simp only [vertexAt, Equiv.trans_apply, finCongr_apply,
      Walk.IsHamiltonian.supportGetEquiv_apply]
    have hi : i.1 ≤ w.length := by
      have hi' := i.2
      rw [hwHamiltonian.length_eq, zeroParameterEqualityVertex_card Q]
      omega
    have hisupp : i.1 < w.support.length := by
      rw [hsupportLength]
      exact i.2
    exact (w.getVert_eq_support_getElem hi).symm
  let iZero : Fin p := ⟨0, by omega⟩
  let iLast : Fin p := ⟨p - 1, by omega⟩
  have hvertexZero : vertexAt iZero = u := by
    rw [vertexAt_getVert]
    exact w.getVert_zero
  have hvertexLast : vertexAt iLast = v := by
    rw [vertexAt_getVert]
    have hval : p - 1 = w.length := by
      rw [hwHamiltonian.length_eq, zeroParameterEqualityVertex_card Q]
    change w.getVert (p - 1) = v
    rw [hval]
    exact w.getVert_length
  refine ⟨
    { left := u
      right := v
      left_ne_right := huv
      left_loop := hUloop
      right_loop := hVloop
      vertexAt := vertexAt
      vertexAt_zero := hvertexZero
      vertexAt_last := hvertexLast
      interior := ?_
      adjacent_iff_successive := ?_ }⟩
  · intro i hiZero hiLast
    apply hinterior (vertexAt i).1 (vertexAt i).2
    · intro hiU
      have hiu : vertexAt i = u := Subtype.ext hiU
      have hii : i = iZero := vertexAt.injective (hiu.trans hvertexZero.symm)
      exact hiZero (congrArg Fin.val hii)
    · intro hiV
      have hiv : vertexAt i = v := Subtype.ext hiV
      have hii : i = iLast := vertexAt.injective (hiv.trans hvertexLast.symm)
      have hval := congrArg Fin.val hii
      simp only [iLast] at hval
      omega
  · intro i j
    rw [vertexAt_getVert, vertexAt_getVert]
    apply walk_adj_getVert_iff_of_isHamiltonian_isTree hwPath hwHamiltonian htree
    · rw [hwHamiltonian.length_eq, zeroParameterEqualityVertex_card Q]
      omega
    · rw [hwHamiltonian.length_eq, zeroParameterEqualityVertex_card Q]
      omega

/-- Canonical ports have one of four incidence labels at each of `p`
canonically ordered vertices. -/
abbrev ZeroParameterCanonicalPort (p : ℕ) := Fin p × Fin 4

/-- The family tag: `0` is the closed doubled cycle and `1` is the loop-ended
doubled path. -/
abbrev ZeroParameterFamilyTag := Fin 2

/-- Edge reversal on source half-edges, including the two distinct incidences
of a loop. -/
def zeroParameterSourceOpposite {p : ℕ} : EqualityHalfEdge p → EqualityHalfEdge p
  | (e, b) => (e, !b)

@[simp] theorem zeroParameterSourceOpposite_involutive {p : ℕ} :
    Function.Involutive (zeroParameterSourceOpposite (p := p)) := by
  rintro ⟨e, b⟩
  cases b <;> rfl

theorem zeroParameterSourceOpposite_ne {p : ℕ} (h : EqualityHalfEdge p) :
    zeroParameterSourceOpposite h ≠ h := by
  rcases h with ⟨e, b⟩
  cases b <;> simp [zeroParameterSourceOpposite]

/-- The cyclic trace transition at a source vertex.  It pairs an outgoing
occurrence with the arrival along its predecessor, and an arrival with the
next outgoing occurrence. -/
noncomputable def zeroParameterSourceTransition {p : ℕ} (hp : 2 ≤ p) :
    EqualityHalfEdge p → EqualityHalfEdge p := fun h ↦ by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rcases h with ⟨e, b⟩
  cases b
  · exact ((cyclicSuccEquiv (2 * p)).symm e, true)
  · exact (cyclicSucc e, false)

@[simp] theorem zeroParameterSourceTransition_involutive {p : ℕ}
    (hp : 2 ≤ p) : Function.Involutive (zeroParameterSourceTransition hp) := by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rintro ⟨e, b⟩
  cases b
  · apply Prod.ext
    · simp only [zeroParameterSourceTransition]
      change cyclicSucc ((cyclicSuccEquiv (2 * p)).symm e) = e
      rw [← cyclicSuccEquiv_apply,
        (cyclicSuccEquiv (2 * p)).apply_symm_apply]
    · rfl
  · apply Prod.ext
    · simp only [zeroParameterSourceTransition]
      change (cyclicSuccEquiv (2 * p)).symm (cyclicSucc e) = e
      rw [← cyclicSuccEquiv_apply,
        (cyclicSuccEquiv (2 * p)).symm_apply_apply]
    · rfl

theorem zeroParameterSourceTransition_ne {p : ℕ} (hp : 2 ≤ p)
    (h : EqualityHalfEdge p) : zeroParameterSourceTransition hp h ≠ h := by
  rcases h with ⟨e, b⟩
  cases b <;> intro hEq
  · have := congrArg Prod.snd hEq
    simp [zeroParameterSourceTransition] at this
  · have := congrArg Prod.snd hEq
    simp [zeroParameterSourceTransition] at this

/-- Edge reversal followed by the local transition advances the source
occurrence word by one position. -/
@[simp] theorem zeroParameterSourceTransition_opposite {p : ℕ}
    (hp : 2 ≤ p) (e : Fin (2 * p)) :
    zeroParameterSourceTransition hp
        (zeroParameterSourceOpposite (e, false)) =
      (cyclicSucc e, false) := by
  letI : NeZero (2 * p) := ⟨by omega⟩
  change (cyclicSucc e, false) = (cyclicSucc e, false)
  rfl

/-- The trace transition stays in the same source equality vertex. -/
@[simp] theorem equalityHalfEdgeVertex_zeroParameterSourceTransition
    {p : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p 0 0)
    (h : EqualityHalfEdge p) :
    equalityHalfEdgeVertex Q (zeroParameterSourceTransition hp h) =
      equalityHalfEdgeVertex Q h := by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rcases h with ⟨e, b⟩
  cases b
  · simp only [zeroParameterSourceTransition, equalityHalfEdgeVertex,
      equalityEdgeDst, equalityEdgeSrc]
    congr 1
    change cyclicSucc ((cyclicSuccEquiv (2 * p)).symm e) = e
    rw [← cyclicSuccEquiv_apply,
      (cyclicSuccEquiv (2 * p)).apply_symm_apply]
  · rfl

private def zeroParameterEdgeSlot {p : ℕ} (e : Fin (2 * p)) : Fin p :=
  ⟨e.1 / 2, by omega⟩

/-- Vertex incident to a canonical closed-family port.  Edges `2i` and
`2i+1` are the two indexed copies between `i` and its cyclic successor.  At
`p = 2`, predecessor and successor agree and hence give four parallel edges
between the two vertices. -/
def zeroParameterClosedVertex {p : ℕ} (h : EqualityHalfEdge p) : Fin p :=
  match h.2 with
  | false => zeroParameterEdgeSlot h.1
  | true => cyclicSucc (zeroParameterEdgeSlot h.1)

private def zeroParameterOpenSrc {p : ℕ} (hp : 2 ≤ p)
    (e : Fin (2 * p)) : Fin p :=
  if hlast : e.1 + 1 = 2 * p then ⟨p - 1, by omega⟩
  else ⟨(e.1 - 1) / 2, by omega⟩

private def zeroParameterOpenDst {p : ℕ} (hp : 2 ≤ p)
    (e : Fin (2 * p)) : Fin p :=
  if hzero : e.1 = 0 then ⟨0, by omega⟩
  else if hlast : e.1 + 1 = 2 * p then ⟨p - 1, by omega⟩
  else ⟨(e.1 - 1) / 2 + 1, by omega⟩

/-- Vertex incident to a canonical open-family port.  Edge zero is the left
endpoint loop, edge `2p-1` the right endpoint loop, and the intervening edges
are consecutive parallel pairs. -/
def zeroParameterOpenVertex {p : ℕ} (hp : 2 ≤ p)
    (h : EqualityHalfEdge p) : Fin p :=
  match h.2 with
  | false => zeroParameterOpenSrc hp h.1
  | true => zeroParameterOpenDst hp h.1

/-- The vertex map for the two fixed canonical multigraph families. -/
def zeroParameterCanonicalVertex {p : ℕ} (hp : 2 ≤ p)
    (tag : ZeroParameterFamilyTag) (h : EqualityHalfEdge p) : Fin p :=
  if tag = 0 then zeroParameterClosedVertex h
  else zeroParameterOpenVertex hp h

@[simp] theorem zeroParameterCanonicalVertex_opposite {p : ℕ}
    (hp : 2 ≤ p) (tag : ZeroParameterFamilyTag) (h : EqualityHalfEdge p) :
    zeroParameterCanonicalVertex hp tag (zeroParameterSourceOpposite h) =
      (if tag = 0 then
        match h.2 with
        | false => cyclicSucc (zeroParameterEdgeSlot h.1)
        | true => zeroParameterEdgeSlot h.1
      else
        match h.2 with
        | false => zeroParameterOpenDst hp h.1
        | true => zeroParameterOpenSrc hp h.1) := by
  rcases h with ⟨e, b⟩
  cases b <;> simp [zeroParameterCanonicalVertex,
    zeroParameterClosedVertex, zeroParameterOpenVertex,
    zeroParameterSourceOpposite]

private theorem fixedPointFreeInvolution_fin_four_card_le :
    Fintype.card (FixedPointFreeInvolution (Fin 4)) ≤ 3 := by
  calc
    Fintype.card (FixedPointFreeInvolution (Fin 4)) ≤
        Fintype.card (Pairing (Finset.univ : Finset (Fin 4))) :=
      fixedPointFreeInvolution_card_le_pairing
    _ ≤ 3 := by
      simpa using
        (pairing_univ_card_sharp_bound (M := 4) (by simp) (by simp)
          (by exact ⟨2, rfl⟩) :
            Fintype.card (Pairing (Finset.univ : Finset (Fin 4))) ≤ 3)

/-- Every block has exactly two occurrences at zero exceptional parameter. -/
theorem zeroParameter_block_card {p : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p 0 0) (B : Finset (Fin (2 * p)))
    (hB : B ∈ Q.1.parts) : B.card = 2 := by
  have hE : equalityExceptionalVertices Q.1 = ∅ :=
    equality_exceptional_empty_of_parameter_eq_zero hp Q rfl
  have hnotLarge : ¬2 < B.card := by
    intro hlarge
    have hmem : B ∈ equalityExceptionalVertices Q.1 := by
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hB, hlarge⟩)
    rw [hE] at hmem
    exact Finset.notMem_empty B hmem
  have htwo := Q.2.1 B hB
  omega

/-- A source-to-canonical conjugacy.  Edge reversal is preserved on the
indexed half-edge type; `vertexEquiv` records the canonical ordering of the
unlabelled equality vertices.  The shape field prevents the family tag from
forgetting the I19 dichotomy. -/
structure ZeroParameterCanonicalization {p : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p 0 0) where
  tag : ZeroParameterFamilyTag
  portEquiv : EqualityHalfEdge p ≃ EqualityHalfEdge p
  vertexEquiv : EqualityVertex Q.1 ≃ Fin p
  port_vertex : ∀ h,
    vertexEquiv (equalityHalfEdgeVertex Q h) =
      zeroParameterCanonicalVertex hp tag (portEquiv h)
  opposite : ∀ h,
    portEquiv (zeroParameterSourceOpposite h) =
      zeroParameterSourceOpposite (portEquiv h)
  shape :
    (tag = 0 ∧ ZeroParameterClosedFamily Q) ∨
      (tag = 1 ∧ ZeroParameterOpenFamily Q)

/-- The exact remaining structural obligation for the zero branch: I19's
two-family classification must be upgraded to a port-level conjugacy with the
fixed canonical models. -/
def ZeroParameterCanonicalizationExists {p : ℕ} (hp : 2 ≤ p) : Prop :=
  ∀ Q : SelectorEqualityData p 0 0,
    Nonempty (ZeroParameterCanonicalization hp Q)

/-- Source and canonical endpoints of an indexed edge. -/
def zeroParameterCanonicalEdgeSrc {p : ℕ} (hp : 2 ≤ p)
    (tag : ZeroParameterFamilyTag) (e : Fin (2 * p)) : Fin p :=
  zeroParameterCanonicalVertex hp tag (e, false)

def zeroParameterCanonicalEdgeDst {p : ℕ} (hp : 2 ≤ p)
    (tag : ZeroParameterFamilyTag) (e : Fin (2 * p)) : Fin p :=
  zeroParameterCanonicalVertex hp tag (e, true)

/-- The graph-theoretic core of a canonicalization: an ordering of vertices
and a bijection of indexed edges preserving their unordered endpoint pairs.
The port-level conjugacy is derived from this data below. -/
structure ZeroParameterEdgeCanonicalization {p : ℕ} (hp : 2 ≤ p)
    (Q : SelectorEqualityData p 0 0) where
  tag : ZeroParameterFamilyTag
  vertexEquiv : EqualityVertex Q.1 ≃ Fin p
  edgeEquiv : Fin (2 * p) ≃ Fin (2 * p)
  endpoints : ∀ e,
    (zeroParameterCanonicalEdgeSrc hp tag (edgeEquiv e) =
        vertexEquiv (equalityEdgeSrc Q e) ∧
      zeroParameterCanonicalEdgeDst hp tag (edgeEquiv e) =
        vertexEquiv (equalityEdgeDst Q e)) ∨
    (zeroParameterCanonicalEdgeSrc hp tag (edgeEquiv e) =
        vertexEquiv (equalityEdgeDst Q e) ∧
      zeroParameterCanonicalEdgeDst hp tag (edgeEquiv e) =
        vertexEquiv (equalityEdgeSrc Q e))
  shape :
    (tag = 0 ∧ ZeroParameterClosedFamily Q) ∨
      (tag = 1 ∧ ZeroParameterOpenFamily Q)

private theorem equalityEdgeSrc_ne_dst_of_no_loops
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (hloop : ∀ B ∈ Q.1.parts, equalityLoopsAt Q.1 B = 0)
    (e : Fin (2 * p)) : equalityEdgeSrc Q e ≠ equalityEdgeDst Q e := by
  intro heq
  have heq' : Q.1.part e = Q.1.part (cyclicSucc e) :=
    congrArg Subtype.val heq
  have hmem : e ∈ ((Finset.univ : Finset (Fin (2 * p))).filter fun i ↦
      Q.1.part i = Q.1.part e ∧
        Q.1.part (cyclicSucc i) = Q.1.part e) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact heq'.symm
  have hpos : 0 < equalityLoopsAt Q.1 (Q.1.part e) := by
    unfold equalityLoopsAt
    exact Finset.card_pos.mpr ⟨e, hmem⟩
  have hz := hloop (Q.1.part e) (Q.1.part_mem.2 (Finset.mem_univ e))
  omega

private theorem sym2_fin_two_eq_of_ne
    {a b c d : Fin 2} (hab : a ≠ b) (hcd : c ≠ d) :
    s(a, b) = s(c, d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all

private theorem zeroParameterClosedEdge_endpoints_ne_two
    (hp : 2 ≤ 2) (e : Fin (2 * 2)) :
    zeroParameterCanonicalEdgeSrc hp 0 e ≠
      zeroParameterCanonicalEdgeDst hp 0 e := by
  fin_cases e <;>
    simp [zeroParameterCanonicalEdgeSrc, zeroParameterCanonicalEdgeDst,
      zeroParameterCanonicalVertex, zeroParameterClosedVertex,
      zeroParameterEdgeSlot, cyclicSucc]

/-- The degenerate `p = 2` closed member is canonically the two-vertex
four-parallel-edge model. -/
noncomputable def zeroParameterEdgeCanonicalization_closed_two
    (Q : SelectorEqualityData 2 0 0)
    (hfour : ∀ B ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 B) :
    ZeroParameterEdgeCanonicalization (p := 2) (by omega) Q := by
  let eV : EqualityVertex Q.1 ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (zeroParameterEqualityVertex_card Q)
  refine
    { tag := 0
      vertexEquiv := eV
      edgeEquiv := Equiv.refl _
      endpoints := ?_
      shape := Or.inl ⟨rfl, Or.inr ⟨rfl, hfour⟩⟩ }
  intro e
  have hsource : equalityEdgeSrc Q e ≠ equalityEdgeDst Q e :=
    equalityEdgeSrc_ne_dst_of_no_loops Q
      (fun B hB ↦ (hfour B hB).1) e
  have hsourceMap : eV (equalityEdgeSrc Q e) ≠
      eV (equalityEdgeDst Q e) := eV.injective.ne hsource
  have hcanonical :=
    zeroParameterClosedEdge_endpoints_ne_two (by omega) e
  have hkey :
      s(zeroParameterCanonicalEdgeSrc (by omega) 0 e,
          zeroParameterCanonicalEdgeDst (by omega) 0 e) =
        s(eV (equalityEdgeSrc Q e), eV (equalityEdgeDst Q e)) :=
    sym2_fin_two_eq_of_ne hcanonical hsourceMap
  exact Sym2.eq_iff.mp hkey

private def zeroParameterEdgeAligned {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) (e : Fin (2 * p)) : Prop :=
  zeroParameterCanonicalEdgeSrc hp E.tag (E.edgeEquiv e) =
    E.vertexEquiv (equalityEdgeSrc Q e)

private noncomputable def zeroParameterPortEquivOfEdgeCanonicalization
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) :
    EqualityHalfEdge p ≃ EqualityHalfEdge p := by
  classical
  exact
    { toFun := fun h ↦
        if zeroParameterEdgeAligned E h.1 then (E.edgeEquiv h.1, h.2)
        else (E.edgeEquiv h.1, !h.2)
      invFun := fun h ↦
        let e := E.edgeEquiv.symm h.1
        if zeroParameterEdgeAligned E e then (e, h.2) else (e, !h.2)
      left_inv := by
        rintro ⟨e, b⟩
        by_cases he : zeroParameterEdgeAligned E e
        · simp [he]
        · cases b <;> simp [he]
      right_inv := by
        rintro ⟨e, b⟩
        by_cases he : zeroParameterEdgeAligned E (E.edgeEquiv.symm e)
        · simp [he]
        · cases b <;> simp [he] }

private theorem zeroParameterEdgeDst_eq_of_aligned
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) (e : Fin (2 * p))
    (he : zeroParameterEdgeAligned E e) :
    zeroParameterCanonicalEdgeDst hp E.tag (E.edgeEquiv e) =
      E.vertexEquiv (equalityEdgeDst Q e) := by
  rcases E.endpoints e with h | h
  · exact h.2
  · rw [h.2, ← he, h.1]

private theorem zeroParameterEdgeSrcDst_eq_of_not_aligned
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) (e : Fin (2 * p))
    (he : ¬zeroParameterEdgeAligned E e) :
    zeroParameterCanonicalEdgeSrc hp E.tag (E.edgeEquiv e) =
        E.vertexEquiv (equalityEdgeDst Q e) ∧
      zeroParameterCanonicalEdgeDst hp E.tag (E.edgeEquiv e) =
        E.vertexEquiv (equalityEdgeSrc Q e) := by
  rcases E.endpoints e with h | h
  · exact (he h.1).elim
  · exact h

@[simp] private theorem zeroParameterPortEquivOfEdge_opposite
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) (h : EqualityHalfEdge p) :
    zeroParameterPortEquivOfEdgeCanonicalization E
        (zeroParameterSourceOpposite h) =
    zeroParameterSourceOpposite
        (zeroParameterPortEquivOfEdgeCanonicalization E h) := by
  classical
  rcases h with ⟨e, b⟩
  by_cases he : zeroParameterEdgeAligned E e
  · cases b <;> simp [zeroParameterPortEquivOfEdgeCanonicalization,
      zeroParameterSourceOpposite, he]
  · cases b <;> simp [zeroParameterPortEquivOfEdgeCanonicalization,
      zeroParameterSourceOpposite, he]

private theorem zeroParameterPortEquivOfEdge_vertex
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) (h : EqualityHalfEdge p) :
    E.vertexEquiv (equalityHalfEdgeVertex Q h) =
      zeroParameterCanonicalVertex hp E.tag
        (zeroParameterPortEquivOfEdgeCanonicalization E h) := by
  classical
  rcases h with ⟨e, b⟩
  by_cases he : zeroParameterEdgeAligned E e
  · have hd := zeroParameterEdgeDst_eq_of_aligned E e he
    cases b
    · simpa [zeroParameterPortEquivOfEdgeCanonicalization, he,
        zeroParameterCanonicalEdgeSrc, equalityHalfEdgeVertex] using he.symm
    · simpa [zeroParameterPortEquivOfEdgeCanonicalization, he,
        zeroParameterCanonicalEdgeDst, equalityHalfEdgeVertex] using hd.symm
  · have hsd := zeroParameterEdgeSrcDst_eq_of_not_aligned E e he
    cases b
    · simpa [zeroParameterPortEquivOfEdgeCanonicalization, he,
        zeroParameterCanonicalEdgeDst, equalityHalfEdgeVertex] using hsd.2.symm
    · simpa [zeroParameterPortEquivOfEdgeCanonicalization, he,
        zeroParameterCanonicalEdgeSrc, equalityHalfEdgeVertex] using hsd.1.symm

/-- Any indexed-edge canonicalization lifts canonically to the required
half-edge conjugacy, including loop orientation and parallel copies. -/
noncomputable def zeroParameterCanonicalizationOfEdge
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (E : ZeroParameterEdgeCanonicalization hp Q) :
    ZeroParameterCanonicalization hp Q where
  tag := E.tag
  portEquiv := zeroParameterPortEquivOfEdgeCanonicalization E
  vertexEquiv := E.vertexEquiv
  port_vertex := zeroParameterPortEquivOfEdge_vertex E
  opposite := zeroParameterPortEquivOfEdge_opposite E
  shape := E.shape

private noncomputable def zeroParameterSingleFiberEquiv
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq κ]
    (f : α → κ) (g : β → κ)
    (hcard : ∀ k,
      Fintype.card {x : α // f x = k} =
        Fintype.card {y : β // g y = k}) (k : κ) :
    {x : α // f x = k} ≃ {y : β // g y = k} :=
  (Fintype.equivFin {x : α // f x = k}).trans
    ((finCongr (hcard k)).trans
      (Fintype.equivFin {y : β // g y = k}).symm)

private noncomputable def zeroParameterFiberwiseEquiv
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq κ]
    (f : α → κ) (g : β → κ)
    (hcard : ∀ k,
      Fintype.card {x : α // f x = k} =
        Fintype.card {y : β // g y = k}) : α ≃ β :=
  (Equiv.sigmaFiberEquiv f).symm |>.trans
    ((Equiv.sigmaCongrRight
      (zeroParameterSingleFiberEquiv f g hcard)).trans
        (Equiv.sigmaFiberEquiv g))

@[simp] private theorem zeroParameterFiberwiseEquiv_key
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq κ]
    (f : α → κ) (g : β → κ)
    (hcard : ∀ k,
      Fintype.card {x : α // f x = k} =
        Fintype.card {y : β // g y = k}) (x : α) :
    g (zeroParameterFiberwiseEquiv f g hcard x) = f x := by
  classical
  let sx : {a : α // f a = f x} := ⟨x, rfl⟩
  change g ((zeroParameterSingleFiberEquiv f g hcard (f x))
    sx).1 = f x
  exact ((zeroParameterSingleFiberEquiv f g hcard (f x))
    sx).2

private def zeroParameterSourceEdgeKey
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (eV : EqualityVertex Q.1 ≃ Fin p) (e : Fin (2 * p)) : Sym2 (Fin p) :=
  s(eV (equalityEdgeSrc Q e), eV (equalityEdgeDst Q e))

private def zeroParameterCanonicalEdgeKey
    {p : ℕ} (hp : 2 ≤ p) (tag : ZeroParameterFamilyTag)
    (e : Fin (2 * p)) : Sym2 (Fin p) :=
  s(zeroParameterCanonicalEdgeSrc hp tag e,
    zeroParameterCanonicalEdgeDst hp tag e)

private theorem cyclicSucc_eq_add_one_local {q : ℕ} [NeZero q]
    (i : Fin q) : cyclicSucc i = i + 1 := by
  apply Fin.ext
  simp [cyclicSucc, Fin.add_def]

private theorem cyclicSucc_cyclicSucc_ne_of_three_le {p : ℕ}
    (hp : 3 ≤ p) (i : Fin p) : cyclicSucc (cyclicSucc i) ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cyclicSucc] at hv
  by_cases h₁ : i.val + 1 < p
  · rw [Nat.mod_eq_of_lt h₁] at hv
    by_cases h₂ : i.val + 1 + 1 < p
    · rw [Nat.mod_eq_of_lt h₂] at hv
      omega
    · have heq : i.val + 1 + 1 = p := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  · have heq : i.val + 1 = p := by omega
    rw [heq, Nat.mod_self] at hv
    simp only [Nat.zero_add] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hv
    omega

private theorem zeroParameterClosedSlotKey_injective {p : ℕ}
    (hp : 3 ≤ p) :
    Function.Injective (fun i : Fin p ↦ s(i, cyclicSucc i)) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with h | h
  · exact h.1
  · exfalso
    have htwo : cyclicSucc (cyclicSucc j) = j := by
      rw [← h.1, h.2]
    exact cyclicSucc_cyclicSucc_ne_of_three_le hp j htwo

private theorem cycleGraph_adj_iff_exists_closedSlotKey {p : ℕ}
    (hp : 3 ≤ p) (u v : Fin p) :
    (cycleGraph p).Adj u v ↔
      ∃ i : Fin p, s(i, cyclicSucc i) = s(u, v) := by
  letI : NeZero p := ⟨by omega⟩
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hp
    rw [cycleGraph_adj] at h
    rcases h with h | h
    · refine ⟨v, ?_⟩
      rw [cyclicSucc_eq_add_one_local, (sub_eq_iff_eq_add').mp h]
      exact Sym2.eq_swap
    · refine ⟨u, ?_⟩
      rw [cyclicSucc_eq_add_one_local, (sub_eq_iff_eq_add').mp h]
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.mp hi with h | h
    · rw [← h.1, ← h.2]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hp
      rw [cycleGraph_adj, cyclicSucc_eq_add_one_local]
      right
      simp
    · rw [← h.1, ← h.2]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hp
      rw [cycleGraph_adj, cyclicSucc_eq_add_one_local]
      left
      simp

private def zeroParameterClosedEdgeIndexEquiv (p : ℕ) :
    Fin p × Fin 2 ≃ Fin (2 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 2))

@[simp] private theorem zeroParameterClosedEdgeIndexEquiv_val
    {p : ℕ} (x : Fin p × Fin 2) :
    (zeroParameterClosedEdgeIndexEquiv p x).val =
      2 * x.1.val + x.2.val := by
  simp [zeroParameterClosedEdgeIndexEquiv, finProdFinEquiv]
  omega

@[simp] private theorem zeroParameterClosedEdgeKey_index
    {p : ℕ} (hp : 2 ≤ p) (x : Fin p × Fin 2) :
    zeroParameterCanonicalEdgeKey hp 0
        (zeroParameterClosedEdgeIndexEquiv p x) =
      s(x.1, cyclicSucc x.1) := by
  unfold zeroParameterCanonicalEdgeKey
    zeroParameterCanonicalEdgeSrc zeroParameterCanonicalEdgeDst
    zeroParameterCanonicalVertex zeroParameterClosedVertex
    zeroParameterEdgeSlot
  simp only [if_pos, Fin.isValue, zeroParameterClosedEdgeIndexEquiv_val]
  have hdiv : (2 * x.1.val + x.2.val) / 2 = x.1.val := by
    omega
  simp only [hdiv]

private noncomputable def zeroParameterClosedCanonicalFiberEquiv
    {p : ℕ} (hp : 2 ≤ p) (k : Sym2 (Fin p)) :
    {e : Fin (2 * p) // zeroParameterCanonicalEdgeKey hp 0 e = k} ≃
      {i : Fin p // s(i, cyclicSucc i) = k} × Fin 2 :=
  (Equiv.subtypeEquiv (zeroParameterClosedEdgeIndexEquiv p)
    (fun x ↦ by rw [zeroParameterClosedEdgeKey_index])).symm.trans
      Equiv.prodSubtypeFstEquivSubtypeProd

private theorem zeroParameterClosedCanonicalFiber_card
    {p : ℕ} (hp : 2 ≤ p) (k : Sym2 (Fin p)) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterCanonicalEdgeKey hp 0 e = k} =
      2 * Fintype.card {i : Fin p // s(i, cyclicSucc i) = k} := by
  rw [Fintype.card_congr (zeroParameterClosedCanonicalFiberEquiv hp k),
    Fintype.card_prod, Fintype.card_fin]
  omega

private theorem zeroParameterClosedSlotFiber_card_le_one
    {p : ℕ} (hp : 3 ≤ p) (k : Sym2 (Fin p)) :
    Fintype.card {i : Fin p // s(i, cyclicSucc i) = k} ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro i j
  apply Subtype.ext
  exact zeroParameterClosedSlotKey_injective hp (i.2.trans j.2.symm)

private theorem zeroParameterClosedSlotFiber_card
    {p : ℕ} (hp : 3 ≤ p) (u v : Fin p) :
    Fintype.card {i : Fin p //
      s(i, cyclicSucc i) = s(u, v)} =
      if (cycleGraph p).Adj u v then 1 else 0 := by
  by_cases hadj : (cycleGraph p).Adj u v
  · simp only [hadj, if_true]
    obtain ⟨i, hi⟩ :=
      (cycleGraph_adj_iff_exists_closedSlotKey hp u v).mp hadj
    have hpos : 0 < Fintype.card {i : Fin p //
        s(i, cyclicSucc i) = s(u, v)} :=
      Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    have hle := zeroParameterClosedSlotFiber_card_le_one hp s(u, v)
    omega
  · simp only [hadj, if_false]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun i ↦ hadj
      ((cycleGraph_adj_iff_exists_closedSlotKey hp u v).mpr ⟨i.1, i.2⟩)⟩

private theorem zeroParameterClosedCanonicalFiber_card_pair
    {p : ℕ} (hp : 3 ≤ p) (u v : Fin p) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterCanonicalEdgeKey (by omega) 0 e = s(u, v)} =
      if (cycleGraph p).Adj u v then 2 else 0 := by
  rw [zeroParameterClosedCanonicalFiber_card,
    zeroParameterClosedSlotFiber_card hp]
  split <;> omega

private def zeroParameterOpenMiddleRightIndexEquiv (p : ℕ) :
    (Fin (p - 1) × Fin 2) ⊕ Fin 1 ≃ Fin ((p - 1) * 2 + 1) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

private def zeroParameterOpenEdgeIndexEquiv {p : ℕ} (hp : 2 ≤ p) :
    Fin 1 ⊕ ((Fin (p - 1) × Fin 2) ⊕ Fin 1) ≃ Fin (2 * p) :=
  (Equiv.sumCongr (Equiv.refl _) (zeroParameterOpenMiddleRightIndexEquiv p)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] private theorem zeroParameterOpenEdgeIndexEquiv_left_val
    {p : ℕ} (hp : 2 ≤ p) (z : Fin 1) :
    (zeroParameterOpenEdgeIndexEquiv hp (Sum.inl z)).val = 0 := by
  fin_cases z
  rfl

@[simp] private theorem zeroParameterOpenEdgeIndexEquiv_middle_val
    {p : ℕ} (hp : 2 ≤ p) (i : Fin (p - 1)) (b : Fin 2) :
    (zeroParameterOpenEdgeIndexEquiv hp (Sum.inr (Sum.inl (i, b)))).val =
      1 + (b.val + 2 * i.val) := by
  rfl

@[simp] private theorem zeroParameterOpenEdgeIndexEquiv_right_val
    {p : ℕ} (hp : 2 ≤ p) (z : Fin 1) :
    (zeroParameterOpenEdgeIndexEquiv hp (Sum.inr (Sum.inr z))).val =
      2 * p - 1 := by
  fin_cases z
  simp [zeroParameterOpenEdgeIndexEquiv,
    zeroParameterOpenMiddleRightIndexEquiv, finSumFinEquiv,
    finProdFinEquiv]
  omega

private def zeroParameterOpenPathSrc {p : ℕ} (hp : 2 ≤ p)
    (i : Fin (p - 1)) : Fin p := ⟨i.val, by omega⟩

private def zeroParameterOpenPathDst {p : ℕ} (hp : 2 ≤ p)
    (i : Fin (p - 1)) : Fin p := ⟨i.val + 1, by omega⟩

private def zeroParameterOpenLeftVertex {p : ℕ} (hp : 2 ≤ p) : Fin p :=
  ⟨0, by omega⟩

private def zeroParameterOpenRightVertex {p : ℕ} (hp : 2 ≤ p) : Fin p :=
  ⟨p - 1, by omega⟩

@[simp] private theorem zeroParameterOpenEdgeKey_left
    {p : ℕ} (hp : 2 ≤ p) (z : Fin 1) :
    zeroParameterCanonicalEdgeKey hp 1
        (zeroParameterOpenEdgeIndexEquiv hp (Sum.inl z)) =
      s(zeroParameterOpenLeftVertex hp, zeroParameterOpenLeftVertex hp) := by
  fin_cases z
  have hlast : 1 ≠ 2 * p := by omega
  simp [zeroParameterCanonicalEdgeKey, zeroParameterCanonicalEdgeSrc,
    zeroParameterCanonicalEdgeDst, zeroParameterCanonicalVertex,
    zeroParameterOpenVertex, zeroParameterOpenSrc, zeroParameterOpenDst,
    zeroParameterOpenLeftVertex, hlast]

@[simp] private theorem zeroParameterOpenEdgeKey_middle
    {p : ℕ} (hp : 2 ≤ p) (i : Fin (p - 1)) (b : Fin 2) :
    zeroParameterCanonicalEdgeKey hp 1
        (zeroParameterOpenEdgeIndexEquiv hp (Sum.inr (Sum.inl (i, b)))) =
      s(zeroParameterOpenPathSrc hp i, zeroParameterOpenPathDst hp i) := by
  unfold zeroParameterCanonicalEdgeKey zeroParameterCanonicalEdgeSrc
    zeroParameterCanonicalEdgeDst zeroParameterCanonicalVertex
    zeroParameterOpenVertex zeroParameterOpenSrc zeroParameterOpenDst
  simp only [Fin.isValue, zeroParameterOpenEdgeIndexEquiv_middle_val]
  have hzero : 1 + (b.val + 2 * i.val) ≠ 0 := by omega
  have hlast : 1 + (b.val + 2 * i.val) + 1 ≠ 2 * p := by omega
  simp only [one_ne_zero, if_false, dif_neg hzero, dif_neg hlast]
  have hsub : 1 + (b.val + 2 * i.val) - 1 = b.val + 2 * i.val := by omega
  have hdiv : (b.val + 2 * i.val) / 2 = i.val := by omega
  simp only [hsub, hdiv, zeroParameterOpenPathSrc, zeroParameterOpenPathDst]

@[simp] private theorem zeroParameterOpenEdgeKey_right
    {p : ℕ} (hp : 2 ≤ p) (z : Fin 1) :
    zeroParameterCanonicalEdgeKey hp 1
        (zeroParameterOpenEdgeIndexEquiv hp (Sum.inr (Sum.inr z))) =
      s(zeroParameterOpenRightVertex hp, zeroParameterOpenRightVertex hp) := by
  fin_cases z
  unfold zeroParameterCanonicalEdgeKey zeroParameterCanonicalEdgeSrc
    zeroParameterCanonicalEdgeDst zeroParameterCanonicalVertex
    zeroParameterOpenVertex zeroParameterOpenSrc zeroParameterOpenDst
    zeroParameterOpenRightVertex
  simp only [Fin.isValue, zeroParameterOpenEdgeIndexEquiv_right_val,
    one_ne_zero, if_false]
  have hne : 2 * p - 1 + 1 = 2 * p := by omega
  have hzero : 2 * p - 1 ≠ 0 := by omega
  simp only [dif_pos hne, dif_neg hzero]

private theorem zeroParameterOpenPathSlotKey_injective
    {p : ℕ} (hp : 2 ≤ p) :
    Function.Injective (fun i : Fin (p - 1) ↦
      s(zeroParameterOpenPathSrc hp i,
        zeroParameterOpenPathDst hp i)) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with h | h
  · apply Fin.ext
    have hval := congrArg Fin.val h.1
    simpa only [zeroParameterOpenPathSrc] using hval
  · have h₁ := congrArg Fin.val h.1
    have h₂ := congrArg Fin.val h.2
    simp only [zeroParameterOpenPathSrc, zeroParameterOpenPathDst] at h₁ h₂
    omega

private theorem successive_iff_exists_openPathSlotKey
    {p : ℕ} (hp : 2 ≤ p) (u v : Fin p) :
    (u.val + 1 = v.val ∨ v.val + 1 = u.val) ↔
      ∃ i : Fin (p - 1),
        s(zeroParameterOpenPathSrc hp i,
          zeroParameterOpenPathDst hp i) = s(u, v) := by
  constructor
  · rintro (h | h)
    · let i : Fin (p - 1) := ⟨u.val, by omega⟩
      refine ⟨i, ?_⟩
      apply Sym2.eq_iff.mpr
      left
      constructor <;> apply Fin.ext <;>
        simp [i, zeroParameterOpenPathSrc, zeroParameterOpenPathDst, h]
    · let i : Fin (p - 1) := ⟨v.val, by omega⟩
      refine ⟨i, ?_⟩
      apply Sym2.eq_iff.mpr
      right
      constructor <;> apply Fin.ext <;>
        simp [i, zeroParameterOpenPathSrc, zeroParameterOpenPathDst, h]
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.mp hi with h | h
    · left
      have h₁ := congrArg Fin.val h.1
      have h₂ := congrArg Fin.val h.2
      simp only [zeroParameterOpenPathSrc, zeroParameterOpenPathDst] at h₁ h₂
      omega
    · right
      have h₁ := congrArg Fin.val h.1
      have h₂ := congrArg Fin.val h.2
      simp only [zeroParameterOpenPathSrc, zeroParameterOpenPathDst] at h₁ h₂
      omega

private theorem zeroParameterOpenPathSlotFiber_card_le_one
    {p : ℕ} (hp : 2 ≤ p) (k : Sym2 (Fin p)) :
    Fintype.card {i : Fin (p - 1) //
      s(zeroParameterOpenPathSrc hp i,
        zeroParameterOpenPathDst hp i) = k} ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro i j
  apply Subtype.ext
  exact zeroParameterOpenPathSlotKey_injective hp (i.2.trans j.2.symm)

private theorem zeroParameterOpenPathSlotFiber_card
    {p : ℕ} (hp : 2 ≤ p) (u v : Fin p) :
    Fintype.card {i : Fin (p - 1) //
      s(zeroParameterOpenPathSrc hp i,
        zeroParameterOpenPathDst hp i) = s(u, v)} =
      if u.val + 1 = v.val ∨ v.val + 1 = u.val then 1 else 0 := by
  by_cases hsucc : u.val + 1 = v.val ∨ v.val + 1 = u.val
  · simp only [hsucc, if_true]
    obtain ⟨i, hi⟩ := (successive_iff_exists_openPathSlotKey hp u v).mp hsucc
    have hpos : 0 < Fintype.card {i : Fin (p - 1) //
        s(zeroParameterOpenPathSrc hp i,
          zeroParameterOpenPathDst hp i) = s(u, v)} :=
      Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    have hle := zeroParameterOpenPathSlotFiber_card_le_one hp s(u, v)
    omega
  · simp only [hsucc, if_false]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun i ↦ hsucc
      ((successive_iff_exists_openPathSlotKey hp u v).mpr ⟨i.1, i.2⟩)⟩

private theorem zeroParameterOpenCanonicalFiber_card_decompose
    {p : ℕ} (hp : 2 ≤ p) (k : Sym2 (Fin p)) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterCanonicalEdgeKey hp 1 e = k} =
      Fintype.card {z : Fin 1 //
        s(zeroParameterOpenLeftVertex hp,
          zeroParameterOpenLeftVertex hp) = k} +
      2 * Fintype.card {i : Fin (p - 1) //
        s(zeroParameterOpenPathSrc hp i,
          zeroParameterOpenPathDst hp i) = k} +
      Fintype.card {z : Fin 1 //
        s(zeroParameterOpenRightVertex hp,
          zeroParameterOpenRightVertex hp) = k} := by
  let E := zeroParameterOpenEdgeIndexEquiv hp
  rw [Fintype.card_congr
    (Equiv.subtypeEquiv E (fun _x ↦ Iff.rfl)).symm]
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  simp only [E, zeroParameterOpenEdgeKey_left]
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  simp only [zeroParameterOpenEdgeKey_right]
  let M :
      {a : Fin (p - 1) × Fin 2 //
        zeroParameterCanonicalEdgeKey hp 1
          (zeroParameterOpenEdgeIndexEquiv hp (Sum.inr (Sum.inl a))) = k} ≃
      {a : Fin (p - 1) × Fin 2 //
        s(zeroParameterOpenPathSrc hp a.1,
          zeroParameterOpenPathDst hp a.1) = k} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun a ↦ by
      rcases a with ⟨i, b⟩
      rw [zeroParameterOpenEdgeKey_middle]
      rfl)
  rw [Fintype.card_congr M]
  let P :
      {a : Fin (p - 1) × Fin 2 //
        s(zeroParameterOpenPathSrc hp a.1,
          zeroParameterOpenPathDst hp a.1) = k} ≃
      {i : Fin (p - 1) //
        s(zeroParameterOpenPathSrc hp i,
          zeroParameterOpenPathDst hp i) = k} × Fin 2 :=
    Equiv.prodSubtypeFstEquivSubtypeProd
      (α := Fin (p - 1)) (β := Fin 2)
      (p := fun i ↦ s(zeroParameterOpenPathSrc hp i,
        zeroParameterOpenPathDst hp i) = k)
  rw [Fintype.card_congr P,
    Fintype.card_prod, Fintype.card_fin]
  omega

private theorem zeroParameterOpenCanonicalFiber_card_pair
    {p : ℕ} (hp : 2 ≤ p) (u v : Fin p) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterCanonicalEdgeKey hp 1 e = s(u, v)} =
      (if s(zeroParameterOpenLeftVertex hp,
          zeroParameterOpenLeftVertex hp) = s(u, v) then 1 else 0) +
      2 * (if u.val + 1 = v.val ∨ v.val + 1 = u.val then 1 else 0) +
      (if s(zeroParameterOpenRightVertex hp,
          zeroParameterOpenRightVertex hp) = s(u, v) then 1 else 0) := by
  rw [zeroParameterOpenCanonicalFiber_card_decompose,
    zeroParameterOpenPathSlotFiber_card hp]
  by_cases hleft : s(zeroParameterOpenLeftVertex hp,
      zeroParameterOpenLeftVertex hp) = s(u, v) <;>
    by_cases hright : s(zeroParameterOpenRightVertex hp,
      zeroParameterOpenRightVertex hp) = s(u, v) <;>
    simp [hleft, hright]

private theorem equalityEdgeMultiplicity_self_local {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : Finset (Fin q)) :
    equalityEdgeMultiplicity P B B = equalityLoopsAt P B := by
  unfold equalityEdgeMultiplicity equalityLoopsAt
  congr 1
  ext e
  simp

private noncomputable instance equalitySupportGraphDecidableRel
    {p : ℕ} (Q : SelectorEqualityData p 0 0) :
    DecidableRel (equalitySupportGraph Q).Adj := Classical.decRel _

private theorem equalityEdgeMultiplicity_eq_two_iff_adj_of_internal
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (u v : EqualityVertex Q.1) (hu : IsEqualityInternal Q.1 u.1)
    (huv : u ≠ v) :
    equalityEdgeMultiplicity Q.1 u.1 v.1 =
      if (equalitySupportGraph Q).Adj u v then 2 else 0 := by
  classical
  rcases hu with
    ⟨_, C, hC, D, hD, hCD, hCu, hDu, hCm, hDm, hother⟩
  by_cases hadj : (equalitySupportGraph Q).Adj u v
  · simp only [hadj, if_true]
    by_cases hvC : v.1 = C
    · simpa [hvC] using hCm
    by_cases hvD : v.1 = D
    · simpa [hvD] using hDm
    have hvu : v.1 ≠ u.1 := fun h ↦ huv (Subtype.ext h.symm)
    have hz := hother v.1 v.2 hvu hvC hvD
    have hpos := hadj.2
    omega
  · simp only [hadj, if_false]
    have hnpos : ¬0 < equalityEdgeMultiplicity Q.1 u.1 v.1 := by
      intro hpos
      exact hadj ⟨huv, hpos⟩
    omega

private theorem equalityEdgeMultiplicity_eq_two_iff_adj_of_loop_terminal
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (u v : EqualityVertex Q.1) (hu : IsEqualityLoopTerminal Q.1 u.1)
    (huv : u ≠ v) :
    equalityEdgeMultiplicity Q.1 u.1 v.1 =
      if (equalitySupportGraph Q).Adj u v then 2 else 0 := by
  classical
  rcases hu with ⟨_, C, hC, hCu, hCm, hother⟩
  by_cases hadj : (equalitySupportGraph Q).Adj u v
  · simp only [hadj, if_true]
    by_cases hvC : v.1 = C
    · simpa [hvC] using hCm
    have hvu : v.1 ≠ u.1 := fun h ↦ huv (Subtype.ext h.symm)
    have hz := hother v.1 v.2 hvu hvC
    have hpos := hadj.2
    omega
  · simp only [hadj, if_false]
    have hnpos : ¬0 < equalityEdgeMultiplicity Q.1 u.1 v.1 := by
      intro hpos
      exact hadj ⟨huv, hpos⟩
    omega

private theorem sym2_self_ne_of_ne {alpha : Type*}
    (a u v : alpha) (huv : u ≠ v) : s(a, a) ≠ s(u, v) := by
  intro h
  rcases Sym2.eq_iff.mp h with h | h
  · exact huv (h.1.symm.trans h.2)
  · exact huv (h.2.symm.trans h.1)

private theorem sym2_self_injective {alpha : Type*} :
    Function.Injective (fun a : alpha ↦ s(a, a)) := by
  intro a b h
  rcases Sym2.eq_iff.mp h with h | h <;> exact h.1

/-- A source endpoint-key fiber is exactly the indexed multiedge fiber
between the corresponding source vertices. -/
private def zeroParameterSourceEdgeFiberEquiv
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (eV : EqualityVertex Q.1 ≃ Fin p) (u v : Fin p) :
    {e : Fin (2 * p) //
      zeroParameterSourceEdgeKey Q eV e = s(u, v)} ≃
      EqualityEdgesBetween Q (eV.symm u) (eV.symm v) where
  toFun e := ⟨e.1, by
    rcases Sym2.eq_iff.mp e.2 with h | h
    · left
      constructor
      · apply eV.injective
        simpa using h.1
      · apply eV.injective
        simpa using h.2
    · right
      constructor
      · apply eV.injective
        simpa using h.1
      · apply eV.injective
        simpa using h.2⟩
  invFun e := ⟨e.1, by
    unfold zeroParameterSourceEdgeKey
    apply Sym2.eq_iff.mpr
    rcases e.2 with h | h
    · left
      simpa [h.1, h.2]
    · right
      simpa [h.1, h.2]⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

private theorem zeroParameterSourceEdgeFiber_card
    {p : ℕ} (Q : SelectorEqualityData p 0 0)
    (eV : EqualityVertex Q.1 ≃ Fin p) (u v : Fin p) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterSourceEdgeKey Q eV e = s(u, v)} =
      equalityEdgeMultiplicity Q.1 (eV.symm u).1 (eV.symm v).1 := by
  rw [Fintype.card_congr
    (zeroParameterSourceEdgeFiberEquiv Q eV u v)]
  exact equalityEdgesBetween_card Q (eV.symm u) (eV.symm v)

private theorem zeroParameterClosedSourceFiber_card_pair
    {p : ℕ} (hp : 3 ≤ p) (Q : SelectorEqualityData p 0 0)
    (hall : ∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B)
    (O : ZeroParameterClosedVertexOrder Q) (u v : Fin p) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterSourceEdgeKey Q O.vertexAt.symm e = s(u, v)} =
      if (cycleGraph p).Adj u v then 2 else 0 := by
  rw [zeroParameterSourceEdgeFiber_card]
  simp only [Equiv.symm_symm]
  by_cases huv : u = v
  · subst v
    have hloop := (hall (O.vertexAt u).1 (O.vertexAt u).2).1
    rw [equalityEdgeMultiplicity_self_local, hloop]
    simp
  · rw [equalityEdgeMultiplicity_eq_two_iff_adj_of_internal Q
      (O.vertexAt u) (O.vertexAt v)
      (hall (O.vertexAt u).1 (O.vertexAt u).2)
      (fun h ↦ huv (O.vertexAt.injective h))]
    congr 1
    exact propext (O.adjacent_iff_cycle u v)

private theorem zeroParameterOpenSourceFiber_card_pair
    {p : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p 0 0)
    (_hopen : ZeroParameterOpenFamily Q)
    (O : ZeroParameterOpenVertexOrder Q) (u v : Fin p) :
    Fintype.card {e : Fin (2 * p) //
      zeroParameterSourceEdgeKey Q O.vertexAt.symm e = s(u, v)} =
      (if s(zeroParameterOpenLeftVertex hp,
          zeroParameterOpenLeftVertex hp) = s(u, v) then 1 else 0) +
      2 * (if u.val + 1 = v.val ∨ v.val + 1 = u.val then 1 else 0) +
      (if s(zeroParameterOpenRightVertex hp,
          zeroParameterOpenRightVertex hp) = s(u, v) then 1 else 0) := by
  rw [zeroParameterSourceEdgeFiber_card]
  simp only [Equiv.symm_symm]
  by_cases huv : u = v
  · subst v
    rw [equalityEdgeMultiplicity_self_local]
    have hsuccessive : ¬(u.val + 1 = u.val ∨ u.val + 1 = u.val) := by
      omega
    by_cases huZero : u.val = 0
    · have hui : u = zeroParameterOpenLeftVertex hp := by
        apply Fin.ext
        simpa [zeroParameterOpenLeftVertex] using huZero
      have huVertex : O.vertexAt u = O.left := by
        rw [hui]
        simpa [zeroParameterOpenLeftVertex] using O.vertexAt_zero
      have hloops : equalityLoopsAt Q.1 (O.vertexAt u).1 = 1 := by
        rw [huVertex]
        exact O.left_loop.1
      have hleft : s(zeroParameterOpenLeftVertex hp,
          zeroParameterOpenLeftVertex hp) = s(u, u) := by rw [hui]
      have hrightVertex : zeroParameterOpenRightVertex hp ≠ u := by
        intro h
        have hval := congrArg Fin.val h
        simp [zeroParameterOpenRightVertex, huZero] at hval
        omega
      have hright : s(zeroParameterOpenRightVertex hp,
          zeroParameterOpenRightVertex hp) ≠ s(u, u) := fun h ↦
        hrightVertex (sym2_self_injective h)
      simp [hloops, hleft, hright, hsuccessive]
    · by_cases huLast : u.val + 1 = p
      · have hui : u = zeroParameterOpenRightVertex hp := by
          apply Fin.ext
          simp only [zeroParameterOpenRightVertex]
          omega
        have huVertex : O.vertexAt u = O.right := by
          rw [hui]
          simpa [zeroParameterOpenRightVertex] using O.vertexAt_last
        have hloops : equalityLoopsAt Q.1 (O.vertexAt u).1 = 1 := by
          rw [huVertex]
          exact O.right_loop.1
        have hleftVertex : zeroParameterOpenLeftVertex hp ≠ u := by
          intro h
          have hval := congrArg Fin.val h
          simp [zeroParameterOpenLeftVertex] at hval
          omega
        have hleft : s(zeroParameterOpenLeftVertex hp,
            zeroParameterOpenLeftVertex hp) ≠ s(u, u) := fun h ↦
          hleftVertex (sym2_self_injective h)
        have hright : s(zeroParameterOpenRightVertex hp,
            zeroParameterOpenRightVertex hp) = s(u, u) := by rw [hui]
        simp [hloops, hleft, hright, hsuccessive]
      · have hloops : equalityLoopsAt Q.1 (O.vertexAt u).1 = 0 :=
          (O.interior u huZero huLast).1
        have hleftVertex : zeroParameterOpenLeftVertex hp ≠ u := by
          intro h
          have hval := congrArg Fin.val h
          simp [zeroParameterOpenLeftVertex] at hval
          exact huZero hval.symm
        have hrightVertex : zeroParameterOpenRightVertex hp ≠ u := by
          intro h
          have hval := congrArg Fin.val h
          simp [zeroParameterOpenRightVertex] at hval
          omega
        have hleft : s(zeroParameterOpenLeftVertex hp,
            zeroParameterOpenLeftVertex hp) ≠ s(u, u) := fun h ↦
          hleftVertex (sym2_self_injective h)
        have hright : s(zeroParameterOpenRightVertex hp,
            zeroParameterOpenRightVertex hp) ≠ s(u, u) := fun h ↦
          hrightVertex (sym2_self_injective h)
        simp [hloops, hleft, hright, hsuccessive]
  · have hleft : s(zeroParameterOpenLeftVertex hp,
        zeroParameterOpenLeftVertex hp) ≠ s(u, v) :=
      sym2_self_ne_of_ne _ _ _ huv
    have hright : s(zeroParameterOpenRightVertex hp,
        zeroParameterOpenRightVertex hp) ≠ s(u, v) :=
      sym2_self_ne_of_ne _ _ _ huv
    have hmult :
        equalityEdgeMultiplicity Q.1 (O.vertexAt u).1 (O.vertexAt v).1 =
          if (equalitySupportGraph Q).Adj (O.vertexAt u) (O.vertexAt v)
            then 2 else 0 := by
      have hvertices : O.vertexAt u ≠ O.vertexAt v :=
        fun h ↦ huv (O.vertexAt.injective h)
      by_cases huZero : u.val = 0
      · have huVertex : O.vertexAt u = O.left := by
          have hui : u = zeroParameterOpenLeftVertex hp := by
            apply Fin.ext
            simpa [zeroParameterOpenLeftVertex] using huZero
          rw [hui]
          simpa [zeroParameterOpenLeftVertex] using O.vertexAt_zero
        exact equalityEdgeMultiplicity_eq_two_iff_adj_of_loop_terminal
          Q (O.vertexAt u) (O.vertexAt v) (by simpa [huVertex] using O.left_loop)
          hvertices
      · by_cases huLast : u.val + 1 = p
        · have huVertex : O.vertexAt u = O.right := by
            have hui : u = zeroParameterOpenRightVertex hp := by
              apply Fin.ext
              simp only [zeroParameterOpenRightVertex]
              omega
            rw [hui]
            simpa [zeroParameterOpenRightVertex] using O.vertexAt_last
          exact equalityEdgeMultiplicity_eq_two_iff_adj_of_loop_terminal
            Q (O.vertexAt u) (O.vertexAt v) (by simpa [huVertex] using O.right_loop)
            hvertices
        · exact equalityEdgeMultiplicity_eq_two_iff_adj_of_internal Q
            (O.vertexAt u) (O.vertexAt v) (O.interior u huZero huLast)
            hvertices
    rw [hmult]
    by_cases hsuccessive : u.val + 1 = v.val ∨ v.val + 1 = u.val
    · have hadj : (equalitySupportGraph Q).Adj
          (O.vertexAt u) (O.vertexAt v) :=
        (O.adjacent_iff_successive u v).mpr hsuccessive
      rw [if_pos hadj]
      simp [hleft, hright, hsuccessive]
    · have hadj : ¬(equalitySupportGraph Q).Adj
          (O.vertexAt u) (O.vertexAt v) := fun h ↦
        hsuccessive ((O.adjacent_iff_successive u v).mp h)
      rw [if_neg hadj]
      simp [hleft, hright, hsuccessive]

/-- Equal fiber cardinalities for every unordered endpoint pair are exactly
what is needed to construct the indexed-edge bijection. -/
noncomputable def zeroParameterEdgeCanonicalizationOfFiberCards
    {p : ℕ} {hp : 2 ≤ p} (Q : SelectorEqualityData p 0 0)
    (tag : ZeroParameterFamilyTag) (eV : EqualityVertex Q.1 ≃ Fin p)
    (hshape :
      (tag = 0 ∧ ZeroParameterClosedFamily Q) ∨
        (tag = 1 ∧ ZeroParameterOpenFamily Q))
    (hcard : ∀ k : Sym2 (Fin p),
      Fintype.card {e : Fin (2 * p) //
        zeroParameterSourceEdgeKey Q eV e = k} =
      Fintype.card {e : Fin (2 * p) //
        zeroParameterCanonicalEdgeKey hp tag e = k}) :
    ZeroParameterEdgeCanonicalization hp Q where
  tag := tag
  vertexEquiv := eV
  edgeEquiv := zeroParameterFiberwiseEquiv
    (zeroParameterSourceEdgeKey Q eV)
    (zeroParameterCanonicalEdgeKey hp tag) hcard
  endpoints := by
    intro e
    have hkey := zeroParameterFiberwiseEquiv_key
      (zeroParameterSourceEdgeKey Q eV)
      (zeroParameterCanonicalEdgeKey hp tag) hcard e
    exact Sym2.eq_iff.mp hkey
  shape := hshape

/-- The all-internal closed member with `p ≥ 3` has exactly the endpoint-key
fibers of the fixed doubled cycle. -/
noncomputable def zeroParameterEdgeCanonicalization_closed_of_three_le
    {p : ℕ} (hp : 3 ≤ p) (Q : SelectorEqualityData p 0 0)
    (hall : ∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B)
    (O : ZeroParameterClosedVertexOrder Q) :
    ZeroParameterEdgeCanonicalization (p := p) (by omega) Q :=
  zeroParameterEdgeCanonicalizationOfFiberCards Q 0 O.vertexAt.symm
    (Or.inl ⟨rfl, Or.inl hall⟩) (fun k ↦
      Sym2.inductionOn k (fun u v ↦ by
        rw [zeroParameterClosedSourceFiber_card_pair hp Q hall O u v,
          zeroParameterClosedCanonicalFiber_card_pair hp u v]))

/-- The loop-ended doubled path has exactly the endpoint-key fibers of the
fixed open canonical model. -/
noncomputable def zeroParameterEdgeCanonicalization_open
    {p : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p 0 0)
    (hopen : ZeroParameterOpenFamily Q)
    (O : ZeroParameterOpenVertexOrder Q) :
    ZeroParameterEdgeCanonicalization hp Q :=
  zeroParameterEdgeCanonicalizationOfFiberCards Q 1 O.vertexAt.symm
    (Or.inr ⟨rfl, hopen⟩) (fun k ↦
      Sym2.inductionOn k (fun u v ↦ by
        rw [zeroParameterOpenSourceFiber_card_pair hp Q hopen O u v,
          zeroParameterOpenCanonicalFiber_card_pair hp u v]))

/-- I19's zero-parameter shape classification always supplies a source-faithful
port conjugacy with one of the two fixed canonical multigraphs. -/
theorem zeroParameterCanonicalizationExists {p : ℕ} (hp : 2 ≤ p) :
    ZeroParameterCanonicalizationExists hp := by
  classical
  intro Q
  rcases zero_parameter_two_family_classification hp Q with hclosed | hopen
  · rcases hclosed with hall | ⟨hpTwo, hfour⟩
    · have hparts : Q.1.parts.card = p := by simpa using Q.2.2.1
      have hpartsNonempty : Q.1.parts.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        rw [hempty] at hparts
        simp at hparts
        omega
      obtain ⟨B, hB⟩ := hpartsNonempty
      rcases hall B hB with
        ⟨_, C, hC, D, hD, hCD, hCB, hDB, _hCm, _hDm, _hother⟩
      have hsub : ({B, C, D} : Finset (Finset (Fin (2 * p)))) ⊆
          Q.1.parts := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hB, hC, hD⟩
      have hthree : ({B, C, D} : Finset (Finset (Fin (2 * p)))).card = 3 := by
        have hBC : B ≠ C := hCB.symm
        have hBD : B ≠ D := hDB.symm
        simp [hBC, hBD, hCD]
      have hpThree : 3 ≤ p := by
        rw [← hparts, ← hthree]
        exact Finset.card_le_card hsub
      let O := Classical.choice
        (zeroParameterClosedVertexOrder_nonempty hpThree Q hall)
      exact ⟨zeroParameterCanonicalizationOfEdge
        (zeroParameterEdgeCanonicalization_closed_of_three_le hpThree Q hall O)⟩
    · subst p
      exact ⟨zeroParameterCanonicalizationOfEdge
        (zeroParameterEdgeCanonicalization_closed_two Q hfour)⟩
  · let O := Classical.choice
      (zeroParameterOpenVertexOrder_nonempty hp Q hopen)
    exact ⟨zeroParameterCanonicalizationOfEdge
      (zeroParameterEdgeCanonicalization_open hp Q hopen O)⟩

/-- Conjugate the source cyclic transition to canonical ports. -/
def zeroParameterCanonicalTransition {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) :
    EqualityHalfEdge p → EqualityHalfEdge p := fun h ↦
  C.portEquiv (zeroParameterSourceTransition hp (C.portEquiv.symm h))

@[simp] theorem zeroParameterCanonicalTransition_involutive
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) :
    Function.Involutive (zeroParameterCanonicalTransition C) := by
  intro h
  change C.portEquiv (zeroParameterSourceTransition hp
      (C.portEquiv.symm (C.portEquiv (zeroParameterSourceTransition hp
        (C.portEquiv.symm h))))) = h
  rw [C.portEquiv.symm_apply_apply,
    zeroParameterSourceTransition_involutive,
    C.portEquiv.apply_symm_apply]

theorem zeroParameterCanonicalTransition_ne
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (h : EqualityHalfEdge p) :
    zeroParameterCanonicalTransition C h ≠ h := by
  intro hEq
  have hpre := congrArg C.portEquiv.symm hEq
  simp only [zeroParameterCanonicalTransition,
    C.portEquiv.symm_apply_apply] at hpre
  exact zeroParameterSourceTransition_ne hp (C.portEquiv.symm h) hpre

/-- The conjugated local transition preserves the canonical vertex. -/
@[simp] theorem zeroParameterCanonicalTransition_vertex
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (h : EqualityHalfEdge p) :
    zeroParameterCanonicalVertex hp C.tag
        (zeroParameterCanonicalTransition C h) =
      zeroParameterCanonicalVertex hp C.tag h := by
  simp only [zeroParameterCanonicalTransition]
  calc
    zeroParameterCanonicalVertex hp C.tag
        (C.portEquiv (zeroParameterSourceTransition hp (C.portEquiv.symm h))) =
        C.vertexEquiv (equalityHalfEdgeVertex Q
          (zeroParameterSourceTransition hp (C.portEquiv.symm h))) :=
      (C.port_vertex _).symm
    _ = C.vertexEquiv (equalityHalfEdgeVertex Q (C.portEquiv.symm h)) := by
      rw [equalityHalfEdgeVertex_zeroParameterSourceTransition]
    _ = zeroParameterCanonicalVertex hp C.tag
        (C.portEquiv (C.portEquiv.symm h)) := C.port_vertex _
    _ = zeroParameterCanonicalVertex hp C.tag h := by
      rw [C.portEquiv.apply_symm_apply]

/-- The four canonical half-edge ports incident to one ordered vertex. -/
abbrev ZeroParameterCanonicalPortsAt {p : ℕ} (hp : 2 ≤ p)
    (tag : ZeroParameterFamilyTag) (v : Fin p) :=
  {h : EqualityHalfEdge p // zeroParameterCanonicalVertex hp tag h = v}

/-- The port conjugacy restricts to each source/canonical vertex fiber. -/
def zeroParameterPortsAtEquiv {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (v : Fin p) :
    EqualityPortsAt Q (C.vertexEquiv.symm v) ≃
      ZeroParameterCanonicalPortsAt hp C.tag v where
  toFun h := ⟨C.portEquiv h.1, by
    rw [← C.port_vertex h.1, h.2]
    exact C.vertexEquiv.apply_symm_apply v⟩
  invFun h := ⟨C.portEquiv.symm h.1, by
    apply C.vertexEquiv.injective
    rw [C.vertexEquiv.apply_symm_apply, C.port_vertex]
    simpa using h.2⟩
  left_inv h := by
    apply Subtype.ext
    exact C.portEquiv.symm_apply_apply h.1
  right_inv h := by
    apply Subtype.ext
    exact C.portEquiv.apply_symm_apply h.1

theorem zeroParameterCanonicalPortsAt_card {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (v : Fin p) :
    Fintype.card (ZeroParameterCanonicalPortsAt hp C.tag v) = 4 := by
  rw [← Fintype.card_congr (zeroParameterPortsAtEquiv C v),
    equalityPortsAt_card hp Q]
  have hpart := zeroParameter_block_card hp Q
    (C.vertexEquiv.symm v).1 (C.vertexEquiv.symm v).2
  omega

/-- Restriction of the canonical transition to one four-port vertex. -/
def zeroParameterLocalTransition {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (v : Fin p) :
    FixedPointFreeInvolution (ZeroParameterCanonicalPortsAt hp C.tag v) :=
  ⟨fun h ↦ ⟨zeroParameterCanonicalTransition C h.1,
      (zeroParameterCanonicalTransition_vertex C h.1).trans h.2⟩,
    by
      constructor
      · intro h
        apply Subtype.ext
        exact zeroParameterCanonicalTransition_involutive C h.1
      · intro h hEq
        exact zeroParameterCanonicalTransition_ne C h.1
          (congrArg Subtype.val hEq)⟩

/-- Transport fixed-point-free involutions through an equivalence. -/
private def fixedPointFreeInvolutionCongrEmbedding
    {α β : Type*} (e : α ≃ β) :
    FixedPointFreeInvolution α ↪ FixedPointFreeInvolution β where
  toFun f :=
    ⟨fun y ↦ e (f.1 (e.symm y)),
      by
        constructor
        · intro y
          simp only [e.symm_apply_apply]
          rw [f.2.1]
          exact e.apply_symm_apply y
        · intro y hEq
          have hpre := congrArg e.symm hEq
          simp only [e.symm_apply_apply] at hpre
          exact f.2.2 (e.symm y) hpre⟩
  inj' := by
    intro f g hfg
    apply Subtype.ext
    funext x
    apply e.injective
    have hpoint := congrArg
      (fun z : FixedPointFreeInvolution β ↦ z.1 (e x)) hfg
    simpa using hpoint

private noncomputable def zeroParameterEmbeddingOfCardLE
    {α β : Type*} [Fintype α] [Fintype β]
    (hcard : Fintype.card α ≤ Fintype.card β) : α ↪ β where
  toFun x := (Fintype.equivFin β).symm
    (Fin.castLE hcard (Fintype.equivFin α x))
  inj' := by
    intro x y hxy
    apply (Fintype.equivFin α).injective
    apply Fin.castLE_injective hcard
    exact (Fintype.equivFin β).symm.injective hxy

private noncomputable def fixedPointFreeInvolutionFinFourCode :
    FixedPointFreeInvolution (Fin 4) ↪ Fin 3 :=
  zeroParameterEmbeddingOfCardLE fixedPointFreeInvolution_fin_four_card_le

/-- Each local transition is one of three pairings. -/
private noncomputable def zeroParameterLocalTransitionCodeEmbedding
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (v : Fin p) :
    FixedPointFreeInvolution (ZeroParameterCanonicalPortsAt hp C.tag v) ↪
      Fin 3 :=
  (fixedPointFreeInvolutionCongrEmbedding
      (Fintype.equivFinOfCardEq (zeroParameterCanonicalPortsAt_card C v))).trans
    fixedPointFreeInvolutionFinFourCode

noncomputable def zeroParameterLocalTransitionCode
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (v : Fin p) : Fin 3 :=
  zeroParameterLocalTransitionCodeEmbedding C v
    (zeroParameterLocalTransition C v)

/-- Family tag together with the started canonical directed port. -/
abbrev ZeroParameterStartedPort (p : ℕ) :=
  ZeroParameterFamilyTag × EqualityHalfEdge p

private theorem zeroParameterStartedPort_card (p : ℕ) :
    Fintype.card (ZeroParameterStartedPort p) = 8 * p := by
  simp [ZeroParameterStartedPort, EqualityHalfEdge]
  omega

noncomputable def zeroParameterStartedPortEquivFin (p : ℕ) :
    ZeroParameterStartedPort p ≃ Fin (8 * p) :=
  Fintype.equivFinOfCardEq (zeroParameterStartedPort_card p)

/-- Explicit zero-parameter Euler-transition code produced by any chosen
source-to-canonical conjugacy. -/
noncomputable def zeroParameterCodeOfCanonicalization
    {p : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p 0 0)
    (C : ZeroParameterCanonicalization hp Q) : EulerTransitionCode p 0 where
  startingDirectedEdgeAndCase :=
    zeroParameterStartedPortEquivFin p
      (C.tag, C.portEquiv (⟨0, by omega⟩, false))
  localDegreeFourTransitions := zeroParameterLocalTransitionCode C
  excessTransitions := Fin.elim0

/-- Equality of the family tag and all ternary local codes forces equality of
the transported global transition. -/
private theorem zeroParameterCanonicalTransition_eq_of_local_codes
    {p : ℕ} {hp : 2 ≤ p}
    {Q R : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q)
    (D : ZeroParameterCanonicalization hp R)
    (htag : C.tag = D.tag)
    (hlocal : ∀ v,
      zeroParameterLocalTransitionCode C v =
        zeroParameterLocalTransitionCode D v) :
    zeroParameterCanonicalTransition C =
      zeroParameterCanonicalTransition D := by
  rcases C with ⟨ctag, cport, cvertex, cportv, copp, cshape⟩
  rcases D with ⟨dtag, dport, dvertex, dportv, dopp, dshape⟩
  dsimp only at htag
  subst dtag
  funext h
  let C : ZeroParameterCanonicalization hp Q :=
    ⟨ctag, cport, cvertex, cportv, copp, cshape⟩
  let D : ZeroParameterCanonicalization hp R :=
    ⟨ctag, dport, dvertex, dportv, dopp, dshape⟩
  change ∀ v, zeroParameterLocalTransitionCode C v =
      zeroParameterLocalTransitionCode D v at hlocal
  change zeroParameterCanonicalTransition C h =
      zeroParameterCanonicalTransition D h
  let v := zeroParameterCanonicalVertex hp ctag h
  have hhC : zeroParameterCanonicalVertex hp ctag h = v := rfl
  have hhD : zeroParameterCanonicalVertex hp ctag h = v := rfl
  let xC : ZeroParameterCanonicalPortsAt hp ctag v := ⟨h, hhC⟩
  let xD : ZeroParameterCanonicalPortsAt hp ctag v := ⟨h, hhD⟩
  have hcode := hlocal v
  have hemb : zeroParameterLocalTransitionCodeEmbedding C v =
      zeroParameterLocalTransitionCodeEmbedding D v := by
    unfold zeroParameterLocalTransitionCodeEmbedding
    congr
  have hfpf : zeroParameterLocalTransition C v =
      zeroParameterLocalTransition D v := by
    rw [zeroParameterLocalTransitionCode, hemb] at hcode
    exact (zeroParameterLocalTransitionCodeEmbedding D v).injective hcode
  have hx : xC = xD := by
    apply Subtype.ext
    rfl
  have hpoint := congrArg
    (fun f : FixedPointFreeInvolution
        (ZeroParameterCanonicalPortsAt hp ctag v) ↦ f.1 xC)
    hfpf
  change zeroParameterCanonicalTransition C h =
    zeroParameterCanonicalTransition D h
  simpa only [zeroParameterLocalTransition, xC, xD, hx] using
    congrArg Subtype.val hpoint

/-- Started source tails transported to the common canonical port model. -/
def zeroParameterCanonicalTail {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (i : Fin (2 * p)) :
    EqualityHalfEdge p := C.portEquiv (i, false)

/-- Canonical edge reversal followed by the transported local transition
advances the original cyclic occurrence index. -/
theorem zeroParameterCanonicalTail_next {p : ℕ} {hp : 2 ≤ p}
    {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (i : Fin (2 * p)) :
    zeroParameterCanonicalTail C (cyclicSucc i) =
      zeroParameterCanonicalTransition C
        (zeroParameterSourceOpposite (zeroParameterCanonicalTail C i)) := by
  rw [zeroParameterCanonicalTail, zeroParameterCanonicalTail,
    ← C.opposite (i, false)]
  simp only [zeroParameterCanonicalTransition, C.portEquiv.symm_apply_apply]
  rw [zeroParameterSourceTransition_opposite]

/-- Equality of source blocks is exactly equality of the canonical vertices
visited by the transported tails. -/
theorem zeroParameterCanonicalTail_class_iff
    {p : ℕ} {hp : 2 ≤ p} {Q : SelectorEqualityData p 0 0}
    (C : ZeroParameterCanonicalization hp Q) (i j : Fin (2 * p)) :
    Q.1.part i = Q.1.part j ↔
      zeroParameterCanonicalVertex hp C.tag
          (zeroParameterCanonicalTail C i) =
        zeroParameterCanonicalVertex hp C.tag
          (zeroParameterCanonicalTail C j) := by
  have hi : equalityHalfEdgeVertex Q (i, false) = equalityVertexAt Q.1 i := rfl
  have hj : equalityHalfEdgeVertex Q (j, false) = equalityVertexAt Q.1 j := rfl
  constructor
  · intro hij
    have hv : equalityHalfEdgeVertex Q (i, false) =
        equalityHalfEdgeVertex Q (j, false) := by
      rw [hi, hj]
      exact Subtype.ext hij
    calc
      zeroParameterCanonicalVertex hp C.tag
          (zeroParameterCanonicalTail C i) =
          C.vertexEquiv (equalityHalfEdgeVertex Q (i, false)) :=
        (C.port_vertex _).symm
      _ = C.vertexEquiv (equalityHalfEdgeVertex Q (j, false)) :=
        congrArg C.vertexEquiv hv
      _ = zeroParameterCanonicalVertex hp C.tag
          (zeroParameterCanonicalTail C j) := C.port_vertex _
  · intro hcanon
    have hvmap : C.vertexEquiv (equalityHalfEdgeVertex Q (i, false)) =
        C.vertexEquiv (equalityHalfEdgeVertex Q (j, false)) := by
      rw [C.port_vertex, C.port_vertex]
      exact hcanon
    have hv := C.vertexEquiv.injective hvmap
    exact congrArg Subtype.val hv

/-- Once a port conjugacy has been selected for every source object, the
resulting map to the advertised Euler-transition code is injective.  The proof
uses only the started port, the `p` ternary local transitions, and the generic
cyclic-dynamics reconstruction theorem. -/
theorem zeroParameterCodeOfCanonicalization_injective
    {p : ℕ} (hp : 2 ≤ p)
    (chooseC : (Q : SelectorEqualityData p 0 0) →
      ZeroParameterCanonicalization hp Q) :
    Function.Injective
      (fun Q ↦ zeroParameterCodeOfCanonicalization hp Q (chooseC Q)) := by
  intro Q R hcode
  let C := chooseC Q
  let D := chooseC R
  have hstartedCode := congrArg
    EulerTransitionCode.startingDirectedEdgeAndCase hcode
  have hstarted :
      (C.tag, zeroParameterCanonicalTail C ⟨0, by omega⟩) =
        (D.tag, zeroParameterCanonicalTail D ⟨0, by omega⟩) := by
    exact (zeroParameterStartedPortEquivFin p).injective hstartedCode
  have htag : C.tag = D.tag := congrArg Prod.fst hstarted
  have hstart : zeroParameterCanonicalTail C ⟨0, by omega⟩ =
      zeroParameterCanonicalTail D ⟨0, by omega⟩ :=
    congrArg Prod.snd hstarted
  have hlocalFun := congrArg EulerTransitionCode.localDegreeFourTransitions hcode
  have hlocal : ∀ v,
      zeroParameterLocalTransitionCode C v =
        zeroParameterLocalTransitionCode D v := fun v ↦ congrFun hlocalFun v
  have htransition : zeroParameterCanonicalTransition C =
      zeroParameterCanonicalTransition D :=
    zeroParameterCanonicalTransition_eq_of_local_codes C D htag hlocal
  have hP : Q.1 = R.1 :=
    finpartition_eq_of_started_cyclic_dynamics_of_pos (by omega)
      Q.1 R.1
      (zeroParameterCanonicalTail C)
      (zeroParameterCanonicalTail D)
      (zeroParameterCanonicalVertex hp C.tag)
      (fun h ↦ zeroParameterCanonicalTransition C
        (zeroParameterSourceOpposite h))
      hstart
      (fun i ↦ zeroParameterCanonicalTail_next C i)
      (fun i ↦ by
        rw [zeroParameterCanonicalTail_next D, htransition])
      (zeroParameterCanonicalTail_class_iff C)
      (fun i j ↦ by
        rw [zeroParameterCanonicalTail_class_iff D, htag])
  exact Subtype.ext hP

/-- The explicit injection, conditional only on the exact port-conjugacy
existence obligation isolated above. -/
noncomputable def zeroParameterInjectionOfCanonicalization
    {p : ℕ} (hp : 2 ≤ p)
    (hexists : ZeroParameterCanonicalizationExists hp) :
    SelectorEqualityData p 0 0 ↪ EulerTransitionCode p 0 where
  toFun Q := zeroParameterCodeOfCanonicalization hp Q
    (Classical.choice (hexists Q))
  inj' := zeroParameterCodeOfCanonicalization_injective hp
    (fun Q ↦ Classical.choice (hexists Q))

/-- Unconditional source-faithful encoding of every zero-parameter selector
equality object by its family tag, started directed port, and `p` local
degree-four transition choices. -/
noncomputable def zeroParameterInjection {p : ℕ} (hp : 2 ≤ p) :
    SelectorEqualityData p 0 0 ↪ EulerTransitionCode p 0 :=
  zeroParameterInjectionOfCanonicalization hp
    (zeroParameterCanonicalizationExists hp)

end

end Problem56
