import Problem56.ContractedCoreComponents
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Boundary-oriented order on a removed component

Every removed component is a finite tree of degree at most two, and its two
retained boundary incidences orient its unique spanning path.  This module
makes that order explicit.  The degenerate one-vertex component is included:
its two boundary incidences have the same removed endpoint and its spanning
walk is nil.
-/

namespace Problem56

open SimpleGraph

noncomputable section

private theorem card_pair_le_degree_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hy : G.Adj x y) (hz : G.Adj x z) (hyz : y ≠ z) :
    2 ≤ G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  have hsub : {y, z} ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.mem_neighborFinset x _).mpr hy
    · exact (G.mem_neighborFinset x _).mpr hz
  have hcard := Finset.card_le_card hsub
  simpa [hyz] using hcard

private theorem card_triple_le_degree_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z w : V} (hy : G.Adj x y) (hz : G.Adj x z)
    (hw : G.Adj x w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    3 ≤ G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  have hsub : {y, z, w} ⊆ G.neighborFinset x := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact (G.mem_neighborFinset x _).mpr hy
    · exact (G.mem_neighborFinset x _).mpr hz
    · exact (G.mem_neighborFinset x _).mpr hw
  have hcard := Finset.card_le_card hsub
  simpa [hyz, hyw, hzw] using hcard

private theorem walk_exists_adj_mem_not_mem
    {V : Type*} {G : SimpleGraph V} {S : Set V}
    {u v : V} (q : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  induction q with
  | nil => exact (hv hu).elim
  | @cons a b c hab q ih =>
      by_cases hb : b ∈ S
      · exact ih hb hv
      · exact ⟨a, b, hu, hb, hab⟩

/-- In a finite tree of maximum degree two, the path between two distinct
vertices of degree at most one visits every vertex. -/
theorem walk_isHamiltonian_of_isTree_of_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hT : G.IsTree) (huv : u ≠ v)
    (hu : G.degree u ≤ 1) (hv : G.degree v ≤ 1)
    (hdeg : ∀ x, G.degree x ≤ 2) :
    p.IsHamiltonian := by
  apply hp.isHamiltonian_of_mem
  intro z
  by_contra hz
  let q := (hT.connected u z).some
  have hcross : ∃ x y, x ∈ p.support ∧ y ∉ p.support ∧ G.Adj x y :=
    walk_exists_adj_mem_not_mem q p.start_mem_support hz
  obtain ⟨x, y, hx, hy, hxy⟩ := hcross
  obtain ⟨q₀, q₁, hq₀, hq₁, hpappend⟩ :=
    hp.mem_support_iff_exists_append.mp hx
  have happPath : (q₀.append q₁).IsPath := hpappend ▸ hp
  by_cases hq₀nil : q₀.Nil
  · have hxu : x = u := hq₀nil.eq.symm
    subst x
    have hq₁notnil : ¬ q₁.Nil := by
      intro hnil
      have hxv : u = v := hnil.eq
      exact huv hxv
    have hadj : G.Adj u q₁.snd := q₁.adj_snd hq₁notnil
    have hne : q₁.snd ≠ y := by
      intro heq
      apply hy
      rw [← heq, hpappend]
      exact (Walk.mem_support_append_iff q₀ q₁).mpr
        (Or.inr (List.mem_of_mem_tail (q₁.snd_mem_tail_support hq₁notnil)))
    have := card_pair_le_degree_of_adj G hadj hxy hne
    omega
  · by_cases hq₁nil : q₁.Nil
    · have hxv : x = v := hq₁nil.eq
      subst x
      have hadj : G.Adj v q₀.penultimate := (q₀.adj_penultimate hq₀nil).symm
      have hne : q₀.penultimate ≠ y := by
        intro heq
        apply hy
        rw [← heq, hpappend]
        exact (Walk.mem_support_append_iff q₀ q₁).mpr
          (Or.inl (q₀.penultimate_mem_dropLast_support hq₀nil |>
            List.mem_of_mem_dropLast))
      have := card_pair_le_degree_of_adj G hadj hxy hne
      omega
    · have hleft : G.Adj x q₀.penultimate :=
        (q₀.adj_penultimate hq₀nil).symm
      have hright : G.Adj x q₁.snd := q₁.adj_snd hq₁nil
      have hlr : q₀.penultimate ≠ q₁.snd := by
        apply happPath.ne_of_mem_support_of_append
          (y := q₁.snd) (q₁.adj_snd hq₁nil).ne'
        · exact q₀.penultimate_mem_dropLast_support hq₀nil |>
            List.mem_of_mem_dropLast
        · exact List.mem_of_mem_tail (q₁.snd_mem_tail_support hq₁nil)
      have hly : q₀.penultimate ≠ y := by
        intro heq
        apply hy
        rw [← heq, hpappend]
        exact (Walk.mem_support_append_iff q₀ q₁).mpr
          (Or.inl (q₀.penultimate_mem_dropLast_support hq₀nil |>
            List.mem_of_mem_dropLast))
      have hry : q₁.snd ≠ y := by
        intro heq
        apply hy
        rw [← heq, hpappend]
        exact (Walk.mem_support_append_iff q₀ q₁).mpr
          (Or.inr (List.mem_of_mem_tail (q₁.snd_mem_tail_support hq₁nil)))
      have := card_triple_le_degree_of_adj G hleft hright hxy hlr hly hry
      have := hdeg x
      omega

/-- A Hamiltonian path in a finite tree uses every graph edge. -/
theorem walk_edges_toFinset_eq_edgeFinset_of_isHamiltonian_isTree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hham : p.IsHamiltonian) (hT : G.IsTree) :
    p.edges.toFinset = G.edgeFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [List.mem_toFinset] at he
    exact G.mem_edgeFinset.mpr (p.edges_subset_edgeSet he)
  · have hpCard : p.edges.toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
        p.length_edges]
    have htreeCard := hT.card_edgeFinset
    have hlength := hham.length_eq
    omega

/-- Natural-index form of the path-graph adjacency law. -/
theorem walk_adj_getVert_iff_of_isHamiltonian_isTree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hham : p.IsHamiltonian) (hT : G.IsTree)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔
      i + 1 = j ∨ j + 1 = i := by
  have hget_inj {a b : ℕ} (ha : a ≤ p.length) (hb : b ≤ p.length)
      (hab : p.getVert a = p.getVert b) : a = b := by
    have ha' : a < p.support.length := by rw [p.length_support]; omega
    have hb' : b < p.support.length := by rw [p.length_support]; omega
    have hsupport : p.support[a] = p.support[b] := by
      rw [← p.getVert_eq_support_getElem ha,
        ← p.getVert_eq_support_getElem hb]
      exact hab
    exact hp.support_nodup.getElem_inj_iff.mp hsupport
  constructor
  · intro hadj
    have hedgeFin : s(p.getVert i, p.getVert j) ∈ G.edgeFinset :=
      G.mem_edgeFinset.mpr hadj
    have hedge : s(p.getVert i, p.getVert j) ∈ p.edges := by
      rw [← List.mem_toFinset,
        walk_edges_toFinset_eq_edgeFinset_of_isHamiltonian_isTree hp hham hT]
      exact hedgeFin
    obtain ⟨k, hk, heq⟩ := (p.mk_mem_edges_iff_exists).mp hedge
    rcases Sym2.eq_iff.mp heq with ⟨hki, hksj⟩ | ⟨hkj, hksi⟩
    · left
      have hki' : k = i := hget_inj (Nat.le_of_lt hk) hi hki
      have hksj' : k + 1 = j := hget_inj (Nat.succ_le_iff.mpr hk) hj hksj
      omega
    · right
      have hkj' : k = j := hget_inj (Nat.le_of_lt hk) hj hkj
      have hksi' : k + 1 = i := hget_inj (Nat.succ_le_iff.mpr hk) hi hksi
      omega
  · rintro (hij | hji)
    · subst j
      exact p.adj_getVert_succ (by omega)
    · subst i
      exact (p.adj_getVert_succ (by omega)).symm

/-- The same incidence enumeration used by the endpoint coordinate of
`equalityComponentBoundaryPortsEquivFinPairs`. -/
noncomputable def equalityComponentBoundaryIncidenceEquivFinTwo
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    EqualityComponentBoundaryIncidence Q c ≃ Fin 2 :=
  Fintype.equivFinOfCardEq
    (equalityComponentBoundaryIncidence_card hp Q ha c)

/-- The boundary incidence with the indicated oriented endpoint number. -/
noncomputable def equalityComponentBoundaryIncidenceAt
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) (i : Fin 2) :
    EqualityComponentBoundaryIncidence Q c :=
  (equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha c).symm i

/-- Removed endpoint of one of the two oriented boundary incidences. -/
noncomputable def equalityRemovedComponentBoundaryVertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) (i : Fin 2) : c :=
  (equalityComponentBoundaryIncidenceAt hp Q ha c i).1

@[simp] theorem equalityComponentBoundaryIncidenceEquivFinTwo_apply_at
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) (i : Fin 2) :
    equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha c
        (equalityComponentBoundaryIncidenceAt hp Q ha c i) = i := by
  exact Equiv.apply_symm_apply _ i

/-- The endpoint coordinate of the existing `(endpoint, copy)` boundary-port
enumeration is exactly the incidence orientation fixed above. -/
@[simp] theorem equalityComponentBoundaryPortsEquivFinPairs_fst
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (z : EqualityComponentBoundaryPorts Q c) :
    (equalityComponentBoundaryPortsEquivFinPairs hp Q ha c z).1 =
      equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha c z.1 := by
  rfl

/-- Conversely, endpoint `i` in the existing boundary-port enumeration uses
the selected incidence `i`. -/
@[simp] theorem equalityComponentBoundaryPortsEquivFinPairs_symm_fst
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (i j : Fin 2) :
    ((equalityComponentBoundaryPortsEquivFinPairs hp Q ha c).symm (i, j)).1 =
      equalityComponentBoundaryIncidenceAt hp Q ha c i := by
  apply (equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha c).injective
  rw [← equalityComponentBoundaryPortsEquivFinPairs_fst hp Q ha c
    ((equalityComponentBoundaryPortsEquivFinPairs hp Q ha c).symm (i, j))]
  calc
    ((equalityComponentBoundaryPortsEquivFinPairs hp Q ha c)
        ((equalityComponentBoundaryPortsEquivFinPairs hp Q ha c).symm (i, j))).1 =
        i := congrArg Prod.fst
          ((equalityComponentBoundaryPortsEquivFinPairs hp Q ha c).apply_symm_apply (i, j))
    _ = equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha c
          (equalityComponentBoundaryIncidenceAt hp Q ha c i) :=
      (equalityComponentBoundaryIncidenceEquivFinTwo_apply_at hp Q ha c i).symm

/-- A boundary endpoint has component degree at most one. -/
theorem equalityRemovedComponentBoundaryVertex_degree_le_one
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) (i : Fin 2) :
    c.toSimpleGraph.degree
        (equalityRemovedComponentBoundaryVertex hp Q ha c i) ≤ 1 := by
  let b := equalityComponentBoundaryIncidenceAt hp Q ha c i
  have hpoint := equality_removed_degree_add_retainedNeighbor_card hp Q b.1.1
  have hdeg : c.toSimpleGraph.degree b.1 =
      (equalityRemovedGraph Q).degree b.1.1 :=
    equalityComponent_degree_eq_removedDegree Q c b.1
  have hpos : 0 < (equalityRetainedNeighborFinset Q b.1.1).card :=
    Finset.card_pos.mpr ⟨b.2.1, b.2.2⟩
  change c.toSimpleGraph.degree b.1 ≤ 1
  omega

/-- The unique path from boundary incidence zero to boundary incidence one. -/
noncomputable def equalityRemovedComponentBoundaryWalk
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    c.toSimpleGraph.Walk
      (equalityRemovedComponentBoundaryVertex hp Q ha c 0)
      (equalityRemovedComponentBoundaryVertex hp Q ha c 1) :=
  ((equalityRemovedComponent_isTree hp Q ha c).existsUnique_path
    (equalityRemovedComponentBoundaryVertex hp Q ha c 0)
    (equalityRemovedComponentBoundaryVertex hp Q ha c 1)).exists.choose

/-- The boundary walk is simple. -/
theorem equalityRemovedComponentBoundaryWalk_isPath
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    (equalityRemovedComponentBoundaryWalk hp Q ha c).IsPath := by
  exact (((equalityRemovedComponent_isTree hp Q ha c).existsUnique_path
    (equalityRemovedComponentBoundaryVertex hp Q ha c 0)
    (equalityRemovedComponentBoundaryVertex hp Q ha c 1)).exists.choose_spec)

private theorem equalityRemovedComponent_subsingleton_of_boundaryVertex_eq
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (hends : equalityRemovedComponentBoundaryVertex hp Q ha c 0 =
      equalityRemovedComponentBoundaryVertex hp Q ha c 1) :
    Subsingleton c := by
  let b₀ := equalityComponentBoundaryIncidenceAt hp Q ha c 0
  let b₁ := equalityComponentBoundaryIncidenceAt hp Q ha c 1
  have hbne : b₀ ≠ b₁ := by
    intro h
    have hi : (0 : Fin 2) = 1 := by
      rw [← equalityComponentBoundaryIncidenceEquivFinTwo_apply_at hp Q ha c 0,
        ← equalityComponentBoundaryIncidenceEquivFinTwo_apply_at hp Q ha c 1]
      exact congrArg (equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha c) h
    exact Fin.zero_ne_one hi
  have hw : b₀.1 = b₁.1 := hends
  have hrne : b₀.2.1 ≠ b₁.2.1 := by
    intro hr
    apply hbne
    apply Sigma.ext hw
    apply (Subtype.heq_iff_coe_eq (fun r ↦ by rw [hw])).2
    exact hr
  have hsub : {b₀.2.1, b₁.2.1} ⊆
      equalityRetainedNeighborFinset Q b₀.1.1 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact b₀.2.2
    · simpa only [hw] using b₁.2.2
  have hcard : 2 ≤ (equalityRetainedNeighborFinset Q b₀.1.1).card := by
    have := Finset.card_le_card hsub
    simpa [hrne] using this
  have hpoint := equality_removed_degree_add_retainedNeighbor_card hp Q b₀.1.1
  have hdegRemoved : (equalityRemovedGraph Q).degree b₀.1.1 = 0 := by
    omega
  have hdeg : c.toSimpleGraph.degree b₀.1 = 0 := by
    rw [equalityComponent_degree_eq_removedDegree Q c b₀.1]
    exact hdegRemoved
  rw [← not_nontrivial_iff_subsingleton]
  intro hnontrivial
  letI : Nontrivial c := hnontrivial
  have hmem : b₀.1 ∈ c.toSimpleGraph.support := by
    rw [(equalityRemovedComponent_isTree hp Q ha c).connected.preconnected.support_eq_univ]
    exact Set.mem_univ _
  exact ((c.toSimpleGraph.degree_eq_zero_iff_notMem_support b₀.1).mp hdeg) hmem

/-- The oriented boundary path covers the entire component, including the
one-vertex case where its endpoints coincide. -/
theorem equalityRemovedComponentBoundaryWalk_isHamiltonian
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    (equalityRemovedComponentBoundaryWalk hp Q ha c).IsHamiltonian := by
  by_cases hends : equalityRemovedComponentBoundaryVertex hp Q ha c 0 =
      equalityRemovedComponentBoundaryVertex hp Q ha c 1
  · letI : Subsingleton c :=
      equalityRemovedComponent_subsingleton_of_boundaryVertex_eq hp Q ha c hends
    exact Walk.IsHamiltonian.of_subsingleton
  · exact walk_isHamiltonian_of_isTree_of_degree_le_two
        (equalityRemovedComponentBoundaryWalk_isPath hp Q ha c)
        (equalityRemovedComponent_isTree hp Q ha c) hends
        (equalityRemovedComponentBoundaryVertex_degree_le_one hp Q ha c 0)
        (equalityRemovedComponentBoundaryVertex_degree_le_one hp Q ha c 1)
        (equalityRemovedComponent_degree_le_two hp Q c)

/-- Set-valued form of the spanning property. -/
theorem equalityRemovedComponentBoundaryWalk_support_eq_univ
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    {v | v ∈ (equalityRemovedComponentBoundaryWalk hp Q ha c).support} =
      Set.univ :=
  (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).setOfPred_support

/-- Canonical boundary-oriented enumeration of component vertices. -/
noncomputable def equalityRemovedComponentFinEquiv
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fin (Fintype.card c) ≃ c :=
  (finCongr
    (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).length_support.symm).trans
      (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).supportGetEquiv

/-- A removed component always has a first vertex. -/
theorem equalityRemovedComponent_card_pos
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    0 < Fintype.card c := by
  apply Fintype.card_pos_iff.mpr
  obtain ⟨w, hw⟩ := c.nonempty_supp
  exact ⟨⟨w, hw⟩⟩

/-- First canonical position of a removed component. -/
noncomputable def equalityRemovedComponentFirstIndex
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fin (Fintype.card c) :=
  ⟨0, equalityRemovedComponent_card_pos Q c⟩

/-- Last canonical position of a removed component. -/
noncomputable def equalityRemovedComponentLastIndex
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fin (Fintype.card c) :=
  ⟨Fintype.card c - 1, by
    have := equalityRemovedComponent_card_pos Q c
    omega⟩

@[simp] theorem equalityRemovedComponentFirstIndex_val
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    (equalityRemovedComponentFirstIndex Q c).1 = 0 := rfl

@[simp] theorem equalityRemovedComponentLastIndex_val
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    (equalityRemovedComponentLastIndex Q c).1 = Fintype.card c - 1 := rfl

/-- The component equivalence is literally the boundary walk's vertex at the
same numerical position. -/
theorem equalityRemovedComponentFinEquiv_apply_eq_getVert
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (i : Fin (Fintype.card c)) :
    equalityRemovedComponentFinEquiv hp Q ha c i =
      (equalityRemovedComponentBoundaryWalk hp Q ha c).getVert i.1 := by
  unfold equalityRemovedComponentFinEquiv
  simp only [Equiv.trans_apply, finCongr_apply,
    Walk.IsHamiltonian.supportGetEquiv_apply]
  have hlength :=
    (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).length_support
  rw [(equalityRemovedComponentBoundaryWalk hp Q ha c).length_support] at hlength
  have hi : i.1 ≤ (equalityRemovedComponentBoundaryWalk hp Q ha c).length := by
    omega
  have hisupp : i.1 <
      (equalityRemovedComponentBoundaryWalk hp Q ha c).support.length := by
    rw [(equalityRemovedComponentBoundaryWalk hp Q ha c).length_support]
    omega
  change (equalityRemovedComponentBoundaryWalk hp Q ha c).support[i.1]'hisupp =
    (equalityRemovedComponentBoundaryWalk hp Q ha c).getVert i.1
  exact (equalityRemovedComponentBoundaryWalk hp Q ha c).getVert_eq_support_getElem hi |>
    Eq.symm

/-- Boundary incidence zero is path position zero. -/
theorem equalityRemovedComponentFinEquiv_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (hc : 0 < Fintype.card c) :
    equalityRemovedComponentFinEquiv hp Q ha c ⟨0, hc⟩ =
      equalityRemovedComponentBoundaryVertex hp Q ha c 0 := by
  rw [equalityRemovedComponentFinEquiv_apply_eq_getVert]
  exact (equalityRemovedComponentBoundaryWalk hp Q ha c).getVert_zero

/-- Boundary incidence one is the last path position. -/
theorem equalityRemovedComponentFinEquiv_last
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (hc : 0 < Fintype.card c) :
    equalityRemovedComponentFinEquiv hp Q ha c
        ⟨Fintype.card c - 1, by omega⟩ =
      equalityRemovedComponentBoundaryVertex hp Q ha c 1 := by
  rw [equalityRemovedComponentFinEquiv_apply_eq_getVert]
  have hlength :
      (equalityRemovedComponentBoundaryWalk hp Q ha c).length =
        Fintype.card c - 1 :=
    (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).length_eq
  simpa only [hlength] using
    (equalityRemovedComponentBoundaryWalk hp Q ha c).getVert_length

/-- Argument-free first-endpoint law using the canonical first index. -/
@[simp] theorem equalityRemovedComponentFinEquiv_firstIndex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    equalityRemovedComponentFinEquiv hp Q ha c
        (equalityRemovedComponentFirstIndex Q c) =
      equalityRemovedComponentBoundaryVertex hp Q ha c 0 := by
  exact equalityRemovedComponentFinEquiv_zero hp Q ha c
    (equalityRemovedComponent_card_pos Q c)

/-- Argument-free last-endpoint law using the canonical last index. -/
@[simp] theorem equalityRemovedComponentFinEquiv_lastIndex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    equalityRemovedComponentFinEquiv hp Q ha c
        (equalityRemovedComponentLastIndex Q c) =
      equalityRemovedComponentBoundaryVertex hp Q ha c 1 := by
  exact equalityRemovedComponentFinEquiv_last hp Q ha c
    (equalityRemovedComponent_card_pos Q c)

/-- Exact path-graph adjacency law in the canonical component coordinates. -/
theorem equalityRemovedComponentFinEquiv_adj_iff
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (i j : Fin (Fintype.card c)) :
    c.toSimpleGraph.Adj
        (equalityRemovedComponentFinEquiv hp Q ha c i)
        (equalityRemovedComponentFinEquiv hp Q ha c j) ↔
      i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
  rw [equalityRemovedComponentFinEquiv_apply_eq_getVert,
    equalityRemovedComponentFinEquiv_apply_eq_getVert]
  apply walk_adj_getVert_iff_of_isHamiltonian_isTree
    (equalityRemovedComponentBoundaryWalk_isPath hp Q ha c)
    (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c)
    (equalityRemovedComponent_isTree hp Q ha c)
  · have hlength :=
      (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).length_support
    rw [(equalityRemovedComponentBoundaryWalk hp Q ha c).length_support] at hlength
    omega
  · have hlength :=
      (equalityRemovedComponentBoundaryWalk_isHamiltonian hp Q ha c).length_support
    rw [(equalityRemovedComponentBoundaryWalk hp Q ha c).length_support] at hlength
    omega

/-- Consecutive canonical positions are adjacent. -/
theorem equalityRemovedComponentFinEquiv_adj_succ
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (i : Fin (Fintype.card c)) (hi : i.1 + 1 < Fintype.card c) :
    c.toSimpleGraph.Adj
        (equalityRemovedComponentFinEquiv hp Q ha c i)
        (equalityRemovedComponentFinEquiv hp Q ha c ⟨i.1 + 1, hi⟩) := by
  exact (equalityRemovedComponentFinEquiv_adj_iff hp Q ha c i
    ⟨i.1 + 1, hi⟩).mpr (Or.inl rfl)

/-- Consecutive path vertices are joined by an exact doubled source edge. -/
theorem equalityRemovedComponentFinEquiv_doubled_succ
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (i : Fin (Fintype.card c)) (hi : i.1 + 1 < Fintype.card c) :
    EqualityDoubledAdjacent Q
      (equalityRemovedComponentFinEquiv hp Q ha c i).1.1
      (equalityRemovedComponentFinEquiv hp Q ha c ⟨i.1 + 1, hi⟩).1.1 := by
  apply equalityRemovedGraph_adj_doubled hp Q
  exact equalityRemovedComponentFinEquiv_adj_succ hp Q ha c i hi

/-- The indexed edge fiber between consecutive path vertices has two copies. -/
theorem equalityRemovedComponentFinEquiv_edge_card_succ
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (i : Fin (Fintype.card c)) (hi : i.1 + 1 < Fintype.card c) :
    Fintype.card (EqualityEdgesBetween Q
      (equalityRemovedComponentFinEquiv hp Q ha c i).1.1
      (equalityRemovedComponentFinEquiv hp Q ha c ⟨i.1 + 1, hi⟩).1.1) = 2 := by
  rw [equalityEdgesBetween_card]
  exact (equalityRemovedComponentFinEquiv_doubled_succ hp Q ha c i hi).2

#print axioms walk_isHamiltonian_of_isTree_of_degree_le_two
#print axioms equalityComponentBoundaryIncidenceEquivFinTwo
#print axioms equalityRemovedComponentBoundaryVertex_degree_le_one
#print axioms equalityRemovedComponentBoundaryWalk_isPath
#print axioms equalityRemovedComponentBoundaryWalk_isHamiltonian
#print axioms equalityRemovedComponentBoundaryWalk_support_eq_univ
#print axioms equalityRemovedComponentFinEquiv
#print axioms equalityRemovedComponent_card_pos
#print axioms equalityRemovedComponentFinEquiv_zero
#print axioms equalityRemovedComponentFinEquiv_last
#print axioms equalityRemovedComponentFinEquiv_adj_iff
#print axioms equalityRemovedComponentFinEquiv_doubled_succ
#print axioms equalityRemovedComponentFinEquiv_edge_card_succ

end

end Problem56
