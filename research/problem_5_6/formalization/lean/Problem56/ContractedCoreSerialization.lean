import Problem56.ContractedCoreComponents

/-!
# Reversible retained-port serialization for the contracted core

This file starts the actual encoder/decoder layer for I20.  It identifies the
precise complement of the direct retained edges: the global component
boundary-port type is not merely injected into retained ports, but covers
exactly those retained ports whose opposite endpoint was removed.
-/

namespace Problem56

open SimpleGraph

/-- The other endpoint-side of the same indexed edge occurrence. -/
def equalityOppositeHalfEdge {p : ℕ} :
    EqualityHalfEdge p → EqualityHalfEdge p
  | (e, b) => (e, !b)

@[simp] theorem equalityOppositeHalfEdge_involutive {p : ℕ}
    (h : EqualityHalfEdge p) :
    equalityOppositeHalfEdge (equalityOppositeHalfEdge h) = h := by
  rcases h with ⟨e, b⟩
  cases b <;> rfl

theorem equalityOppositeHalfEdge_ne {p : ℕ}
    (h : EqualityHalfEdge p) : equalityOppositeHalfEdge h ≠ h := by
  rcases h with ⟨e, b⟩
  cases b <;> simp [equalityOppositeHalfEdge]

/-- For an edge between distinct vertices, the opposite of its port at the
first vertex is incident to the second vertex. -/
theorem equalityHalfEdgeVertex_opposite_portAtFirst
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (u v : EqualityVertex Q.1) (huv : u ≠ v)
    (e : EqualityEdgesBetween Q u v) :
    equalityHalfEdgeVertex Q
        (equalityOppositeHalfEdge (equalityPortAtFirst Q u v e).1) = v := by
  classical
  unfold equalityPortAtFirst
  split
  next hs =>
    simp only [equalityOppositeHalfEdge, equalityHalfEdgeVertex]
    rcases e.2 with he | he
    · exact he.2
    · exact (huv (hs.symm.trans he.1)).elim
  next hs =>
    simp only [equalityOppositeHalfEdge, equalityHalfEdgeVertex]
    rcases e.2 with he | he
    · exact (hs he.1).elim
    · exact he.1

/-- Retained ports whose opposite endpoint is retained are the direct-edge
ports of the contracted graph. -/
abbrev EqualityDirectRetainedPort {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :=
  {z : EqualityRetainedPorts Q //
    equalityHalfEdgeVertex Q (equalityOppositeHalfEdge z.2.1) ∈
      equalityRetainedVertices Q}

/-- Retained ports whose opposite endpoint is removed are precisely boundary
ports of positive-length contracted links. -/
abbrev EqualityRemovedBoundaryRetainedPort {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :=
  {z : EqualityRetainedPorts Q //
    equalityHalfEdgeVertex Q (equalityOppositeHalfEdge z.2.1) ∉
      equalityRetainedVertices Q}

/-- Direct and removed-boundary ports form a disjoint exhaustive split of all
retained ports. -/
noncomputable def equalityRetainedPortSplitEquiv
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    EqualityRetainedPorts Q ≃
      EqualityDirectRetainedPort Q ⊕ EqualityRemovedBoundaryRetainedPort Q := by
  classical
  let P : EqualityRetainedPorts Q → Prop := fun z ↦
    equalityHalfEdgeVertex Q (equalityOppositeHalfEdge z.2.1) ∈
      equalityRetainedVertices Q
  exact (Equiv.sumCompl P).symm

/-- Recover the second endpoint equality for an arbitrary retained port whose
opposite endpoint is named explicitly. -/
private theorem retainedPort_edge_between_opposite
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (z : EqualityRetainedPorts Q) (v : EqualityVertex Q.1)
    (hv : equalityHalfEdgeVertex Q
        (equalityOppositeHalfEdge z.2.1) = v) :
    (equalityEdgeSrc Q z.2.1.1 = z.1.1 ∧
        equalityEdgeDst Q z.2.1.1 = v) ∨
      (equalityEdgeSrc Q z.2.1.1 = v ∧
        equalityEdgeDst Q z.2.1.1 = z.1.1) := by
  rcases z with ⟨r, ⟨⟨e, b⟩, hr⟩⟩
  cases b
  · change equalityEdgeSrc Q e = r.1 at hr
    change equalityEdgeDst Q e = v at hv
    exact Or.inl ⟨hr, hv⟩
  · change equalityEdgeDst Q e = r.1 at hr
    change equalityEdgeSrc Q e = v at hv
    exact Or.inr ⟨hv, hr⟩

/-- Reconstructing the retained port from its edge fiber returns the original
port.  Distinctness of the retained and removed endpoints fixes its side. -/
private theorem portAtFirst_edge_between_opposite_eq
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (z : EqualityRetainedPorts Q) (v : EqualityVertex Q.1)
    (hv : equalityHalfEdgeVertex Q
        (equalityOppositeHalfEdge z.2.1) = v)
    (hrv : z.1.1 ≠ v) :
    equalityPortAtFirst Q z.1.1 v
        ⟨z.2.1.1, retainedPort_edge_between_opposite Q z v hv⟩ = z.2 := by
  rcases z with ⟨r, ⟨⟨e, b⟩, hr⟩⟩
  cases b
  · change equalityEdgeSrc Q e = r.1 at hr
    simp [equalityPortAtFirst, hr]
  · change equalityEdgeDst Q e = r.1 at hr
    change equalityEdgeSrc Q e = v at hv
    have hs : equalityEdgeSrc Q e ≠ r.1 := by
      intro h
      exact hrv (h.symm.trans hv)
    simp [equalityPortAtFirst, hs]

/-- Every retained port pointing into the removed graph is represented by a
unique-component boundary incidence and its original indexed edge
occurrence.  This is the missing surjectivity half of the positive-link port
representation. -/
theorem equalityAllComponentBoundaryPortsEmbedding_surjective_to_boundary
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (z : EqualityRemovedBoundaryRetainedPort Q) :
    ∃ x : EqualityAllComponentBoundaryPorts Q,
      equalityAllComponentBoundaryPortsEmbedding Q x = z.1 := by
  classical
  let v : EqualityVertex Q.1 :=
    equalityHalfEdgeVertex Q (equalityOppositeHalfEdge z.1.2.1)
  have hvRemoved : v ∉ equalityRetainedVertices Q := z.2
  let w : EqualityRemovedVertex Q := ⟨v, hvRemoved⟩
  let c := (equalityRemovedGraph Q).connectedComponentMk w
  let wc : c := ⟨w, ConnectedComponent.connectedComponentMk_mem⟩
  have hrv : z.1.1.1 ≠ v := by
    intro h
    exact hvRemoved (h ▸ z.1.1.2)
  let e : EqualityEdgesBetween Q z.1.1.1 v :=
    ⟨z.1.2.1.1,
      retainedPort_edge_between_opposite Q z.1 v rfl⟩
  have hsupport : (equalitySupportGraph Q).Adj w.1 z.1.1.1 := by
    refine ⟨hrv.symm, ?_⟩
    rw [equalityEdgeMultiplicity_symm_local,
      ← equalityEdgesBetween_card]
    exact Fintype.card_pos_iff.mpr ⟨e⟩
  have hmem : z.1.1 ∈ equalityRetainedNeighborFinset Q w :=
    (mem_equalityRetainedNeighborFinset Q w z.1.1).mpr hsupport
  let b : EqualityComponentBoundaryIncidence Q c :=
    ⟨wc, ⟨z.1.1, hmem⟩⟩
  let x : EqualityAllComponentBoundaryPorts Q := ⟨⟨c, b⟩, e⟩
  refine ⟨x, ?_⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq
      (portAtFirst_edge_between_opposite_eq Q z.1 v rfl hrv)

/-- The component-indexed boundary-port family is exactly the removed-facing
part of the retained-port set.  This packages the preceding injectivity and
surjectivity results into the equivalence used by a decoder. -/
noncomputable def equalityAllComponentBoundaryPortsEquivRemovedBoundary
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    EqualityAllComponentBoundaryPorts Q ≃
      EqualityRemovedBoundaryRetainedPort Q := by
  classical
  let f : EqualityAllComponentBoundaryPorts Q →
      EqualityRemovedBoundaryRetainedPort Q := fun x ↦
    ⟨equalityAllComponentBoundaryPortsEmbedding Q x, by
      have hv := equalityHalfEdgeVertex_opposite_portAtFirst Q
        x.1.2.2.1.1 x.1.2.1.1.1
        (by
          intro h
          exact x.1.2.1.1.2 ((h ▸ x.1.2.2.1.2)))
        x.2
      change equalityHalfEdgeVertex Q
          (equalityOppositeHalfEdge
            (equalityPortAtFirst Q x.1.2.2.1.1 x.1.2.1.1.1 x.2).1) ∉
        equalityRetainedVertices Q
      rw [hv]
      exact x.1.2.1.1.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    apply (equalityAllComponentBoundaryPortsEmbedding Q).injective
    exact congrArg Subtype.val hxy
  · intro z
    obtain ⟨x, hx⟩ :=
      equalityAllComponentBoundaryPortsEmbedding_surjective_to_boundary Q z
    refine ⟨x, Subtype.ext ?_⟩
    exact hx

/-! ## Direct retained edges -/

/-- The opposite endpoint port of a direct retained port, retaining the
endpoint vertex as part of the dependent port type. -/
def equalityDirectRetainedPortOpposite
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    EqualityDirectRetainedPort Q → EqualityDirectRetainedPort Q := fun z ↦
    ⟨⟨⟨equalityHalfEdgeVertex Q
          (equalityOppositeHalfEdge z.1.2.1), z.2⟩,
      ⟨equalityOppositeHalfEdge z.1.2.1, rfl⟩⟩,
    by
      rw [equalityOppositeHalfEdge_involutive, z.1.2.2]
      exact z.1.1.2⟩

@[simp] theorem equalityDirectRetainedPortOpposite_involutive
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (z : EqualityDirectRetainedPort Q) :
    equalityDirectRetainedPortOpposite Q
        (equalityDirectRetainedPortOpposite Q z) = z := by
  rcases z with ⟨⟨⟨r, hr⟩, ⟨⟨e, b⟩, hh⟩⟩, hd⟩
  cases b <;> cases hh <;> rfl

theorem equalityDirectRetainedPortOpposite_ne
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (z : EqualityDirectRetainedPort Q) :
    equalityDirectRetainedPortOpposite Q z ≠ z := by
  intro h
  have hh : equalityOppositeHalfEdge z.1.2.1 = z.1.2.1 := by
    exact congrArg (fun w : EqualityDirectRetainedPort Q ↦ w.1.2.1) h
  exact equalityOppositeHalfEdge_ne z.1.2.1 hh

/-- A fixed-point-free involution on a finite type gives its canonical pairing
into two-element orbits. -/
noncomputable def pairingOfFixedPointFreeInvolution
    {α : Type*} [Fintype α] [DecidableEq α]
    (op : α → α) (hinv : Function.Involutive op)
    (hne : ∀ x, op x ≠ x) :
    Pairing (Finset.univ : Finset α) := by
  classical
  let S : Setoid α :=
    ⟨fun x y ↦ y = x ∨ y = op x,
      ⟨fun _ ↦ Or.inl rfl,
        by
          intro x y h
          rcases h with rfl | h
          · exact Or.inl rfl
          · right
            calc
              x = op (op x) := (hinv x).symm
              _ = op y := congrArg op h.symm,
        by
          intro x y z hxy hyz
          rcases hxy with rfl | hxy <;> rcases hyz with rfl | hyz
          · exact Or.inl rfl
          · exact Or.inr hyz
          · exact Or.inr hxy
          · left
            calc
              z = op y := hyz
              _ = op (op x) := congrArg op hxy
              _ = x := hinv x⟩⟩
  let P := Finpartition.ofSetoid S
  refine ⟨P, ?_⟩
  intro B hB
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
  have hpart : P.part x = B := P.part_eq_of_mem hB hx
  have hclass : P.part x = {x, op x} := by
    ext y
    rw [Finpartition.mem_part_ofSetoid_iff_rel]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    change (y = x ∨ y = op x) ↔ y = x ∨ y = op x
    rfl
  rw [← hpart, hclass]
  exact Finset.card_pair (Ne.symm (hne x))

/-- The fixed-point-free opposite-port involution partitions all direct
retained ports into the indexed edges of the contracted core. -/
noncomputable def equalityDirectRetainedPortPairing
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    Pairing (Finset.univ : Finset (EqualityDirectRetainedPort Q)) :=
  pairingOfFixedPointFreeInvolution
    (equalityDirectRetainedPortOpposite Q)
    (equalityDirectRetainedPortOpposite_involutive Q)
    (equalityDirectRetainedPortOpposite_ne Q)

/-! ## Positive-link port pairing -/

/-- Boundary ports, with their component, endpoint-incidence, and parallel-copy
coordinates exposed. -/
noncomputable def equalityRemovedBoundaryPortEquivComponentFinPairs
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityRemovedBoundaryRetainedPort Q ≃
      Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2 :=
  (equalityAllComponentBoundaryPortsEquivRemovedBoundary Q).symm.trans
    (equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha)

private theorem finTwo_rev_ne_self (i : Fin 2) : Fin.rev i ≠ i := by
  fin_cases i <;> decide

/-- Pair a boundary port with the equally indexed parallel copy at the other
boundary incidence of the same removed component.  The chosen finite
enumerations are auxiliary; any such cross-incidence pairing expands to the
same doubled-link isomorphism class. -/
noncomputable def equalityRemovedBoundaryPortContractedOpposite
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityRemovedBoundaryRetainedPort Q →
      EqualityRemovedBoundaryRetainedPort Q := fun z ↦
  let E := equalityRemovedBoundaryPortEquivComponentFinPairs hp Q ha
  let w := E z
  E.symm ⟨w.1, Fin.rev w.2.1, w.2.2⟩

@[simp] theorem equalityRemovedBoundaryPortContractedOpposite_involutive
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : EqualityRemovedBoundaryRetainedPort Q) :
    equalityRemovedBoundaryPortContractedOpposite hp Q ha
        (equalityRemovedBoundaryPortContractedOpposite hp Q ha z) = z := by
  let E := equalityRemovedBoundaryPortEquivComponentFinPairs hp Q ha
  apply E.injective
  simp [equalityRemovedBoundaryPortContractedOpposite, E,
    Fin.rev_involutive]

theorem equalityRemovedBoundaryPortContractedOpposite_ne
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : EqualityRemovedBoundaryRetainedPort Q) :
    equalityRemovedBoundaryPortContractedOpposite hp Q ha z ≠ z := by
  let E := equalityRemovedBoundaryPortEquivComponentFinPairs hp Q ha
  intro h
  have hE := congrArg E h
  have hrev : Fin.rev (E z).2.1 = (E z).2.1 := by
    simpa [equalityRemovedBoundaryPortContractedOpposite, E] using
      congrArg (fun w ↦ w.2.1) hE
  exact finTwo_rev_ne_self (E z).2.1 hrev

/-- The contracted mate operation on the direct/boundary split. -/
noncomputable def equalityRetainedPortSplitContractedOpposite
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityDirectRetainedPort Q ⊕ EqualityRemovedBoundaryRetainedPort Q →
      EqualityDirectRetainedPort Q ⊕ EqualityRemovedBoundaryRetainedPort Q
  | Sum.inl z => Sum.inl (equalityDirectRetainedPortOpposite Q z)
  | Sum.inr z =>
      Sum.inr (equalityRemovedBoundaryPortContractedOpposite hp Q ha z)

@[simp] theorem equalityRetainedPortSplitContractedOpposite_involutive
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : EqualityDirectRetainedPort Q ⊕
      EqualityRemovedBoundaryRetainedPort Q) :
    equalityRetainedPortSplitContractedOpposite hp Q ha
        (equalityRetainedPortSplitContractedOpposite hp Q ha z) = z := by
  rcases z with z | z
  · simp [equalityRetainedPortSplitContractedOpposite]
  · simp [equalityRetainedPortSplitContractedOpposite]

theorem equalityRetainedPortSplitContractedOpposite_ne
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : EqualityDirectRetainedPort Q ⊕
      EqualityRemovedBoundaryRetainedPort Q) :
    equalityRetainedPortSplitContractedOpposite hp Q ha z ≠ z := by
  rcases z with z | z
  · intro h
    exact equalityDirectRetainedPortOpposite_ne Q z (Sum.inl.inj h)
  · intro h
    exact equalityRemovedBoundaryPortContractedOpposite_ne hp Q ha z
      (Sum.inr.inj h)

/-- All retained ports are paired into the edges of the contracted multigraph:
direct edges use their original opposite ports, while the four ports of each
positive link become two cross-incidence core edges. -/
noncomputable def equalityContractedRetainedPortOpposite
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) : EqualityRetainedPorts Q → EqualityRetainedPorts Q :=
  let E := equalityRetainedPortSplitEquiv Q
  E.symm ∘ equalityRetainedPortSplitContractedOpposite hp Q ha ∘ E

@[simp] theorem equalityContractedRetainedPortOpposite_involutive
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityRetainedPorts Q) :
    equalityContractedRetainedPortOpposite hp Q ha
        (equalityContractedRetainedPortOpposite hp Q ha z) = z := by
  let E := equalityRetainedPortSplitEquiv Q
  apply E.injective
  simp [equalityContractedRetainedPortOpposite, E,
    Function.comp_apply]

theorem equalityContractedRetainedPortOpposite_ne
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityRetainedPorts Q) :
    equalityContractedRetainedPortOpposite hp Q ha z ≠ z := by
  let E := equalityRetainedPortSplitEquiv Q
  intro h
  have hE := congrArg E h
  have hfix : equalityRetainedPortSplitContractedOpposite hp Q ha (E z) =
      E z := by
    simpa [equalityContractedRetainedPortOpposite, E,
      Function.comp_apply] using hE
  exact equalityRetainedPortSplitContractedOpposite_ne hp Q ha (E z) hfix

/-- The full indexed edge pairing of the contracted core. -/
noncomputable def equalityContractedRetainedPortPairing
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Pairing (Finset.univ : Finset (EqualityRetainedPorts Q)) :=
  pairingOfFixedPointFreeInvolution
    (equalityContractedRetainedPortOpposite hp Q ha)
    (equalityContractedRetainedPortOpposite_involutive hp Q ha)
    (equalityContractedRetainedPortOpposite_ne hp Q ha)

#print axioms equalityHalfEdgeVertex_opposite_portAtFirst
#print axioms equalityRetainedPortSplitEquiv
#print axioms equalityAllComponentBoundaryPortsEmbedding_surjective_to_boundary
#print axioms equalityAllComponentBoundaryPortsEquivRemovedBoundary
#print axioms equalityDirectRetainedPortOpposite_involutive
#print axioms equalityDirectRetainedPortOpposite_ne
#print axioms pairingOfFixedPointFreeInvolution
#print axioms equalityDirectRetainedPortPairing
#print axioms equalityRemovedBoundaryPortEquivComponentFinPairs
#print axioms equalityRemovedBoundaryPortContractedOpposite_involutive
#print axioms equalityRemovedBoundaryPortContractedOpposite_ne
#print axioms equalityRetainedPortSplitContractedOpposite_involutive
#print axioms equalityRetainedPortSplitContractedOpposite_ne
#print axioms equalityContractedRetainedPortOpposite_involutive
#print axioms equalityContractedRetainedPortOpposite_ne
#print axioms equalityContractedRetainedPortPairing

end Problem56
