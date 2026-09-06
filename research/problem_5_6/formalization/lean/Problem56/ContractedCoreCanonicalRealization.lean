import Problem56.ContractedCoreCanonicalSource
import Problem56.ContractedCorePathOrder

/-!
# Realizing source ports in the canonical expanded core

This module identifies the source-side retained/direct split and fixes the
boundary-oriented component and vertex coordinates used by the canonical
expansion.  The resulting maps retain the original indexed half-edge ports;
in particular, loops and parallel occurrences are never quotiented by their
endpoints.
-/

namespace Problem56

noncomputable section

/-- A transported retained port is designated by a positive core link exactly
when its original opposite endpoint is removed. -/
theorem equalityStandardPort_isLinkPort_iff
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityRetainedPorts Q) :
    (equalityAbstractContractedCore hp Q ha).2.IsLinkPort
        (equalityRetainedPortsEquivContractedCorePort hp Q ha z) ↔
      equalityHalfEdgeVertex Q (equalityOppositeHalfEdge z.2.1) ∉
        equalityRetainedVertices Q := by
  classical
  let E := equalityRetainedPortsEquivContractedCorePort hp Q ha
  constructor
  · rintro ⟨w, hw⟩
    have hz : equalitySourceLinkRetainedPort hp Q ha w = z := by
      apply E.injective
      change E (equalitySourceLinkRetainedPort hp Q ha w) = E z
      change E (equalitySourceLinkRetainedPort hp Q ha w) = E z at hw
      exact hw
    rw [← hz]
    exact (equalitySourceLinkBoundaryPort hp Q ha w).2
  · intro hz
    let zb : EqualityRemovedBoundaryRetainedPort Q := ⟨z, hz⟩
    let B := equalityRemovedBoundaryPortEquivComponentFinPairs hp Q ha
    let L := equalityRemovedComponentPortsEquivLinkPortIndex Q
    let w := L.symm (B zb)
    refine ⟨w, ?_⟩
    change E (equalitySourceLinkRetainedPort hp Q ha w) = E z
    have hb : equalitySourceLinkBoundaryPort hp Q ha w = zb := by
      apply B.injective
      simp [equalitySourceLinkBoundaryPort, B, L, w,
        equalityRemovedBoundaryPortEquivComponentFinPairs]
    exact congrArg E
      (congrArg (fun x : EqualityRemovedBoundaryRetainedPort Q ↦ x.1) hb)

/-- Direct source retained ports and direct canonical profile ports are the
same subtype under the retained-port transport. -/
noncomputable def equalityDirectRetainedPortEquivCanonicalDirectPort
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityDirectRetainedPort Q ≃
      CanonicalDirectPort (equalityAbstractContractedCore hp Q ha) :=
  Equiv.subtypeEquiv
    (equalityRetainedPortsEquivContractedCorePort hp Q ha) (fun z ↦ by
      constructor
      · intro hret hlink
        exact (equalityStandardPort_isLinkPort_iff hp Q ha z).mp hlink hret
      · intro hnlink
        by_contra hret
        exact hnlink
          ((equalityStandardPort_isLinkPort_iff hp Q ha z).mpr hret))

/-- Numerical component label used by the source-extracted core. -/
noncomputable def equalityRemovedComponentLabel
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) :=
  Fintype.equivFin (equalityRemovedGraph Q).ConnectedComponent c

/-- Recover the source component from its numerical core label. -/
noncomputable def equalityRemovedComponentAtLabel
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) :
    (equalityRemovedGraph Q).ConnectedComponent :=
  (Fintype.equivFin (equalityRemovedGraph Q).ConnectedComponent).symm i

@[simp] theorem equalityRemovedComponentAtLabel_label
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    equalityRemovedComponentAtLabel Q (equalityRemovedComponentLabel Q c) = c :=
  Equiv.symm_apply_apply _ c

@[simp] theorem equalityRemovedComponentLabel_atLabel
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) :
    equalityRemovedComponentLabel Q (equalityRemovedComponentAtLabel Q i) = i :=
  Equiv.apply_symm_apply _ i

/-- The path position of a removed source vertex in the corresponding
canonical expanded-link vertex fiber. -/
noncomputable def equalityRemovedComponentCanonicalPosition
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent) :
    Fin (Fintype.card c) ≃
      Fin ((equalityAbstractContractedCore hp Q ha).2.links.linkLength
        (equalityRemovedComponentLabel Q c)).1 :=
  finCongr (by
    change Fintype.card c = Fintype.card
      (equalityRemovedComponentAtLabel Q
        (equalityRemovedComponentLabel Q c))
    rw [equalityRemovedComponentAtLabel_label])

/-- Retained source vertex labels in the exact canonical profile fiber. -/
noncomputable def equalityRetainedVertexEquivCanonical
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityRetainedVertex Q ≃
      Fin (equalityAbstractContractedCore hp Q ha).1.vertexCountCode.1 :=
  equalityRetainedVertexEquivFin Q

@[simp] theorem equalityRetainedPortsEquivContractedCorePort_fst
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityRetainedPorts Q) :
    (equalityRetainedPortsEquivContractedCorePort hp Q ha z).1 =
      equalityRetainedVertexEquivFin Q z.1 := by
  rfl

@[simp] theorem equalityRemovedComponentCanonicalPosition_val
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c)) :
    (equalityRemovedComponentCanonicalPosition hp Q ha c j).1 = j.1 := by
  rfl

/-- Removed source vertices, oriented component by component, in the exact
canonical internal-vertex fibers. -/
noncomputable def equalityRemovedVertexEquivCanonicalInternal
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityRemovedVertex Q ≃
      (Σ i : Fin (equalityAbstractContractedCore hp Q ha).2.links.linkCount.1,
        Fin ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1) :=
  (equalityRemovedComponentVertexEquiv Q).symm |>.trans
    (Equiv.sigmaCongr
      (Fintype.equivFin (equalityRemovedGraph Q).ConnectedComponent)
      (fun c ↦ (equalityRemovedComponentFinEquiv hp Q ha c).symm |>.trans
        (equalityRemovedComponentCanonicalPosition hp Q ha c)))

/-- The source retained/removed vertex split, with every removed component
oriented from boundary incidence zero to boundary incidence one, realizes the
canonical expanded vertex type. -/
noncomputable def equalityVertexEquivCanonicalExpandedVertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityVertex Q.1 ≃
      CanonicalExpandedVertex (equalityAbstractContractedCore hp Q ha) :=
  ((Equiv.sumCompl (fun u : EqualityVertex Q.1 ↦
      u ∈ equalityRetainedVertices Q)).symm).trans
    (Equiv.sumCongr
      (equalityRetainedVertexEquivCanonical hp Q ha)
      (equalityRemovedVertexEquivCanonicalInternal hp Q ha))

@[simp] theorem equalityRemovedVertexEquivCanonicalInternal_path
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c)) :
    equalityRemovedVertexEquivCanonicalInternal hp Q ha
        (equalityRemovedComponentFinEquiv hp Q ha c j).1 =
      ⟨equalityRemovedComponentLabel Q c,
        equalityRemovedComponentCanonicalPosition hp Q ha c j⟩ := by
  let w := equalityRemovedComponentFinEquiv hp Q ha c j
  have hcomp :
      (equalityRemovedComponentVertexEquiv Q).symm w.1 = ⟨c, w⟩ := by
    apply (equalityRemovedComponentVertexEquiv Q).injective
    rw [Equiv.apply_symm_apply]
    rfl
  unfold equalityRemovedVertexEquivCanonicalInternal
  rw [Equiv.trans_apply, hcomp]
  unfold Equiv.sigmaCongr
  rw [Equiv.trans_apply]
  change (Equiv.sigmaCongrLeft
      (β := fun i : Fin (equalityAbstractContractedCore hp Q ha).2.links.linkCount.1 ↦
        Fin ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1)
      (Fintype.equivFin (equalityRemovedGraph Q).ConnectedComponent))
      ⟨c, equalityRemovedComponentCanonicalPosition hp Q ha c
        ((equalityRemovedComponentFinEquiv hp Q ha c).symm w)⟩ = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem equalityVertexEquivCanonicalExpandedVertex_retained
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (u : EqualityRetainedVertex Q) :
    equalityVertexEquivCanonicalExpandedVertex hp Q ha u.1 =
      Sum.inl (equalityRetainedVertexEquivFin Q u) := by
  change (Equiv.sumCongr
      (equalityRetainedVertexEquivCanonical hp Q ha)
      (equalityRemovedVertexEquivCanonicalInternal hp Q ha))
      ((Equiv.sumCompl (fun v : EqualityVertex Q.1 ↦
        v ∈ equalityRetainedVertices Q)).symm u.1) = _
  rw [Equiv.sumCompl_symm_apply_pos]
  rfl

@[simp] theorem equalityVertexEquivCanonicalExpandedVertex_removedPath
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c)) :
    equalityVertexEquivCanonicalExpandedVertex hp Q ha
        (equalityRemovedComponentFinEquiv hp Q ha c j).1.1 =
      Sum.inr ⟨equalityRemovedComponentLabel Q c,
        equalityRemovedComponentCanonicalPosition hp Q ha c j⟩ := by
  let w := equalityRemovedComponentFinEquiv hp Q ha c j
  change (Equiv.sumCongr
      (equalityRetainedVertexEquivCanonical hp Q ha)
      (equalityRemovedVertexEquivCanonicalInternal hp Q ha))
      ((Equiv.sumCompl (fun v : EqualityVertex Q.1 ↦
        v ∈ equalityRetainedVertices Q)).symm w.1.1) = _
  rw [Equiv.sumCompl_symm_apply_neg]
  change Sum.inr
      (equalityRemovedVertexEquivCanonicalInternal hp Q ha w.1) = _
  rw [equalityRemovedVertexEquivCanonicalInternal_path]

/-! ## Source half-edges carried by the canonical link segments -/

/-- The actual retained-side source half-edge represented by one canonical
boundary coordinate. -/
noncomputable def equalitySourceLinkBoundaryHalfEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (endpoint copy : Fin 2) : EqualityHalfEdge p :=
  (equalitySourceLinkBoundaryPort hp Q ha
    ⟨i, endpoint, copy⟩).1.2.1

/-- The opposite endpoint of an outer link port is the correspondingly
oriented boundary vertex of the removed component. -/
theorem equalitySourceLinkBoundaryHalfEdge_opposite_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (endpoint copy : Fin 2) :
    equalityHalfEdgeVertex Q
        (equalityOppositeHalfEdge
          (equalitySourceLinkBoundaryHalfEdge hp Q ha i endpoint copy)) =
      (equalityRemovedComponentBoundaryVertex hp Q ha
        (equalityRemovedComponentAtLabel Q i) endpoint).1.1 := by
  classical
  let c := equalityRemovedComponentAtLabel Q i
  let x : EqualityAllComponentBoundaryPorts Q :=
    (equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha).symm
      ⟨c, endpoint, copy⟩
  have hxsource :
      (equalitySourceLinkBoundaryPort hp Q ha
        ⟨i, endpoint, copy⟩).1 =
        equalityAllComponentBoundaryPortsEmbedding Q x := by
    rfl
  rw [equalitySourceLinkBoundaryHalfEdge, hxsource]
  change equalityHalfEdgeVertex Q
      (equalityOppositeHalfEdge
        (equalityPortAtFirst Q x.1.2.2.1.1 x.1.2.1.1.1 x.2).1) = _
  have hne : x.1.2.2.1.1 ≠ x.1.2.1.1.1 := by
    intro h
    exact x.1.2.1.1.2 (h ▸ x.1.2.2.1.2)
  rw [equalityHalfEdgeVertex_opposite_portAtFirst Q _ _ hne]
  have hcoord :
      (equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha x) =
        ⟨c, endpoint, copy⟩ := by
    exact (equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha).apply_symm_apply _
  change (⟨x.1.1,
      equalityComponentBoundaryPortsEquivFinPairs hp Q ha x.1.1
        ⟨x.1.2, x.2⟩⟩ :
      Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2) =
        ⟨c, endpoint, copy⟩ at hcoord
  have hcomp : x.1.1 = c := by
    simpa using
      congrArg (fun w :
        Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2 ↦
          w.1) hcoord
  subst c
  have hendpoint :
      equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha x.1.1 x.1.2 =
        endpoint := by
    rw [← equalityComponentBoundaryPortsEquivFinPairs_fst hp Q ha x.1.1
      ⟨x.1.2, x.2⟩]
    simpa using
      congrArg (fun w :
        Σ _c : (equalityRemovedGraph Q).ConnectedComponent, Fin 2 × Fin 2 ↦
          w.2.1) hcoord
  have hinc : x.1.2 =
      equalityComponentBoundaryIncidenceAt hp Q ha x.1.1 endpoint := by
    apply (equalityComponentBoundaryIncidenceEquivFinTwo hp Q ha x.1.1).injective
    rw [equalityComponentBoundaryIncidenceEquivFinTwo_apply_at]
    exact hendpoint
  exact congrArg (fun w : EqualityComponentBoundaryIncidence Q x.1.1 ↦
    w.1.1.1) hinc

/-- The indexed source edge used by an internal canonical segment `k`, where
`1 ≤ k < card c`; its endpoints are path positions `k-1` and `k` and its
two parallel occurrences are enumerated by `copy : Fin 2`. -/
noncomputable def equalityRemovedComponentInternalSegmentEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c))
    (hj : j.1 + 1 < Fintype.card c)
    (copy : Fin 2) :
    EqualityEdgesBetween Q
      (equalityRemovedComponentFinEquiv hp Q ha c
        j).1.1
      (equalityRemovedComponentFinEquiv hp Q ha c
        ⟨j.1 + 1, hj⟩).1.1 :=
  (Fintype.equivFinOfCardEq
    (equalityRemovedComponentFinEquiv_edge_card_succ hp Q ha c j hj)).symm copy

/-- Source port at endpoint `b` of one internal canonical segment. -/
noncomputable def equalityRemovedComponentInternalSegmentHalfEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c))
    (hj : j.1 + 1 < Fintype.card c)
    (copy : Fin 2) (b : Bool) : EqualityHalfEdge p :=
  let u := (equalityRemovedComponentFinEquiv hp Q ha c
    j).1.1
  let v := (equalityRemovedComponentFinEquiv hp Q ha c
    ⟨j.1 + 1, hj⟩).1.1
  let e := equalityRemovedComponentInternalSegmentEdge
    hp Q ha c j hj copy
  match b with
  | false => (equalityPortAtFirst Q u v e).1
  | true => equalityOppositeHalfEdge (equalityPortAtFirst Q u v e).1

@[simp] theorem equalityRemovedComponentInternalSegmentHalfEdge_false_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c))
    (hj : j.1 + 1 < Fintype.card c) (copy : Fin 2) :
    equalityHalfEdgeVertex Q
        (equalityRemovedComponentInternalSegmentHalfEdge
          hp Q ha c j hj copy false) =
      (equalityRemovedComponentFinEquiv hp Q ha c j).1.1 := by
  exact (equalityPortAtFirst Q _ _ _).2

@[simp] theorem equalityRemovedComponentInternalSegmentHalfEdge_true_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c))
    (hj : j.1 + 1 < Fintype.card c) (copy : Fin 2) :
    equalityHalfEdgeVertex Q
        (equalityRemovedComponentInternalSegmentHalfEdge
          hp Q ha c j hj copy true) =
      (equalityRemovedComponentFinEquiv hp Q ha c
        ⟨j.1 + 1, hj⟩).1.1 := by
  apply equalityHalfEdgeVertex_opposite_portAtFirst
  intro huv
  have hw :
      equalityRemovedComponentFinEquiv hp Q ha c j =
        equalityRemovedComponentFinEquiv hp Q ha c ⟨j.1 + 1, hj⟩ :=
    Subtype.ext (Subtype.ext huv)
  have hindex := (equalityRemovedComponentFinEquiv hp Q ha c).injective hw
  have hval := congrArg Fin.val hindex
  change j.1 = j.1 + 1 at hval
  omega

/-- Numerical coordinates of the internal (removed--removed) doubled
segments, excluding the two retained boundary segments. -/
abbrev EqualityCanonicalInternalSegmentCoordinate
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :=
  Σ i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent),
    ({j : Fin (Fintype.card (equalityRemovedComponentAtLabel Q i)) //
      j.1 + 1 < Fintype.card (equalityRemovedComponentAtLabel Q i)} × Fin 2)

/-- Source indexed edge carried by an internal canonical segment
coordinate. -/
noncomputable def equalityCanonicalInternalSegmentSourceEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityCanonicalInternalSegmentCoordinate Q → Fin (2 * p) := fun x ↦
  (equalityRemovedComponentInternalSegmentEdge hp Q ha
    (equalityRemovedComponentAtLabel Q x.1) x.2.1.1 x.2.1.2 x.2.2).1

/-- Distinct internal component/position/copy coordinates use distinct
source indexed edges. -/
theorem equalityCanonicalInternalSegmentSourceEdge_injective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Injective
      (equalityCanonicalInternalSegmentSourceEdge hp Q ha) := by
  rintro ⟨i, ⟨⟨j, hj⟩, copy⟩⟩ ⟨i', ⟨⟨j', hj'⟩, copy'⟩⟩ hedge
  let c := equalityRemovedComponentAtLabel Q i
  let c' := equalityRemovedComponentAtLabel Q i'
  let u := equalityRemovedComponentFinEquiv hp Q ha c j
  let v := equalityRemovedComponentFinEquiv hp Q ha c ⟨j.1 + 1, hj⟩
  let u' := equalityRemovedComponentFinEquiv hp Q ha c' j'
  let v' := equalityRemovedComponentFinEquiv hp Q ha c' ⟨j'.1 + 1, hj'⟩
  let e := equalityRemovedComponentInternalSegmentEdge
    hp Q ha c j hj copy
  let e' := equalityRemovedComponentInternalSegmentEdge
    hp Q ha c' j' hj' copy'
  have heval : e.1 = e'.1 := hedge
  have hsrc := congrArg (equalityEdgeSrc Q) heval
  have hdst := congrArg (equalityEdgeDst Q) heval
  have hcomponent_of_left (hleft : u.1.1 = u'.1.1) : i = i' := by
    have huu' : u.1 = u'.1 := Subtype.ext hleft
    have hcc' : c = c' :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex
        u.2 (huu'.symm ▸ u'.2)
    calc
      i = equalityRemovedComponentLabel Q c := by simp [c]
      _ = equalityRemovedComponentLabel Q c' := congrArg _ hcc'
      _ = i' := by simp [c']
  have hcomponent_of_cross (hleft : u.1.1 = v'.1.1) : i = i' := by
    have huv' : u.1 = v'.1 := Subtype.ext hleft
    have hcc' : c = c' :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex
        u.2 (huv'.symm ▸ v'.2)
    calc
      i = equalityRemovedComponentLabel Q c := by simp [c]
      _ = equalityRemovedComponentLabel Q c' := congrArg _ hcc'
      _ = i' := by simp [c']
  have hordered (hleft : u.1.1 = u'.1.1)
      (hright : v.1.1 = v'.1.1) :
      (⟨i, ⟨⟨j, hj⟩, copy⟩⟩ :
        EqualityCanonicalInternalSegmentCoordinate Q) =
        ⟨i', ⟨⟨j', hj'⟩, copy'⟩⟩ := by
    have hii' := hcomponent_of_left hleft
    subst i'
    have hjj' : j = j' := by
      apply (equalityRemovedComponentFinEquiv hp Q ha c).injective
      exact Subtype.ext (Subtype.ext hleft)
    subst j'
    have hcopy : copy = copy' := by
      apply (Fintype.equivFinOfCardEq
        (equalityRemovedComponentFinEquiv_edge_card_succ hp Q ha c j hj)).symm.injective
      apply Subtype.ext
      exact heval
    subst copy'
    rfl
  have hcross_false (hleft : u.1.1 = v'.1.1)
      (hright : v.1.1 = u'.1.1) : False := by
    have hii' := hcomponent_of_cross hleft
    subst i'
    have hj_forward : j = ⟨j'.1 + 1, hj'⟩ := by
      apply (equalityRemovedComponentFinEquiv hp Q ha c).injective
      exact Subtype.ext (Subtype.ext hleft)
    have hj_backward : ⟨j.1 + 1, hj⟩ = j' := by
      apply (equalityRemovedComponentFinEquiv hp Q ha c).injective
      exact Subtype.ext (Subtype.ext hright)
    have hval_forward := congrArg Fin.val hj_forward
    have hval_backward := congrArg Fin.val hj_backward
    change j.1 = j'.1 + 1 at hval_forward
    change j.1 + 1 = j'.1 at hval_backward
    omega
  rcases e.2 with he | he <;> rcases e'.2 with he' | he'
  · exact hordered
      (he.1.symm.trans (hsrc.trans he'.1))
      (he.2.symm.trans (hdst.trans he'.2))
  · exact (hcross_false
      (he.1.symm.trans (hsrc.trans he'.1))
      (he.2.symm.trans (hdst.trans he'.2))).elim
  · exact (hcross_false
      (he.2.symm.trans (hdst.trans he'.2))
      (he.1.symm.trans (hsrc.trans he'.1))).elim
  · exact hordered
      (he.2.symm.trans (hdst.trans he'.2))
      (he.1.symm.trans (hsrc.trans he'.1))

/-- Realize every canonical positive-link segment port as its original
indexed source half-edge.  Segment zero begins at boundary incidence zero,
segment `ell` ends at boundary incidence one, and the intervening segments
follow the boundary-oriented component path. -/
noncomputable def equalityCanonicalLinkSegmentSourceHalfEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    CanonicalLinkSegmentPort (equalityAbstractContractedCore hp Q ha) →
      EqualityHalfEdge p
  | ⟨i, k, copy, b⟩ => by
      let c := equalityRemovedComponentAtLabel Q i
      by_cases hkzero : k.1 = 0
      · exact match b with
        | false => equalitySourceLinkBoundaryHalfEdge hp Q ha i 0 copy
        | true => equalityOppositeHalfEdge
            (equalitySourceLinkBoundaryHalfEdge hp Q ha i 0 copy)
      · by_cases hklast :
          k.1 = ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
        · exact match b with
          | false => equalityOppositeHalfEdge
              (equalitySourceLinkBoundaryHalfEdge hp Q ha i 1 copy)
          | true => equalitySourceLinkBoundaryHalfEdge hp Q ha i 1 copy
        · have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hkzero
          have hklt : k.1 < Fintype.card c := by
            change k.1 <
              ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
            omega
          let j : Fin (Fintype.card c) := ⟨k.1 - 1, by omega⟩
          have hj : j.1 + 1 < Fintype.card c := by
            change k.1 - 1 + 1 < Fintype.card c
            omega
          exact equalityRemovedComponentInternalSegmentHalfEdge
            hp Q ha c j hj copy b

/-- Toggling a canonical segment endpoint is literally source half-edge
reversal. -/
theorem equalityCanonicalLinkSegmentSourceHalfEdge_toggle
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalLinkSegmentPort
      (equalityAbstractContractedCore hp Q ha)) :
    equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
        ⟨z.1, z.2.1, z.2.2.1, !z.2.2.2⟩ =
      equalityOppositeHalfEdge
        (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha z) := by
  rcases z with ⟨i, k, copy, b⟩
  have hlenne :
      (equalityAbstractContractedCore hp Q ha).2.links.linkLength i ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    have hpos :=
      (equalityAbstractContractedCore hp Q ha).2.links.linkLength_pos i
    simp only [Fin.val_zero] at hval
    omega
  by_cases hkzero : k.1 = 0
  · cases b <;> simp [equalityCanonicalLinkSegmentSourceHalfEdge,
      equalityRemovedComponentInternalSegmentHalfEdge, hkzero]
  · by_cases hklast : k.1 =
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
    · cases b <;> simp [equalityCanonicalLinkSegmentSourceHalfEdge,
        equalityRemovedComponentInternalSegmentHalfEdge, hkzero, hklast,
        hlenne]
    · cases b <;> simp [equalityCanonicalLinkSegmentSourceHalfEdge,
        equalityRemovedComponentInternalSegmentHalfEdge, hkzero, hklast]

@[simp] theorem equalityOppositeHalfEdge_fst
    {p : ℕ} (h : EqualityHalfEdge p) :
    (equalityOppositeHalfEdge h).1 = h.1 := by
  rcases h with ⟨e, b⟩
  rfl

@[simp] theorem equalityRemovedComponentInternalSegmentHalfEdge_fst
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (c : (equalityRemovedGraph Q).ConnectedComponent)
    (j : Fin (Fintype.card c))
    (hj : j.1 + 1 < Fintype.card c) (copy : Fin 2) (b : Bool) :
    (equalityRemovedComponentInternalSegmentHalfEdge
      hp Q ha c j hj copy b).1 =
      (equalityRemovedComponentInternalSegmentEdge
        hp Q ha c j hj copy).1 := by
  cases b
  · simp only [equalityRemovedComponentInternalSegmentHalfEdge]
    unfold equalityPortAtFirst
    split <;> rfl
  · simp only [equalityRemovedComponentInternalSegmentHalfEdge,
      equalityOppositeHalfEdge_fst]
    unfold equalityPortAtFirst
    split <;> rfl

/-- At segment zero, forgetting the half-edge side gives the first boundary
source edge. -/
theorem equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (k : Fin
      (((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 + 1))
    (copy : Fin 2) (b : Bool) (hk : k.1 = 0) :
    (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
      ⟨i, k, copy, b⟩).1 =
      (equalitySourceLinkBoundaryHalfEdge hp Q ha i 0 copy).1 := by
  cases b <;> simp [equalityCanonicalLinkSegmentSourceHalfEdge, hk]

/-- At the last segment, forgetting the half-edge side gives the second
boundary source edge. -/
theorem equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (k : Fin
      (((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 + 1))
    (copy : Fin 2) (b : Bool)
    (hkzero : k.1 ≠ 0)
    (hklast : k.1 =
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1) :
    (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
      ⟨i, k, copy, b⟩).1 =
      (equalitySourceLinkBoundaryHalfEdge hp Q ha i 1 copy).1 := by
  have hlenvalne :
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 ≠ 0 := by
    exact Nat.ne_of_gt
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength_pos i)
  cases b <;> simp [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
    hklast, hlenvalne]

/-- An interior segment forgets to the globally indexed internal source
edge at path position `k-1`. -/
theorem equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (k : Fin
      (((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 + 1))
    (copy : Fin 2) (b : Bool)
    (hkzero : k.1 ≠ 0)
    (hklast : k.1 ≠
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1) :
    (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
      ⟨i, k, copy, b⟩).1 =
      equalityCanonicalInternalSegmentSourceEdge hp Q ha
        ⟨i, ⟨⟨⟨k.1 - 1, by
          change k.1 - 1 <
            ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
          omega⟩, by
            change k.1 - 1 + 1 <
              ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
            omega⟩, copy⟩⟩ := by
  cases b <;> simp [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
    hklast, equalityCanonicalInternalSegmentSourceEdge]

/-! ## Direct ports and the global canonical realization map -/

/-- On the direct summand, the source contracted mate is the original
indexed half-edge reversal. -/
@[simp] theorem equalityContractedRetainedPortOpposite_direct
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityDirectRetainedPort Q) :
    equalityContractedRetainedPortOpposite hp Q ha z.1 =
      (equalityDirectRetainedPortOpposite Q z).1 := by
  let S := equalityRetainedPortSplitEquiv Q
  have hS : S z.1 = Sum.inl z := by
    simpa [S, equalityRetainedPortSplitEquiv] using
      (Equiv.sumCompl_symm_apply_pos z)
  have hSop : S (equalityDirectRetainedPortOpposite Q z).1 =
      Sum.inl (equalityDirectRetainedPortOpposite Q z) := by
    simpa [S, equalityRetainedPortSplitEquiv] using
      (Equiv.sumCompl_symm_apply_pos
        (equalityDirectRetainedPortOpposite Q z))
  apply S.injective
  simp only [equalityContractedRetainedPortOpposite, S,
    Function.comp_apply, Equiv.apply_symm_apply]
  rw [hS, hSop]
  rfl

/-- The standard numerical mate transports the direct source mate. -/
theorem equalityStandardContractedPortOpposite_direct
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityDirectRetainedPort Q) :
    equalityStandardContractedPortOpposite hp Q ha
        (equalityRetainedPortsEquivContractedCorePort hp Q ha z.1) =
      equalityRetainedPortsEquivContractedCorePort hp Q ha
        (equalityDirectRetainedPortOpposite Q z).1 := by
  simp [equalityStandardContractedPortOpposite, Function.comp_apply]

/-- Realize a direct canonical port as its original indexed source half-edge. -/
noncomputable def equalityCanonicalDirectPortSourceHalfEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    CanonicalDirectPort (equalityAbstractContractedCore hp Q ha) →
      EqualityHalfEdge p := fun z ↦
  let d :=
    (equalityDirectRetainedPortEquivCanonicalDirectPort hp Q ha).symm z
  d.1.2.1

/-- A retained port is determined by its underlying indexed source
half-edge. -/
theorem equalityRetainedPort_halfEdge_injective
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    Function.Injective (fun z : EqualityRetainedPorts Q ↦ z.2.1) := by
  rintro ⟨u, ⟨h, hu⟩⟩ ⟨v, ⟨g, hv⟩⟩ hh
  dsimp only at hh
  subst g
  have huv : u = v := Subtype.ext (hu.symm.trans hv)
  subst v
  rfl

/-- The component, endpoint, and parallel-copy coordinates of a boundary
half-edge are globally injective. -/
theorem equalitySourceLinkBoundaryHalfEdge_injective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Injective (fun w : ContractedCoreLinkPortIndex
        (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦
      equalitySourceLinkBoundaryHalfEdge hp Q ha w.1 w.2.1 w.2.2) := by
  intro w z hwz
  have hret :
      (equalitySourceLinkBoundaryPort hp Q ha w).1 =
        (equalitySourceLinkBoundaryPort hp Q ha z).1 := by
    apply equalityRetainedPort_halfEdge_injective Q
    exact hwz
  have hboundary :
      equalitySourceLinkBoundaryPort hp Q ha w =
        equalitySourceLinkBoundaryPort hp Q ha z := Subtype.ext hret
  apply (equalityRemovedComponentPortsEquivLinkPortIndex Q).injective
  apply (equalityAllComponentBoundaryPortsEquivComponentFinPairs hp Q ha).symm.injective
  apply (equalityAllComponentBoundaryPortsEquivRemovedBoundary Q).injective
  exact hboundary

/-- A removed-facing retained boundary port is determined already by its
indexed edge occurrence: only one endpoint of such an edge is retained. -/
theorem equalityRemovedBoundaryRetainedPort_eq_of_edge_eq
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (z w : EqualityRemovedBoundaryRetainedPort Q)
    (hedge : z.1.2.1.1 = w.1.2.1.1) : z = w := by
  have halfEdge_eq_or_opposite (a b : EqualityHalfEdge p)
      (hab : a.1 = b.1) :
      a = b ∨ a = equalityOppositeHalfEdge b := by
    rcases a with ⟨e, q⟩
    rcases b with ⟨f, r⟩
    dsimp only at hab
    subst f
    cases q <;> cases r <;> simp [equalityOppositeHalfEdge]
  have horient : z.1.2.1 = w.1.2.1 ∨
      z.1.2.1 = equalityOppositeHalfEdge w.1.2.1 := by
    exact halfEdge_eq_or_opposite z.1.2.1 w.1.2.1 hedge
  rcases horient with hsame | hopp
  · apply Subtype.ext
    apply equalityRetainedPort_halfEdge_injective Q
    exact hsame
  · exfalso
    apply w.2
    have hzmem : equalityHalfEdgeVertex Q z.1.2.1 ∈
        equalityRetainedVertices Q := by
      rw [z.1.2.2]
      exact z.1.1.2
    exact congrArg (equalityHalfEdgeVertex Q) hopp ▸ hzmem

/-- Boundary source edges retain their global component/endpoint/copy
coordinates even after forgetting the retained-side orientation. -/
theorem equalitySourceLinkBoundaryEdge_injective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Injective (fun w : ContractedCoreLinkPortIndex
        (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦
      (equalitySourceLinkBoundaryHalfEdge hp Q ha
        w.1 w.2.1 w.2.2).1) := by
  intro w z hedge
  apply equalitySourceLinkBoundaryHalfEdge_injective hp Q ha
  have hb := equalityRemovedBoundaryRetainedPort_eq_of_edge_eq Q
    (equalitySourceLinkBoundaryPort hp Q ha w)
    (equalitySourceLinkBoundaryPort hp Q ha z) hedge
  exact congrArg (fun q : EqualityRemovedBoundaryRetainedPort Q ↦
    q.1.2.1) hb

/-- A retained--removed boundary edge cannot be one of the internal
removed--removed path edges. -/
theorem equalitySourceLinkBoundaryEdge_ne_internal
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (w : ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (x : EqualityCanonicalInternalSegmentCoordinate Q) :
    (equalitySourceLinkBoundaryHalfEdge hp Q ha w.1 w.2.1 w.2.2).1 ≠
      equalityCanonicalInternalSegmentSourceEdge hp Q ha x := by
  intro hedge
  let r := equalitySourceLinkBoundaryPort hp Q ha w
  let c := equalityRemovedComponentAtLabel Q x.1
  let u := equalityRemovedComponentFinEquiv hp Q ha c x.2.1.1
  let v := equalityRemovedComponentFinEquiv hp Q ha c
    ⟨x.2.1.1.1 + 1, x.2.1.2⟩
  let e := equalityRemovedComponentInternalSegmentEdge
    hp Q ha c x.2.1.1 x.2.1.2 x.2.2
  have heval : r.1.2.1.1 = e.1 := hedge
  have hsrc := congrArg (equalityEdgeSrc Q) heval
  have hdst := congrArg (equalityEdgeDst Q) heval
  have hrmem : equalityHalfEdgeVertex Q r.1.2.1 ∈
      equalityRetainedVertices Q := by
    rw [r.1.2.2]
    exact r.1.1.2
  have hrEndpoint :
      equalityHalfEdgeVertex Q r.1.2.1 =
          equalityEdgeSrc Q r.1.2.1.1 ∨
        equalityHalfEdgeVertex Q r.1.2.1 =
          equalityEdgeDst Q r.1.2.1.1 := by
    rcases r.1.2.1 with ⟨re, b⟩
    cases b <;> simp [equalityHalfEdgeVertex]
  rcases hrEndpoint with hr | hr <;> rcases e.2 with he | he
  · exact u.1.2 (hr.trans (hsrc.trans he.1) ▸ hrmem)
  · exact v.1.2 (hr.trans (hsrc.trans he.1) ▸ hrmem)
  · exact v.1.2 (hr.trans (hdst.trans he.2) ▸ hrmem)
  · exact u.1.2 (hr.trans (hdst.trans he.2) ▸ hrmem)

/-- The direct summand of the realization is injective. -/
theorem equalityCanonicalDirectPortSourceHalfEdge_injective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Injective
      (equalityCanonicalDirectPortSourceHalfEdge hp Q ha) := by
  intro z w hzw
  let D := equalityDirectRetainedPortEquivCanonicalDirectPort hp Q ha
  apply D.symm.injective
  apply Subtype.ext
  apply equalityRetainedPort_halfEdge_injective Q
  exact hzw

/-- The positive-link summand retains its component, segment, parallel-copy,
and half-edge-side coordinates. -/
theorem equalityCanonicalLinkSegmentSourceHalfEdge_injective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Injective
      (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha) := by
  rintro ⟨i, k, copy, b⟩ ⟨i', k', copy', b'⟩ hh
  change Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) at i i'
  have hedge := congrArg Prod.fst hh
  have finish (hi : i = i') (hkval : k.1 = k'.1)
      (hcopy : copy = copy') :
      (⟨i, k, copy, b⟩ : CanonicalLinkSegmentPort
        (equalityAbstractContractedCore hp Q ha)) =
        ⟨i', k', copy', b'⟩ := by
    subst i'
    have hk : k = k' := Fin.ext hkval
    subst k'
    subst copy'
    have hb : b = b' := by
      cases b <;> cases b'
      · rfl
      · exfalso
        have ht := equalityCanonicalLinkSegmentSourceHalfEdge_toggle hp Q ha
          (⟨i, k, copy, false⟩ : CanonicalLinkSegmentPort
            (equalityAbstractContractedCore hp Q ha))
        exact equalityOppositeHalfEdge_ne _ (hh.trans ht).symm
      · exfalso
        have ht := equalityCanonicalLinkSegmentSourceHalfEdge_toggle hp Q ha
          (⟨i, k, copy, false⟩ : CanonicalLinkSegmentPort
            (equalityAbstractContractedCore hp Q ha))
        exact equalityOppositeHalfEdge_ne _ (ht.symm.trans hh)
      · rfl
    subst b'
    rfl
  have boundary_coordinate_eq (endpoint endpoint' : Fin 2)
      (h :
        (equalitySourceLinkBoundaryHalfEdge hp Q ha i endpoint copy).1 =
          (equalitySourceLinkBoundaryHalfEdge hp Q ha
            i' endpoint' copy').1) :
      (⟨i, endpoint, copy⟩ : ContractedCoreLinkPortIndex
        (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) =
        ⟨i', endpoint', copy'⟩ :=
    equalitySourceLinkBoundaryEdge_injective hp Q ha h
  let internal_coordinate (q : Fin
      (((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 + 1))
      (hqzero : q.1 ≠ 0)
      (hqlast : q.1 ≠
        ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1)
      (r : Fin 2) : EqualityCanonicalInternalSegmentCoordinate Q :=
    ⟨i, ⟨⟨⟨q.1 - 1, by
      change q.1 - 1 <
        ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
      omega⟩, by
        change q.1 - 1 + 1 <
          ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
        omega⟩, r⟩⟩
  let internal_coordinate' (q : Fin
      (((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1 + 1))
      (hqzero : q.1 ≠ 0)
      (hqlast : q.1 ≠
        ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1)
      (r : Fin 2) : EqualityCanonicalInternalSegmentCoordinate Q :=
    ⟨i', ⟨⟨⟨q.1 - 1, by
      change q.1 - 1 <
        ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1
      omega⟩, by
        change q.1 - 1 + 1 <
          ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1
        omega⟩, r⟩⟩
  by_cases hkzero : k.1 = 0
  · by_cases hkzero' : k'.1 = 0
    · have hcoord :
          (⟨i, 0, copy⟩ : ContractedCoreLinkPortIndex
            (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) =
            ⟨i', 0, copy'⟩ := boundary_coordinate_eq 0 0 (by
        calc
          (equalitySourceLinkBoundaryHalfEdge hp Q ha i 0 copy).1 =
              (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                ⟨i, k, copy, b⟩).1 :=
            (equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
              hp Q ha i k copy b hkzero).symm
          _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                ⟨i', k', copy', b'⟩).1 := hedge
          _ = (equalitySourceLinkBoundaryHalfEdge hp Q ha i' 0 copy').1 :=
            equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
              hp Q ha i' k' copy' b' hkzero')
      have hi : i = i' := congrArg (fun q : ContractedCoreLinkPortIndex
        (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦ q.1) hcoord
      subst i'
      exact finish rfl (by omega)
        (congrArg (fun q : ContractedCoreLinkPortIndex
          (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦ q.2.2)
          hcoord)
    · by_cases hklast' : k'.1 =
          ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1
      · have hcoord :
            (⟨i, 0, copy⟩ : ContractedCoreLinkPortIndex
              (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) =
              ⟨i', 1, copy'⟩ := boundary_coordinate_eq 0 1 (by
          calc
            (equalitySourceLinkBoundaryHalfEdge hp Q ha i 0 copy).1 =
                (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i, k, copy, b⟩).1 :=
              (equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
                hp Q ha i k copy b hkzero).symm
            _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i', k', copy', b'⟩).1 := hedge
            _ = (equalitySourceLinkBoundaryHalfEdge hp Q ha i' 1 copy').1 :=
              equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
                hp Q ha i' k' copy' b' hkzero' hklast')
        have hend := congrArg (fun q : ContractedCoreLinkPortIndex
          (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦ q.2.1.1)
          hcoord
        norm_num at hend
      · let x' := internal_coordinate' k' hkzero' hklast' copy'
        exfalso
        apply equalitySourceLinkBoundaryEdge_ne_internal hp Q ha
          ⟨i, 0, copy⟩ x'
        calc
          (equalitySourceLinkBoundaryHalfEdge hp Q ha i 0 copy).1 =
              (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                ⟨i, k, copy, b⟩).1 :=
            (equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
              hp Q ha i k copy b hkzero).symm
          _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                ⟨i', k', copy', b'⟩).1 := hedge
          _ = equalityCanonicalInternalSegmentSourceEdge hp Q ha x' := by
            simpa only [x', internal_coordinate'] using
              equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
                hp Q ha i' k' copy' b' hkzero' hklast'
  · by_cases hklast : k.1 =
        ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
    · by_cases hkzero' : k'.1 = 0
      · have hcoord :
            (⟨i, 1, copy⟩ : ContractedCoreLinkPortIndex
              (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) =
              ⟨i', 0, copy'⟩ := boundary_coordinate_eq 1 0 (by
          calc
            (equalitySourceLinkBoundaryHalfEdge hp Q ha i 1 copy).1 =
                (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i, k, copy, b⟩).1 :=
              (equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
                hp Q ha i k copy b hkzero hklast).symm
            _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i', k', copy', b'⟩).1 := hedge
            _ = (equalitySourceLinkBoundaryHalfEdge hp Q ha i' 0 copy').1 :=
              equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
                hp Q ha i' k' copy' b' hkzero')
        have hend := congrArg (fun q : ContractedCoreLinkPortIndex
          (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦ q.2.1.1)
          hcoord
        norm_num at hend
      · by_cases hklast' : k'.1 =
            ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1
        · have hcoord :
              (⟨i, 1, copy⟩ : ContractedCoreLinkPortIndex
                (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) =
                ⟨i', 1, copy'⟩ := boundary_coordinate_eq 1 1 (by
            calc
              (equalitySourceLinkBoundaryHalfEdge hp Q ha i 1 copy).1 =
                  (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                    ⟨i, k, copy, b⟩).1 :=
                (equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
                  hp Q ha i k copy b hkzero hklast).symm
              _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                    ⟨i', k', copy', b'⟩).1 := hedge
              _ = (equalitySourceLinkBoundaryHalfEdge hp Q ha i' 1 copy').1 :=
                equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
                  hp Q ha i' k' copy' b' hkzero' hklast')
          have hi : i = i' := congrArg (fun q : ContractedCoreLinkPortIndex
            (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦ q.1) hcoord
          subst i'
          exact finish rfl (by omega)
            (congrArg (fun q : ContractedCoreLinkPortIndex
              (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) ↦ q.2.2)
              hcoord)
        · let x' := internal_coordinate' k' hkzero' hklast' copy'
          exfalso
          apply equalitySourceLinkBoundaryEdge_ne_internal hp Q ha
            ⟨i, 1, copy⟩ x'
          calc
            (equalitySourceLinkBoundaryHalfEdge hp Q ha i 1 copy).1 =
                (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i, k, copy, b⟩).1 :=
              (equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
                hp Q ha i k copy b hkzero hklast).symm
            _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i', k', copy', b'⟩).1 := hedge
            _ = equalityCanonicalInternalSegmentSourceEdge hp Q ha x' := by
              simpa only [x', internal_coordinate'] using
                equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
                  hp Q ha i' k' copy' b' hkzero' hklast'
    · let x := internal_coordinate k hkzero hklast copy
      by_cases hkzero' : k'.1 = 0
      · exfalso
        apply equalitySourceLinkBoundaryEdge_ne_internal hp Q ha
          ⟨i', 0, copy'⟩ x
        calc
          (equalitySourceLinkBoundaryHalfEdge hp Q ha i' 0 copy').1 =
              (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                ⟨i', k', copy', b'⟩).1 :=
            (equalityCanonicalLinkSegmentSourceHalfEdge_edge_zero
              hp Q ha i' k' copy' b' hkzero').symm
          _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                ⟨i, k, copy, b⟩).1 := hedge.symm
          _ = equalityCanonicalInternalSegmentSourceEdge hp Q ha x := by
            simpa only [x, internal_coordinate] using
              equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
                hp Q ha i k copy b hkzero hklast
      · by_cases hklast' : k'.1 =
            ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i').1
        · exfalso
          apply equalitySourceLinkBoundaryEdge_ne_internal hp Q ha
            ⟨i', 1, copy'⟩ x
          calc
            (equalitySourceLinkBoundaryHalfEdge hp Q ha i' 1 copy').1 =
                (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i', k', copy', b'⟩).1 :=
              (equalityCanonicalLinkSegmentSourceHalfEdge_edge_last
                hp Q ha i' k' copy' b' hkzero' hklast').symm
            _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                  ⟨i, k, copy, b⟩).1 := hedge.symm
            _ = equalityCanonicalInternalSegmentSourceEdge hp Q ha x := by
              simpa only [x, internal_coordinate] using
                equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
                  hp Q ha i k copy b hkzero hklast
        · let x' := internal_coordinate' k' hkzero' hklast' copy'
          have hcoord : x = x' :=
            equalityCanonicalInternalSegmentSourceEdge_injective hp Q ha (by
              calc
                equalityCanonicalInternalSegmentSourceEdge hp Q ha x =
                    (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                      ⟨i, k, copy, b⟩).1 :=
                  (by
                    simpa only [x, internal_coordinate] using
                      (equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
                        hp Q ha i k copy b hkzero hklast).symm)
                _ = (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
                      ⟨i', k', copy', b'⟩).1 := hedge
                _ = equalityCanonicalInternalSegmentSourceEdge hp Q ha x' := by
                  simpa only [x', internal_coordinate'] using
                    equalityCanonicalLinkSegmentSourceHalfEdge_edge_internal
                      hp Q ha i' k' copy' b' hkzero' hklast')
          simp only [x, x', internal_coordinate, internal_coordinate'] at hcoord
          have hi : i = i' := congrArg Sigma.fst hcoord
          have hjval : k.1 - 1 = k'.1 - 1 := congrArg
            (fun q : EqualityCanonicalInternalSegmentCoordinate Q ↦
              q.2.1.1.1) hcoord
          have hcopy : copy = copy' := congrArg
            (fun q : EqualityCanonicalInternalSegmentCoordinate Q ↦ q.2.2)
            hcoord
          exact finish hi (by omega) hcopy

/-- A retained source port has the retained numerical vertex label stored in
its transported profile port. -/
theorem equalityVertexEquivCanonicalExpandedVertex_retainedPort
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) (z : EqualityRetainedPorts Q) :
    equalityVertexEquivCanonicalExpandedVertex hp Q ha
        (equalityHalfEdgeVertex Q z.2.1) =
      Sum.inl
        (equalityRetainedPortsEquivContractedCorePort hp Q ha z).1 := by
  rw [z.2.2]
  rw [equalityVertexEquivCanonicalExpandedVertex_retained]
  congr

@[simp] theorem equalityRetainedPortsEquivContractedCorePort_sourceLink
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (w : ContractedCoreLinkPortIndex
      (Fintype.card (equalityRemovedGraph Q).ConnectedComponent)) :
    equalityRetainedPortsEquivContractedCorePort hp Q ha
        (equalitySourceLinkRetainedPort hp Q ha w) =
      (equalityAbstractContractedCore hp Q ha).2.links.linkPorts w := by
  rfl

/-- A source path position in the component carrying numerical label `i`
is the same dependent canonical internal-vertex coordinate. -/
theorem equalityRemovedComponentCanonicalSigma_atLabel
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (i : Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent))
    (j : Fin (Fintype.card (equalityRemovedComponentAtLabel Q i))) :
    (⟨equalityRemovedComponentLabel Q (equalityRemovedComponentAtLabel Q i),
        equalityRemovedComponentCanonicalPosition hp Q ha
          (equalityRemovedComponentAtLabel Q i) j⟩ :
      Σ q : Fin (equalityAbstractContractedCore hp Q ha).2.links.linkCount.1,
        Fin ((equalityAbstractContractedCore hp Q ha).2.links.linkLength q).1) =
      ⟨i, ⟨j.1, by
        change j.1 < Fintype.card (equalityRemovedComponentAtLabel Q i)
        exact j.2⟩⟩ := by
  let hlabel := equalityRemovedComponentLabel_atLabel Q i
  apply Sigma.ext hlabel
  apply (Fin.heq_ext_iff (congrArg
    (fun q ↦ ((equalityAbstractContractedCore hp Q ha).2.links.linkLength q).1)
    hlabel)).mpr
  exact equalityRemovedComponentCanonicalPosition_val hp Q ha _ j

/-- The direct-port realization preserves its incident vertex label. -/
theorem equalityCanonicalDirectPortSourceHalfEdge_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalDirectPort (equalityAbstractContractedCore hp Q ha)) :
    equalityVertexEquivCanonicalExpandedVertex hp Q ha
        (equalityHalfEdgeVertex Q
          (equalityCanonicalDirectPortSourceHalfEdge hp Q ha z)) =
      canonicalExpandedPortVertex (Sum.inl z) := by
  let D := equalityDirectRetainedPortEquivCanonicalDirectPort hp Q ha
  let d := D.symm z
  have hz : D d = z := D.apply_symm_apply z
  change equalityVertexEquivCanonicalExpandedVertex hp Q ha
      (equalityHalfEdgeVertex Q d.1.2.1) = Sum.inl z.1.1
  rw [equalityVertexEquivCanonicalExpandedVertex_retainedPort hp Q ha d.1]
  have hzval := congrArg
    (fun q : CanonicalDirectPort
      (equalityAbstractContractedCore hp Q ha) ↦ q.1.1) hz
  exact congrArg Sum.inl hzval

/-- The link-segment realization preserves every retained or internal
incident vertex, including both outer boundaries. -/
theorem equalityCanonicalLinkSegmentSourceHalfEdge_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalLinkSegmentPort
      (equalityAbstractContractedCore hp Q ha)) :
    equalityVertexEquivCanonicalExpandedVertex hp Q ha
        (equalityHalfEdgeVertex Q
          (equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha z)) =
      canonicalExpandedPortVertex (Sum.inr z) := by
  rcases z with ⟨i, k, copy, b⟩
  change Fin (Fintype.card (equalityRemovedGraph Q).ConnectedComponent) at i
  let c := equalityRemovedComponentAtLabel Q i
  have hlen :
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 =
        Fintype.card c := by
    rfl
  have hcpos : 0 < Fintype.card c :=
    equalityRemovedComponent_card_pos Q c
  have hlenne :
      (equalityAbstractContractedCore hp Q ha).2.links.linkLength i ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero] at hval
    rw [hlen] at hval
    omega
  have hlenvalne :
      ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 ≠ 0 := by
    rw [hlen]
    omega
  by_cases hkzero : k.1 = 0
  · cases b
    · simp only [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
        ↓reduceDIte, equalitySourceLinkBoundaryHalfEdge]
      rw [equalityVertexEquivCanonicalExpandedVertex_retainedPort hp Q ha
        (equalitySourceLinkBoundaryPort hp Q ha ⟨i, 0, copy⟩)]
      simp only [canonicalExpandedPortVertex, hkzero, ↓reduceDIte]
      apply congrArg Sum.inl
      change (equalityRetainedPortsEquivContractedCorePort hp Q ha
        (equalitySourceLinkRetainedPort hp Q ha ⟨i, 0, copy⟩)).1 = _
      exact congrArg Sigma.fst
        (equalityRetainedPortsEquivContractedCorePort_sourceLink hp Q ha
          ⟨i, 0, copy⟩)
    · have hklt :
          k.1 <
            ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 := by
        rw [hkzero, hlen]
        exact hcpos
      simp only [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
        ↓reduceDIte]
      rw [equalitySourceLinkBoundaryHalfEdge_opposite_vertex]
      rw [← congrArg (fun w : c ↦ w.1.1)
        (equalityRemovedComponentFinEquiv_firstIndex hp Q ha c)]
      rw [equalityVertexEquivCanonicalExpandedVertex_removedPath]
      simp only [canonicalExpandedPortVertex, hklt, ↓reduceDIte]
      rw [equalityRemovedComponentCanonicalSigma_atLabel hp Q ha i]
      apply congrArg Sum.inr
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (by simp [hkzero])))
  · by_cases hklast :
        k.1 =
          ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
    · cases b
      · simp only [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
          hklast, hlenne, hlenvalne, ↓reduceDIte]
        rw [equalitySourceLinkBoundaryHalfEdge_opposite_vertex]
        rw [← congrArg (fun w : c ↦ w.1.1)
          (equalityRemovedComponentFinEquiv_lastIndex hp Q ha c)]
        rw [equalityVertexEquivCanonicalExpandedVertex_removedPath]
        simp only [canonicalExpandedPortVertex, hkzero, ↓reduceDIte]
        rw [equalityRemovedComponentCanonicalSigma_atLabel hp Q ha i]
        apply congrArg Sum.inr
        exact Sigma.ext rfl (heq_of_eq (Fin.ext (by
          simp [equalityRemovedComponentLastIndex_val]
          omega)))
      · simp only [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
          hklast, hlenne, hlenvalne, ↓reduceDIte,
          equalitySourceLinkBoundaryHalfEdge]
        rw [equalityVertexEquivCanonicalExpandedVertex_retainedPort hp Q ha
          (equalitySourceLinkBoundaryPort hp Q ha ⟨i, 1, copy⟩)]
        have hknotlt : ¬ k.1 <
            ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 := by
          omega
        simp only [canonicalExpandedPortVertex, hknotlt, ↓reduceDIte]
        apply congrArg Sum.inl
        change (equalityRetainedPortsEquivContractedCorePort hp Q ha
          (equalitySourceLinkRetainedPort hp Q ha ⟨i, 1, copy⟩)).1 = _
        exact congrArg Sigma.fst
          (equalityRetainedPortsEquivContractedCorePort_sourceLink hp Q ha
            ⟨i, 1, copy⟩)
    · have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hkzero
      have hklt : k.1 < Fintype.card c := by
        rw [← hlen]
        omega
      let j : Fin (Fintype.card c) := ⟨k.1 - 1, by omega⟩
      have hj : j.1 + 1 < Fintype.card c := by
        change k.1 - 1 + 1 < Fintype.card c
        omega
      cases b
      · simp only [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
          hklast, ↓reduceDIte]
        rw [equalityRemovedComponentInternalSegmentHalfEdge_false_vertex]
        rw [equalityVertexEquivCanonicalExpandedVertex_removedPath]
        simp only [canonicalExpandedPortVertex, hkzero, ↓reduceDIte]
        rw [equalityRemovedComponentCanonicalSigma_atLabel hp Q ha i]
      · simp only [equalityCanonicalLinkSegmentSourceHalfEdge, hkzero,
          hklast, ↓reduceDIte]
        rw [equalityRemovedComponentInternalSegmentHalfEdge_true_vertex]
        rw [equalityVertexEquivCanonicalExpandedVertex_removedPath]
        have hkltlen :
            k.1 <
              ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1 := by
          omega
        simp only [canonicalExpandedPortVertex, hkltlen, ↓reduceDIte]
        rw [equalityRemovedComponentCanonicalSigma_atLabel hp Q ha i]
        apply congrArg Sum.inr
        exact Sigma.ext rfl (heq_of_eq (Fin.ext (by
          simp [j]
          omega)))

set_option maxHeartbeats 800000 in
/-- Direct canonical edge reversal is original source half-edge reversal. -/
theorem equalityCanonicalDirectPortSourceHalfEdge_mate
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalDirectPort (equalityAbstractContractedCore hp Q ha)) :
    equalityCanonicalDirectPortSourceHalfEdge hp Q ha
        (canonicalDirectPortMate
          (equalityAbstractContractedCore_compatible hp Q ha) z) =
      equalityOppositeHalfEdge
        (equalityCanonicalDirectPortSourceHalfEdge hp Q ha z) := by
  let D := equalityDirectRetainedPortEquivCanonicalDirectPort hp Q ha
  let d := D.symm z
  have hz : D d = z := D.apply_symm_apply z
  have hmate :
      D (equalityDirectRetainedPortOpposite Q d) =
        canonicalDirectPortMate
          (equalityAbstractContractedCore_compatible hp Q ha) z := by
    rw [← hz]
    apply Subtype.ext
    change equalityRetainedPortsEquivContractedCorePort hp Q ha
        (equalityDirectRetainedPortOpposite Q d).1 =
      pairingMate
        (equalityStandardContractedPortPairing hp Q ha)
        (equalityRetainedPortsEquivContractedCorePort hp Q ha d.1) (by simp)
    have hpair : pairingMate
        (equalityStandardContractedPortPairing hp Q ha)
        (equalityRetainedPortsEquivContractedCorePort hp Q ha d.1) (by simp) =
      equalityStandardContractedPortOpposite hp Q ha
        (equalityRetainedPortsEquivContractedCorePort hp Q ha d.1) := by
      change pairingMate
          (pairingOfFixedPointFreeInvolution
            (equalityStandardContractedPortOpposite hp Q ha)
            (equalityStandardContractedPortOpposite_involutive hp Q ha)
            (equalityStandardContractedPortOpposite_ne hp Q ha))
          (equalityRetainedPortsEquivContractedCorePort hp Q ha d.1)
          (by simp) = _
      exact pairingMate_pairingOfFixedPointFreeInvolution _ _ _ _
    exact (equalityStandardContractedPortOpposite_direct hp Q ha d).symm.trans
      hpair.symm
  change ((D.symm (canonicalDirectPortMate
    (equalityAbstractContractedCore_compatible hp Q ha) z)).1.2.1) =
      equalityOppositeHalfEdge d.1.2.1
  rw [← hmate, D.symm_apply_apply]
  rfl

/-- Realize every canonical expanded port as its original indexed source
half-edge. -/
noncomputable def equalityCanonicalExpandedPortSourceHalfEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    CanonicalExpandedPort (equalityAbstractContractedCore hp Q ha) →
      EqualityHalfEdge p
  | Sum.inl z => equalityCanonicalDirectPortSourceHalfEdge hp Q ha z
  | Sum.inr z => equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha z

/-- The global realization preserves incident vertices. -/
theorem equalityCanonicalExpandedPortSourceHalfEdge_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalExpandedPort (equalityAbstractContractedCore hp Q ha)) :
    equalityVertexEquivCanonicalExpandedVertex hp Q ha
        (equalityHalfEdgeVertex Q
          (equalityCanonicalExpandedPortSourceHalfEdge hp Q ha z)) =
      canonicalExpandedPortVertex z := by
  rcases z with z | z
  · exact equalityCanonicalDirectPortSourceHalfEdge_vertex hp Q ha z
  · exact equalityCanonicalLinkSegmentSourceHalfEdge_vertex hp Q ha z

/-- The global realization intertwines the core-determined canonical edge
mate with original source half-edge reversal. -/
theorem equalityCanonicalExpandedPortSourceHalfEdge_edgeMate
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalExpandedPort (equalityAbstractContractedCore hp Q ha)) :
    equalityCanonicalExpandedPortSourceHalfEdge hp Q ha
        (canonicalExpandedEdgeMate
          (equalityAbstractContractedCore_compatible hp Q ha) z) =
      equalityOppositeHalfEdge
        (equalityCanonicalExpandedPortSourceHalfEdge hp Q ha z) := by
  rcases z with z | z
  · exact equalityCanonicalDirectPortSourceHalfEdge_mate hp Q ha z
  · exact equalityCanonicalLinkSegmentSourceHalfEdge_toggle hp Q ha z

/-- A direct source edge occurrence cannot also realize a positive-link
segment occurrence.  The latter has an internal endpoint because every stored
link length is positive, whereas both endpoints of a direct edge are retained. -/
theorem equalityCanonicalDirectPortSourceHalfEdge_ne_link
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : CanonicalDirectPort (equalityAbstractContractedCore hp Q ha))
    (w : CanonicalLinkSegmentPort (equalityAbstractContractedCore hp Q ha)) :
    equalityCanonicalDirectPortSourceHalfEdge hp Q ha z ≠
      equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha w := by
  intro hzw
  rcases w with ⟨i, k, copy, b⟩
  have hvert :
      canonicalExpandedPortVertex (Sum.inl z) =
        canonicalExpandedPortVertex (Sum.inr ⟨i, k, copy, b⟩) := by
    rw [← equalityCanonicalDirectPortSourceHalfEdge_vertex hp Q ha z]
    rw [← equalityCanonicalLinkSegmentSourceHalfEdge_vertex hp Q ha
      ⟨i, k, copy, b⟩]
    rw [hzw]
  have hedgeMate :
      equalityCanonicalDirectPortSourceHalfEdge hp Q ha
          (canonicalDirectPortMate
            (equalityAbstractContractedCore_compatible hp Q ha) z) =
        equalityCanonicalLinkSegmentSourceHalfEdge hp Q ha
          ⟨i, k, copy, !b⟩ := by
    rw [equalityCanonicalDirectPortSourceHalfEdge_mate]
    rw [equalityCanonicalLinkSegmentSourceHalfEdge_toggle hp Q ha
      ⟨i, k, copy, b⟩]
    rw [hzw]
  have hvertMateSource := congrArg
    (fun e : EqualityHalfEdge p ↦
      equalityVertexEquivCanonicalExpandedVertex hp Q ha
        (equalityHalfEdgeVertex Q e)) hedgeMate
  have hvertMate :
      canonicalExpandedPortVertex
          (Sum.inl (canonicalDirectPortMate
            (equalityAbstractContractedCore_compatible hp Q ha) z)) =
        canonicalExpandedPortVertex
          (Sum.inr ⟨i, k, copy, !b⟩) :=
    (equalityCanonicalDirectPortSourceHalfEdge_vertex hp Q ha _).symm.trans
      (hvertMateSource.trans
        (equalityCanonicalLinkSegmentSourceHalfEdge_vertex hp Q ha _))
  have hlenpos :=
    (equalityAbstractContractedCore hp Q ha).2.links.linkLength_pos i
  cases b
  · by_cases hkzero : k.1 = 0
    · simp [canonicalExpandedEdgeMate, canonicalExpandedPortVertex, hkzero,
        hlenpos] at hvertMate
    · simp [canonicalExpandedPortVertex, hkzero] at hvert
  · by_cases hklt :
        k.1 < ((equalityAbstractContractedCore hp Q ha).2.links.linkLength i).1
    · simp [canonicalExpandedPortVertex, hklt] at hvert
    · have hkzero : k.1 ≠ 0 := by omega
      simp [canonicalExpandedEdgeMate, canonicalExpandedPortVertex, hkzero]
        at hvertMate

/-- The complete canonical-to-source port realization is injective, including
across the direct and positive-link summands. -/
theorem equalityCanonicalExpandedPortSourceHalfEdge_injective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Injective
      (equalityCanonicalExpandedPortSourceHalfEdge hp Q ha) := by
  intro z w hzw
  rcases z with z | z <;> rcases w with w | w
  · exact congrArg Sum.inl
      (equalityCanonicalDirectPortSourceHalfEdge_injective hp Q ha hzw)
  · exact (equalityCanonicalDirectPortSourceHalfEdge_ne_link hp Q ha z w hzw).elim
  · exact (equalityCanonicalDirectPortSourceHalfEdge_ne_link hp Q ha w z hzw.symm).elim
  · exact congrArg Sum.inr
      (equalityCanonicalLinkSegmentSourceHalfEdge_injective hp Q ha hzw)

/-- Source half-edges split into the retained port fibers and four ports for
each removed (hence nonexceptional two-occurrence) vertex. -/
theorem equalityRetainedPorts_card_add_four_removed
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    Fintype.card (EqualityRetainedPorts Q) +
        4 * Fintype.card (EqualityRemovedVertex Q) =
      4 * p := by
  classical
  have hremovedBlock (u : EqualityRemovedVertex Q) : u.1.1.card = 2 := by
    have hlarge : ¬ 2 < u.1.1.card := by
      intro hlarge
      apply u.2
      simp only [equalityRetainedVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      apply Or.inl
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨u.1.2, hlarge⟩
    have htwo := Q.2.1 u.1.1 u.1.2
    omega
  have hvertexCardSum :
      (∑ u : EqualityVertex Q.1, u.1.card) = 2 * p := by
    calc
      (∑ u : EqualityVertex Q.1, u.1.card) =
          ∑ B ∈ Q.1.parts, B.card := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach Q.1.parts (fun B ↦ B.card)
      _ = 2 * p := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Q.1.sum_card_parts
  have htotal :
      (∑ u : EqualityVertex Q.1, 2 * u.1.card) = 4 * p := by
    rw [← Finset.mul_sum, hvertexCardSum]
    omega
  let removedFinset := (Finset.univ : Finset (EqualityVertex Q.1)).filter
    (fun u ↦ u ∉ equalityRetainedVertices Q)
  have hremovedFinsetCard :
      removedFinset.card = Fintype.card (EqualityRemovedVertex Q) := by
    simp only [removedFinset, EqualityRemovedVertex, Fintype.card_subtype]
  have hremovedSum :
      (∑ u ∈ removedFinset, 2 * u.1.card) =
        4 * Fintype.card (EqualityRemovedVertex Q) := by
    calc
      (∑ u ∈ removedFinset, 2 * u.1.card) =
          ∑ _u ∈ removedFinset, 4 := by
        apply Finset.sum_congr rfl
        intro u hu
        have hunretained : u ∉ equalityRetainedVertices Q :=
          (Finset.mem_filter.mp hu).2
        rw [hremovedBlock ⟨u, hunretained⟩]
      _ = removedFinset.card * 4 := by simp
      _ = 4 * removedFinset.card := by omega
      _ = 4 * Fintype.card (EqualityRemovedVertex Q) :=
        congrArg (4 * ·) hremovedFinsetCard
  have hretainedFilter :
      (Finset.univ : Finset (EqualityVertex Q.1)).filter
          (fun u ↦ u ∈ equalityRetainedVertices Q) =
        equalityRetainedVertices Q := by
    ext u
    simp
  rw [equalityRetainedPorts_card hp Q]
  calc
    (∑ u ∈ equalityRetainedVertices Q, 2 * u.1.card) +
          4 * Fintype.card (EqualityRemovedVertex Q) =
        (∑ u ∈ equalityRetainedVertices Q, 2 * u.1.card) +
          ∑ u ∈ removedFinset, 2 * u.1.card := by rw [hremovedSum]
    _ = ∑ u : EqualityVertex Q.1, 2 * u.1.card := by
      rw [← hretainedFilter]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    _ = 4 * p := htotal

#print axioms equalityStandardPort_isLinkPort_iff
#print axioms equalityDirectRetainedPortEquivCanonicalDirectPort
#print axioms equalityVertexEquivCanonicalExpandedVertex
#print axioms equalityCanonicalLinkSegmentSourceHalfEdge_toggle
#print axioms equalityCanonicalExpandedPortSourceHalfEdge_edgeMate
#print axioms equalityCanonicalLinkSegmentSourceHalfEdge_injective
#print axioms equalityCanonicalDirectPortSourceHalfEdge_ne_link
#print axioms equalityCanonicalExpandedPortSourceHalfEdge_injective
#print axioms equalityRetainedPorts_card_add_four_removed

end

end Problem56
