import Problem56.ContractedCoreCanonicalCount
import Problem56.ContractedCoreWordReconstruction

/-!
# Source realizations and bounded canonical Euler data

This module records the exact interface needed to transport the cyclic
half-edge dynamics of a source equality partition to a canonical expanded
core.  It is deliberately independent of the geometric construction of the
realization: positive-parameter link contraction and the zero-parameter
cycle/path classification can supply the same interface without duplicating
the ensuing fiber and counting arguments.
-/

namespace Problem56

open scoped BigOperators

noncomputable section

/-- A source equality multigraph realized on one compatible canonical expanded
core.  Both equivalences retain indexed half-edge ports, so loops and parallel
occurrences remain distinct. -/
structure CanonicalSourceRealizationData
    {p s t a : ℕ} (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a) where
  compatible : CanonicalCoreCompatible C
  portEquiv : EqualityHalfEdge p ≃ CanonicalExpandedPort C
  vertexEquiv : EqualityVertex Q.1 ≃ CanonicalExpandedVertex C
  port_vertex : ∀ h : EqualityHalfEdge p,
    canonicalExpandedPortVertex (portEquiv h) =
      vertexEquiv (equalityHalfEdgeVertex Q h)
  opposite : ∀ h : EqualityHalfEdge p,
    portEquiv (equalityOppositeHalfEdge h) =
      canonicalExpandedEdgeMate compatible (portEquiv h)

/-- The global port realization restricts to corresponding incident-port
fibers. -/
def canonicalSourcePortsAtEquiv
    {p s t a : ℕ} {Q : SelectorEqualityData p s t}
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C) (u : EqualityVertex Q.1) :
    EqualityPortsAt Q u ≃
      CanonicalExpandedPortsAt C (R.vertexEquiv u) where
  toFun h := ⟨R.portEquiv h.1, by
    rw [R.port_vertex, h.2]⟩
  invFun z := ⟨R.portEquiv.symm z.1, by
    apply R.vertexEquiv.injective
    rw [← R.port_vertex, R.portEquiv.apply_symm_apply]
    exact z.2⟩
  left_inv h := by
    apply Subtype.ext
    exact R.portEquiv.symm_apply_apply h.1
  right_inv z := by
    apply Subtype.ext
    exact R.portEquiv.apply_symm_apply z.1

/-- Fiber form indexed by a canonical vertex. -/
def canonicalSourcePortsAtCanonicalVertexEquiv
    {p s t a : ℕ} {Q : SelectorEqualityData p s t}
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C)
    (v : CanonicalExpandedVertex C) :
    EqualityPortsAt Q (R.vertexEquiv.symm v) ≃
      CanonicalExpandedPortsAt C v where
  toFun h := ⟨R.portEquiv h.1, by
    rw [R.port_vertex, h.2, R.vertexEquiv.apply_symm_apply]⟩
  invFun z := ⟨R.portEquiv.symm z.1, by
    apply R.vertexEquiv.injective
    rw [R.vertexEquiv.apply_symm_apply, ← R.port_vertex,
      R.portEquiv.apply_symm_apply]
    exact z.2⟩
  left_inv h := by
    apply Subtype.ext
    exact R.portEquiv.symm_apply_apply h.1
  right_inv z := by
    apply Subtype.ext
    exact R.portEquiv.apply_symm_apply z.1

/-- Every source realization carries the exact source cardinal and transition
excess bounds required by the canonical counting theorem. -/
theorem canonicalSourceBounds_of_realization
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C)
    (ha : s ≤ a) : CanonicalSourceBounds C := by
  classical
  refine
    { expandedPort_card_le := ?_
      expandedVertex_card_le := ?_
      port_card_le := ?_
      port_card_pos := ?_
      port_card_even := ?_
      excess_sum_le := ?_ }
  · rw [← Fintype.card_congr R.portEquiv, equalityHalfEdge_card]
    omega
  · rw [← Fintype.card_congr R.vertexEquiv, equalityVertex_card]
    omega
  · intro v
    rw [← Fintype.card_congr
      (canonicalSourcePortsAtCanonicalVertexEquiv R v)]
    exact equalityPortsAt_card_le_coreBase hp Q _
  · intro v
    rw [← Fintype.card_congr
      (canonicalSourcePortsAtCanonicalVertexEquiv R v)]
    exact equalityPortsAt_card_pos hp Q _
  · intro v
    rw [← Fintype.card_congr
      (canonicalSourcePortsAtCanonicalVertexEquiv R v)]
    exact equalityPortsAt_card_even hp Q _
  · have hsum :
        (∑ v : CanonicalExpandedVertex C,
          (Fintype.card (CanonicalExpandedPortsAt C v) - 4) / 2) =
        ∑ u : EqualityVertex Q.1,
          (Fintype.card (EqualityPortsAt Q u) - 4) / 2 := by
      calc
        (∑ v : CanonicalExpandedVertex C,
            (Fintype.card (CanonicalExpandedPortsAt C v) - 4) / 2) =
            ∑ u : EqualityVertex Q.1,
              (Fintype.card
                (CanonicalExpandedPortsAt C (R.vertexEquiv u)) - 4) / 2 :=
          (Equiv.sum_comp R.vertexEquiv
            (fun v : CanonicalExpandedVertex C ↦
              (Fintype.card (CanonicalExpandedPortsAt C v) - 4) / 2)).symm
        _ = ∑ u : EqualityVertex Q.1,
              (Fintype.card (EqualityPortsAt Q u) - 4) / 2 := by
          apply Finset.sum_congr rfl
          intro u _
          rw [← Fintype.card_congr (canonicalSourcePortsAtEquiv R u)]
    rw [hsum, equalityPortsAt_transitionExcess_sum hp Q]
    omega

/-! ## Transporting the started cyclic dynamics -/

/-- Conjugate fixed-point-free involution data through an equivalence. -/
def fixedPointFreeInvolutionTransport
    {α β : Type*} (e : α ≃ β) :
    FixedPointFreeInvolution α → FixedPointFreeInvolution β := fun f ↦
  ⟨fun y ↦ e (f.1 (e.symm y)), by
    constructor
    · intro y
      simp only [e.symm_apply_apply]
      rw [f.2.1]
      exact e.apply_symm_apply y
    · intro y hEq
      have hpre := congrArg e.symm hEq
      simp only [e.symm_apply_apply] at hpre
      exact f.2.2 (e.symm y) hpre⟩

/-- Source cyclic transition as a global half-edge operation.  It is independent
of the partition; the partition is used only to prove that the operation stays
inside one incident-port fiber. -/
noncomputable def equalityCyclicTransitionMate
    {p s t : ℕ} (hp : 2 ≤ p) (_Q : SelectorEqualityData p s t) :
    EqualityHalfEdge p → EqualityHalfEdge p := fun h ↦ by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rcases h with ⟨e, b⟩
  cases b
  · exact ((cyclicSuccEquiv (2 * p)).symm e, true)
  · exact (cyclicSucc e, false)

@[simp] theorem equalityCyclicTransitionMate_target
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (i : Fin (2 * p)) :
  equalityCyclicTransitionMate hp Q (i, true) =
      (cyclicSucc i, false) := by
  rfl

@[simp] theorem equalityCyclicTransitionMate_involutive
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    Function.Involutive (equalityCyclicTransitionMate hp Q) := by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rintro ⟨e, b⟩
  cases b
  · apply Prod.ext
    · simp only [equalityCyclicTransitionMate]
      change cyclicSucc ((cyclicSuccEquiv (2 * p)).symm e) = e
      rw [← cyclicSuccEquiv_apply,
        (cyclicSuccEquiv (2 * p)).apply_symm_apply]
    · rfl
  · apply Prod.ext
    · simp only [equalityCyclicTransitionMate]
      change (cyclicSuccEquiv (2 * p)).symm (cyclicSucc e) = e
      rw [← cyclicSuccEquiv_apply,
        (cyclicSuccEquiv (2 * p)).symm_apply_apply]
    · rfl

theorem equalityCyclicTransitionMate_ne
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (h : EqualityHalfEdge p) : equalityCyclicTransitionMate hp Q h ≠ h := by
  rcases h with ⟨e, b⟩
  cases b <;> intro hEq
  · have hb := congrArg Prod.snd hEq
    simp [equalityCyclicTransitionMate] at hb
  · have hb := congrArg Prod.snd hEq
    simp [equalityCyclicTransitionMate] at hb

@[simp] theorem equalityCyclicTransitionMate_vertex
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (h : EqualityHalfEdge p) :
    equalityHalfEdgeVertex Q (equalityCyclicTransitionMate hp Q h) =
      equalityHalfEdgeVertex Q h := by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rcases h with ⟨e, b⟩
  cases b
  · simp only [equalityCyclicTransitionMate, equalityHalfEdgeVertex,
      equalityEdgeDst, equalityEdgeSrc]
    congr 1
    change cyclicSucc ((cyclicSuccEquiv (2 * p)).symm e) = e
    rw [← cyclicSuccEquiv_apply,
      (cyclicSuccEquiv (2 * p)).apply_symm_apply]
  · rfl

/-- Global transported local mate on the canonical port type. -/
noncomputable def canonicalTransitionMateOfRealization
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C) :
    CanonicalExpandedPort C → CanonicalExpandedPort C := fun z ↦
  R.portEquiv (equalityCyclicTransitionMate hp Q (R.portEquiv.symm z))

@[simp] theorem canonicalTransitionMateOfRealization_vertex
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C)
    (z : CanonicalExpandedPort C) :
    canonicalExpandedPortVertex
        (canonicalTransitionMateOfRealization hp Q R z) =
      canonicalExpandedPortVertex z := by
  calc
    canonicalExpandedPortVertex
        (canonicalTransitionMateOfRealization hp Q R z) =
        R.vertexEquiv (equalityHalfEdgeVertex Q
          (equalityCyclicTransitionMate hp Q (R.portEquiv.symm z))) :=
      R.port_vertex _
    _ = R.vertexEquiv
        (equalityHalfEdgeVertex Q (R.portEquiv.symm z)) := by
      rw [equalityCyclicTransitionMate_vertex]
    _ = canonicalExpandedPortVertex
        (R.portEquiv (R.portEquiv.symm z)) := (R.port_vertex _).symm
    _ = canonicalExpandedPortVertex z := by
      rw [R.portEquiv.apply_symm_apply]

@[simp] theorem canonicalTransitionMateOfRealization_involutive
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C) :
    Function.Involutive (canonicalTransitionMateOfRealization hp Q R) := by
  intro z
  simp only [canonicalTransitionMateOfRealization,
    R.portEquiv.symm_apply_apply]
  rw [equalityCyclicTransitionMate_involutive,
    R.portEquiv.apply_symm_apply]

theorem canonicalTransitionMateOfRealization_ne
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C)
    (z : CanonicalExpandedPort C) :
    canonicalTransitionMateOfRealization hp Q R z ≠ z := by
  intro hEq
  have hpre := congrArg R.portEquiv.symm hEq
  simp only [canonicalTransitionMateOfRealization,
    R.portEquiv.symm_apply_apply] at hpre
  exact equalityCyclicTransitionMate_ne hp Q (R.portEquiv.symm z) hpre

/-- The original cyclic transition, transported independently on every
canonical vertex fiber. -/
noncomputable def canonicalLocalTransitionOfRealization
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C) :
    CanonicalLocalTransitionSystem C := fun _v ↦
  ⟨fun z ↦ ⟨canonicalTransitionMateOfRealization hp Q R z.1,
      (canonicalTransitionMateOfRealization_vertex hp Q R z.1).trans z.2⟩,
    by
      constructor
      · intro z
        apply Subtype.ext
        exact canonicalTransitionMateOfRealization_involutive hp Q R z.1
      · intro z hEq
        exact canonicalTransitionMateOfRealization_ne hp Q R z.1
          (congrArg Subtype.val hEq)⟩

/-- Evaluation of the transported global local mate. -/
theorem canonicalLocalTransitionOfRealization_mate
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C)
    (h : EqualityHalfEdge p) :
    canonicalLocalTransitionMate
        (canonicalLocalTransitionOfRealization hp Q C R) (R.portEquiv h) =
      R.portEquiv (equalityCyclicTransitionMate hp Q h) := by
  change canonicalTransitionMateOfRealization hp Q R (R.portEquiv h) = _
  simp [canonicalTransitionMateOfRealization]

/-- Canonical port visited at a source occurrence. -/
def canonicalTailOfRealization
    {p s t a : ℕ} {Q : SelectorEqualityData p s t}
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C) (i : Fin (2 * p)) :
    CanonicalExpandedPort C := R.portEquiv (i, false)

/-- One canonical edge reversal followed by the transported local transition
advances the source cyclic occurrence. -/
theorem canonicalTailOfRealization_next
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C) (i : Fin (2 * p)) :
    canonicalTailOfRealization R (cyclicSucc i) =
      canonicalEulerStep R.compatible
        (canonicalLocalTransitionOfRealization hp Q C R)
        (canonicalTailOfRealization R i) := by
  rw [canonicalTailOfRealization, canonicalTailOfRealization,
    canonicalEulerStep, Function.comp_apply, ← R.opposite]
  exact (canonicalLocalTransitionOfRealization_mate hp Q C R
    (equalityOppositeHalfEdge (i, false))).symm

/-- The transported source tail is the finite iterate generated by its encoded
start and canonical Euler step. -/
theorem canonicalTailOfRealization_eq_iterate
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C) (i : Fin (2 * p)) :
    canonicalTailOfRealization R i =
      ((canonicalEulerStep R.compatible
        (canonicalLocalTransitionOfRealization hp Q C R))^[i.1])
          (canonicalTailOfRealization R ⟨0, by omega⟩) := by
  let step := canonicalEulerStep R.compatible
    (canonicalLocalTransitionOfRealization hp Q C R)
  let start := canonicalTailOfRealization R ⟨0, by omega⟩
  generalize hn : i.1 = n
  induction n generalizing i with
  | zero =>
      have hi : i = ⟨0, by omega⟩ := Fin.ext hn
      rw [hi]
      simp
  | succ n ih =>
      have hn1lt : n + 1 < 2 * p := by omega
      have hnlt : n < 2 * p := by omega
      let j : Fin (2 * p) := ⟨n, hnlt⟩
      have hcyclic : cyclicSucc j = i := by
        apply Fin.ext
        simp only [cyclicSucc, j]
        rw [Nat.mod_eq_of_lt hn1lt]
        exact hn.symm
      calc
        canonicalTailOfRealization R i =
            canonicalTailOfRealization R (cyclicSucc j) :=
          congrArg (canonicalTailOfRealization R) hcyclic.symm
        _ = step (canonicalTailOfRealization R j) :=
          canonicalTailOfRealization_next hp Q C R j
        _ = step ((step^[j.1]) start) := congrArg step (ih j rfl)
        _ = ((canonicalEulerStep R.compatible
              (canonicalLocalTransitionOfRealization hp Q C R))^[n + 1])
              (canonicalTailOfRealization R ⟨0, by omega⟩) := by
          simp only [step, start, j]
          exact (Function.iterate_succ_apply'
            (canonicalEulerStep R.compatible
              (canonicalLocalTransitionOfRealization hp Q C R)) n
            (canonicalTailOfRealization R ⟨0, by omega⟩)).symm

/-- The source partition classes are exactly the canonical vertices visited by
the transported occurrence tails. -/
theorem canonicalTailOfRealization_class_iff
    {p s t a : ℕ} {Q : SelectorEqualityData p s t}
    {C : AbstractContractedCore p a}
    (R : CanonicalSourceRealizationData Q C) (i j : Fin (2 * p)) :
    Q.1.part i = Q.1.part j ↔
      canonicalExpandedPortVertex (canonicalTailOfRealization R i) =
        canonicalExpandedPortVertex (canonicalTailOfRealization R j) := by
  rw [canonicalTailOfRealization, canonicalTailOfRealization,
    R.port_vertex, R.port_vertex]
  constructor
  · intro hij
    apply congrArg R.vertexEquiv
    apply Subtype.ext
    exact hij
  · intro hij
    exact congrArg Subtype.val (R.vertexEquiv.injective hij)

/-! ## A decoder-bearing injectivity wrapper -/

/-- Bounded canonical data together with the compatible edge-mate law needed
to read its Euler vertex word.  Compatibility is a proposition and therefore
adds no counting cost; forgetting it is an embedding into the counted type. -/
abbrev CompatibleBoundedCanonicalEqualityData (p a : ℕ) :=
  {D : BoundedCanonicalEqualityData p a //
    CanonicalCoreCompatible D.1}

/-- The equivalence relation on cyclic positions obtained by reading the
canonical Euler vertex word. -/
def canonicalDynamicsSetoid {p a : ℕ}
    (D : CompatibleBoundedCanonicalEqualityData p a) : Setoid (Fin (2 * p)) where
  r i j :=
    canonicalEulerVertexAt D.2 D.1.2.1.2 D.1.2.1.1 i.1 =
      canonicalEulerVertexAt D.2 D.1.2.1.2 D.1.2.1.1 j.1
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Decode the partition determined by the canonical Euler vertex word. -/
noncomputable def canonicalDynamicsPartition {p a : ℕ}
    (D : CompatibleBoundedCanonicalEqualityData p a) :
    Finpartition (Finset.univ : Finset (Fin (2 * p))) := by
  classical
  exact Finpartition.ofSetoid (canonicalDynamicsSetoid D)

/-- Package one realized source partition as bounded compatible canonical
Euler data. -/
noncomputable def compatibleBoundedCanonicalDataOfRealization
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C) (ha : s ≤ a) :
    CompatibleBoundedCanonicalEqualityData p a :=
  ⟨⟨C, ⟨(canonicalTailOfRealization R ⟨0, by omega⟩,
      canonicalLocalTransitionOfRealization hp Q C R),
    canonicalSourceBounds_of_realization hp Q C R ha⟩⟩,
    R.compatible⟩

/-- Decoding a realized canonical Euler word recovers the source partition
exactly. -/
theorem canonicalDynamicsPartition_dataOfRealization
    {p s t a : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (C : AbstractContractedCore p a)
    (R : CanonicalSourceRealizationData Q C) (ha : s ≤ a) :
    canonicalDynamicsPartition
        (compatibleBoundedCanonicalDataOfRealization hp Q C R ha) = Q.1 := by
  classical
  let D := compatibleBoundedCanonicalDataOfRealization hp Q C R ha
  have hpart : ∀ i : Fin (2 * p),
      (canonicalDynamicsPartition D).part i = Q.1.part i := by
    intro i
    ext j
    change j ∈ (Finpartition.ofSetoid
        (canonicalDynamicsSetoid D)).part i ↔ j ∈ Q.1.part i
    rw [Finpartition.mem_part_ofSetoid_iff_rel]
    change canonicalExpandedPortVertex
        (((canonicalEulerStep R.compatible
          (canonicalLocalTransitionOfRealization hp Q C R))^[i.1])
            (canonicalTailOfRealization R ⟨0, by omega⟩)) =
      canonicalExpandedPortVertex
        (((canonicalEulerStep R.compatible
          (canonicalLocalTransitionOfRealization hp Q C R))^[j.1])
            (canonicalTailOfRealization R ⟨0, by omega⟩)) ↔
      j ∈ Q.1.part i
    rw [← canonicalTailOfRealization_eq_iterate hp Q C R i,
      ← canonicalTailOfRealization_eq_iterate hp Q C R j,
      ← canonicalTailOfRealization_class_iff R i j]
    simpa only [eq_comm] using
      (Q.1.mem_part_iff_part_eq_part
        (Finset.mem_univ j) (Finset.mem_univ i)).symm
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi⟩ :=
      (canonicalDynamicsPartition D).nonempty_of_mem_parts hB
    rw [← (canonicalDynamicsPartition D).part_eq_of_mem hB hi, hpart i]
    exact Q.1.part_mem.mpr (Finset.mem_univ i)
  · intro hB
    obtain ⟨i, hi⟩ := Q.1.nonempty_of_mem_parts hB
    rw [← Q.1.part_eq_of_mem hB hi, ← hpart i]
    exact (canonicalDynamicsPartition D).part_mem.mpr (Finset.mem_univ i)

/-- A realization for every source object gives an injection into the bounded
canonical data counted by the public Euler budget.  Injectivity is witnessed by
the canonical-dynamics decoder, so it is independent of arbitrary choices made
inside the geometric realizations. -/
noncomputable def boundedCanonicalInjectionOfRealizations
    {p s t a : ℕ} (hp : 2 ≤ p)
    (core : SelectorEqualityData p s t → AbstractContractedCore p a)
    (realize : ∀ Q : SelectorEqualityData p s t,
      CanonicalSourceRealizationData Q (core Q))
    (ha : s ≤ a) :
    SelectorEqualityData p s t ↪ BoundedCanonicalEqualityData p a where
  toFun Q :=
    (compatibleBoundedCanonicalDataOfRealization hp Q (core Q)
      (realize Q) ha).1
  inj' := by
    intro Q R hdata
    let DQ := compatibleBoundedCanonicalDataOfRealization hp Q (core Q)
      (realize Q) ha
    let DR := compatibleBoundedCanonicalDataOfRealization hp R (core R)
      (realize R) ha
    have hcompatible : DQ = DR := by
      apply Subtype.ext
      exact hdata
    have hdecoded := congrArg canonicalDynamicsPartition hcompatible
    have hQ := canonicalDynamicsPartition_dataOfRealization hp Q (core Q)
      (realize Q) ha
    have hR := canonicalDynamicsPartition_dataOfRealization hp R (core R)
      (realize R) ha
    apply Subtype.ext
    exact hQ.symm.trans (hdecoded.trans hR)

/-- Realizations on any chosen `(s+t)`-budget cores discharge the full public
contracted-core/Euler encoding bound. -/
theorem contracted_core_encoding_bound_of_realizations
    {p s t : ℕ} (hp : 2 ≤ p)
    (core : SelectorEqualityData p s t →
      AbstractContractedCore p (s + t))
    (realize : ∀ Q : SelectorEqualityData p s t,
      CanonicalSourceRealizationData Q (core Q)) :
    Fintype.card (ContractedCoreCode p (s + t)) ≤
        (4 * p + 1) ^ (72 * (s + t)) ∧
      Nonempty (EqualityEncoding p s t) :=
  contracted_core_encoding_bound_of_boundedCanonicalInjection
    (boundedCanonicalInjectionOfRealizations hp core realize (by omega))

/-! ## Fixed-core use of a direct Euler-code injection -/

/-- Adjoin one fixed contracted-core code to an injective Euler-code map. -/
noncomputable def fullEqualityCodeInjectionOfEulerInjection
    {p s t : ℕ} (c : ContractedCoreCode p (s + t))
    (f : SelectorEqualityData p s t ↪ EulerTransitionCode p (s + t)) :
    SelectorEqualityData p s t ↪ FullEqualityCode p (s + t) where
  toFun Q := ⟨c, f Q⟩
  inj' := by
    intro Q R h
    apply f.injective
    exact congrArg Sigma.snd h

/-- A direct Euler-code injection, together with any fixed core code, supplies
the public decoder-bearing encoding. -/
theorem equalityEncoding_nonempty_of_eulerInjection
    {p s t : ℕ} (c : ContractedCoreCode p (s + t))
    (f : SelectorEqualityData p s t ↪ EulerTransitionCode p (s + t)) :
    Nonempty (EqualityEncoding p s t) :=
  ⟨equalityEncodingOfInjective
    (fullEqualityCodeInjectionOfEulerInjection c f)
    (fullEqualityCodeInjectionOfEulerInjection c f).injective⟩

/-- The unique zero-budget contracted-core code. -/
def zeroParameterContractedCoreCode (p : ℕ) : ContractedCoreCode p 0 where
  vertexDegreeChoice := ⟨0, by simp⟩
  degreeVector := fun i ↦ Fin.elim0 i
  halfEdgePairing := fun i ↦ Fin.elim0 i
  doubledLinkPorts := fun i ↦ Fin.elim0 i
  linkLengths := fun i ↦ Fin.elim0 i

/-- A zero-parameter Euler injection closes both advertised I20 outputs. -/
theorem contracted_core_encoding_bound_zero_of_eulerInjection
    {p : ℕ}
    (f : SelectorEqualityData p 0 0 ↪ EulerTransitionCode p 0) :
    Fintype.card (ContractedCoreCode p 0) ≤
        (4 * p + 1) ^ (72 * 0) ∧
      Nonempty (EqualityEncoding p 0 0) :=
  ⟨contracted_core_code_card_bound p 0 0,
    equalityEncoding_nonempty_of_eulerInjection
      (zeroParameterContractedCoreCode p) f⟩

#print axioms canonicalSourcePortsAtEquiv
#print axioms canonicalSourcePortsAtCanonicalVertexEquiv
#print axioms canonicalSourceBounds_of_realization
#print axioms fixedPointFreeInvolutionTransport
#print axioms equalityCyclicTransitionMate_target
#print axioms equalityCyclicTransitionMate_vertex
#print axioms canonicalLocalTransitionOfRealization
#print axioms canonicalLocalTransitionOfRealization_mate
#print axioms canonicalTailOfRealization_next
#print axioms canonicalTailOfRealization_class_iff
#print axioms canonicalTailOfRealization_eq_iterate
#print axioms canonicalDynamicsPartition_dataOfRealization
#print axioms boundedCanonicalInjectionOfRealizations
#print axioms contracted_core_encoding_bound_of_realizations
#print axioms equalityEncoding_nonempty_of_eulerInjection
#print axioms contracted_core_encoding_bound_zero_of_eulerInjection

end

end Problem56
