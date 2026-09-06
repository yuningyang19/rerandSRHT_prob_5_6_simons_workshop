import Problem56.ContractedCoreTransition

/-!
# Canonical expansion of a semantic contracted core

The semantic core determines a common finite port graph.  A direct retained
pair remains one edge.  Each designated positive link of length `ell` is
expanded into `ell + 1` doubled segments; the four outer segment ports replace
the four retained ports designated by the link.  Consequently two source
partitions with equal semantic cores have literally the same expanded vertex
and port types, rather than merely equicardinal source-dependent types.
-/

namespace Problem56

open scoped BigOperators

noncomputable section

/-- A retained core port is designated by a positive doubled link exactly
when it lies in the range of the link-port embedding. -/
def ContractedCoreTopology.IsLinkPort
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a}
    (T : ContractedCoreTopology c) (z : ContractedCorePort c) : Prop :=
  ∃ w : ContractedCoreLinkPortIndex T.links.linkCount.1,
    T.links.linkPorts w = z

/-- Retained ports belonging to direct (uncontracted) indexed edges. -/
def CanonicalDirectPort
    {p a : ℕ} (C : AbstractContractedCore p a) :=
  {z : ContractedCorePort C.1 // ¬ C.2.IsLinkPort z}

/-- Vertices of the canonical expansion: retained profile vertices followed
by the positive-length internal vertices of every designated link. -/
def CanonicalExpandedVertex
    {p a : ℕ} (C : AbstractContractedCore p a) :=
  Fin C.1.vertexCountCode.1 ⊕
    (Σ i : Fin C.2.links.linkCount.1,
      Fin (C.2.links.linkLength i).1)

/-- One canonical segment of link `i` is indexed from `0` through its stored
length.  It has two parallel copies and two endpoint ports. -/
def CanonicalLinkSegmentPort
    {p a : ℕ} (C : AbstractContractedCore p a) :=
  Σ i : Fin C.2.links.linkCount.1,
    Fin ((C.2.links.linkLength i).1 + 1) × Fin 2 × Bool

/-- Global ports of the expanded core.  Direct retained ports are kept once;
the designated boundary ports occur as the four outer ports of each doubled
link-chain rather than as separate retained-port summands. -/
def CanonicalExpandedPort
    {p a : ℕ} (C : AbstractContractedCore p a) :=
  CanonicalDirectPort C ⊕ CanonicalLinkSegmentPort C

noncomputable instance canonicalDirectPortFintype
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype (CanonicalDirectPort C) := by
  classical
  unfold CanonicalDirectPort ContractedCoreTopology.IsLinkPort
  infer_instance

noncomputable instance canonicalExpandedVertexFintype
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype (CanonicalExpandedVertex C) := by
  classical
  unfold CanonicalExpandedVertex
  infer_instance

noncomputable instance canonicalLinkSegmentPortFintype
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype (CanonicalLinkSegmentPort C) := by
  classical
  unfold CanonicalLinkSegmentPort
  infer_instance

noncomputable instance canonicalExpandedPortFintype
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype (CanonicalExpandedPort C) := by
  classical
  unfold CanonicalExpandedPort
  infer_instance

noncomputable instance canonicalExpandedVertexLinearOrder
    {p a : ℕ} (C : AbstractContractedCore p a) :
    LinearOrder (CanonicalExpandedVertex C) :=
  LinearOrder.lift' (Fintype.equivFin (CanonicalExpandedVertex C))
    (Fintype.equivFin (CanonicalExpandedVertex C)).injective

noncomputable instance canonicalExpandedPortLinearOrder
    {p a : ℕ} (C : AbstractContractedCore p a) :
    LinearOrder (CanonicalExpandedPort C) :=
  LinearOrder.lift' (Fintype.equivFin (CanonicalExpandedPort C))
    (Fintype.equivFin (CanonicalExpandedPort C)).injective

/-- The vertex incident to a canonical expanded port.  The left endpoint of
segment zero and the right endpoint of segment `ell` are retained vertices;
all other segment endpoints are the ordered internal vertices. -/
def canonicalExpandedPortVertex
    {p a : ℕ} {C : AbstractContractedCore p a} :
    CanonicalExpandedPort C → CanonicalExpandedVertex C
  | Sum.inl z => Sum.inl z.1.1
  | Sum.inr ⟨i, k, copy, false⟩ =>
      if hk : k.1 = 0 then
        Sum.inl (C.2.links.linkPorts ⟨i, 0, copy⟩).1
      else
        Sum.inr ⟨i, ⟨k.1 - 1, by
          have hklt := k.2
          omega⟩⟩
  | Sum.inr ⟨i, k, copy, true⟩ =>
      if hk : k.1 < (C.2.links.linkLength i).1 then
        Sum.inr ⟨i, ⟨k.1, hk⟩⟩
      else
        Sum.inl (C.2.links.linkPorts ⟨i, 1, copy⟩).1

/-- Ports incident to one vertex of the common canonical expansion. -/
def CanonicalExpandedPortsAt
    {p a : ℕ} (C : AbstractContractedCore p a)
    (v : CanonicalExpandedVertex C) :=
  {z : CanonicalExpandedPort C // canonicalExpandedPortVertex z = v}

noncomputable instance canonicalExpandedPortsAtFintype
    {p a : ℕ} (C : AbstractContractedCore p a)
    (v : CanonicalExpandedVertex C) :
    Fintype (CanonicalExpandedPortsAt C v) := by
  classical
  unfold CanonicalExpandedPortsAt
  infer_instance

noncomputable instance canonicalExpandedPortsAtLinearOrder
    {p a : ℕ} (C : AbstractContractedCore p a)
    (v : CanonicalExpandedVertex C) :
    LinearOrder (CanonicalExpandedPortsAt C v) :=
  LinearOrder.lift' (Fintype.equivFin (CanonicalExpandedPortsAt C v))
    (Fintype.equivFin (CanonicalExpandedPortsAt C v)).injective

/-- The sole compatibility condition needed to expand a counted topology:
its retained-port pairing pairs the two endpoint incidences of every
designated link, keeping the parallel-copy coordinate fixed. -/
structure CanonicalCoreCompatible
    {p a : ℕ} (C : AbstractContractedCore p a) : Prop where
  link_mate : ∀ w : ContractedCoreLinkPortIndex C.2.links.linkCount.1,
    pairingMate C.2.portPairing (C.2.links.linkPorts w) (by simp) =
      C.2.links.linkPorts ⟨w.1, Fin.rev w.2.1, w.2.2⟩

/-- The mate of a direct retained port is again direct whenever the link
designations agree with the retained-port pairing. -/
theorem canonicalDirectPort_mate_not_link
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) (z : CanonicalDirectPort C) :
    ¬ C.2.IsLinkPort
      (pairingMate C.2.portPairing z.1 (by simp)) := by
  intro hz
  rcases hz with ⟨w, hw⟩
  have hinv := pairingMate_involutive C.2.portPairing z.1 (by simp)
  have hmate := hC.link_mate w
  have hzrange : C.2.IsLinkPort z.1 := by
    refine ⟨⟨w.1, Fin.rev w.2.1, w.2.2⟩, ?_⟩
    calc
      C.2.links.linkPorts ⟨w.1, Fin.rev w.2.1, w.2.2⟩ =
          pairingMate C.2.portPairing (C.2.links.linkPorts w) (by simp) :=
        hmate.symm
      _ = pairingMate C.2.portPairing
          (pairingMate C.2.portPairing z.1 (by simp)) (by simp) := by
        rw [hw]
      _ = z.1 := hinv
  exact z.2 hzrange

/-- Direct retained-edge reversal recovered from the stored pairing. -/
def canonicalDirectPortMate
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) :
    CanonicalDirectPort C → CanonicalDirectPort C := fun z ↦
  ⟨pairingMate C.2.portPairing z.1 (by simp),
    canonicalDirectPort_mate_not_link hC z⟩

@[simp] theorem canonicalDirectPortMate_involutive
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) (z : CanonicalDirectPort C) :
    canonicalDirectPortMate hC (canonicalDirectPortMate hC z) = z := by
  apply Subtype.ext
  exact pairingMate_involutive C.2.portPairing z.1 (by simp)

theorem canonicalDirectPortMate_ne
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) (z : CanonicalDirectPort C) :
    canonicalDirectPortMate hC z ≠ z := by
  intro h
  exact pairingMate_ne C.2.portPairing z.1 (by simp)
    (congrArg Subtype.val h)

/-- Edge reversal on the canonical expansion.  On a chain segment it merely
toggles the endpoint side, so loops and the two parallel indexed copies remain
separate ports. -/
def canonicalExpandedEdgeMate
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) :
    CanonicalExpandedPort C → CanonicalExpandedPort C
  | Sum.inl z => Sum.inl (canonicalDirectPortMate hC z)
  | Sum.inr ⟨i, k, copy, b⟩ => Sum.inr ⟨i, k, copy, !b⟩

@[simp] theorem canonicalExpandedEdgeMate_involutive
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) (z : CanonicalExpandedPort C) :
    canonicalExpandedEdgeMate hC (canonicalExpandedEdgeMate hC z) = z := by
  rcases z with z | ⟨i, k, copy, b⟩
  · exact congrArg Sum.inl (canonicalDirectPortMate_involutive hC z)
  · cases b <;> rfl

theorem canonicalExpandedEdgeMate_ne
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C) (z : CanonicalExpandedPort C) :
    canonicalExpandedEdgeMate hC z ≠ z := by
  rcases z with z | ⟨i, k, copy, b⟩
  · intro h
    exact canonicalDirectPortMate_ne hC z (Sum.inl.inj h)
  · intro h
    have hb := congrArg
      (fun x : CanonicalLinkSegmentPort C ↦ x.2.2.2) (Sum.inr.inj h)
    simpa using hb

/-- Local Euler transitions on the common expanded core. -/
abbrev CanonicalLocalTransitionSystem
    {p a : ℕ} (C : AbstractContractedCore p a) :=
  (v : CanonicalExpandedVertex C) →
    FixedPointFreeInvolution (CanonicalExpandedPortsAt C v)

/-- The total space of vertex-indexed port fibers is canonically equivalent
to the global expanded-port type.  Using this equivalence makes transport
between dependent fibers explicit rather than relying on proof-term casts. -/
def canonicalExpandedPortFiberEquiv
    {p a : ℕ} {C : AbstractContractedCore p a} :
    (Σ v : CanonicalExpandedVertex C, CanonicalExpandedPortsAt C v) ≃
      CanonicalExpandedPort C where
  toFun z := z.2.1
  invFun z := ⟨canonicalExpandedPortVertex z, ⟨z, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨v, z, hz⟩
    subst hz
    rfl
  right_inv z := rfl

/-- Apply the vertexwise transition on the total fiber space. -/
def canonicalLocalTransitionFiberMate
    {p a : ℕ} {C : AbstractContractedCore p a}
    (T : CanonicalLocalTransitionSystem C) :
    (Σ v : CanonicalExpandedVertex C, CanonicalExpandedPortsAt C v) →
      (Σ v : CanonicalExpandedVertex C, CanonicalExpandedPortsAt C v)
  | ⟨v, z⟩ => ⟨v, (T v).1 z⟩

@[simp] theorem canonicalLocalTransitionFiberMate_involutive
    {p a : ℕ} {C : AbstractContractedCore p a}
    (T : CanonicalLocalTransitionSystem C)
    (z : Σ v : CanonicalExpandedVertex C, CanonicalExpandedPortsAt C v) :
    canonicalLocalTransitionFiberMate T
      (canonicalLocalTransitionFiberMate T z) = z := by
  rcases z with ⟨v, z⟩
  change Sigma.mk v ((T v).1 ((T v).1 z)) = Sigma.mk v z
  rw [(T v).2.1 z]

/-- Apply a local transition to a global canonical port. -/
def canonicalLocalTransitionMate
    {p a : ℕ} {C : AbstractContractedCore p a}
    (T : CanonicalLocalTransitionSystem C) :
    CanonicalExpandedPort C → CanonicalExpandedPort C := fun z ↦
  canonicalExpandedPortFiberEquiv
    (canonicalLocalTransitionFiberMate T
      (canonicalExpandedPortFiberEquiv.symm z))

@[simp] theorem canonicalLocalTransitionMate_vertex
    {p a : ℕ} {C : AbstractContractedCore p a}
    (T : CanonicalLocalTransitionSystem C) (z : CanonicalExpandedPort C) :
    canonicalExpandedPortVertex (canonicalLocalTransitionMate T z) =
      canonicalExpandedPortVertex z := by
  change canonicalExpandedPortVertex
      (((T (canonicalExpandedPortVertex z)).1 ⟨z, rfl⟩).1) =
    canonicalExpandedPortVertex z
  exact ((T (canonicalExpandedPortVertex z)).1 ⟨z, rfl⟩).2

@[simp] theorem canonicalLocalTransitionMate_involutive
    {p a : ℕ} {C : AbstractContractedCore p a}
    (T : CanonicalLocalTransitionSystem C) (z : CanonicalExpandedPort C) :
    canonicalLocalTransitionMate T (canonicalLocalTransitionMate T z) = z := by
  change canonicalExpandedPortFiberEquiv
      (canonicalLocalTransitionFiberMate T
        (canonicalExpandedPortFiberEquiv.symm
          (canonicalExpandedPortFiberEquiv
            (canonicalLocalTransitionFiberMate T
              (canonicalExpandedPortFiberEquiv.symm z))))) = z
  rw [canonicalExpandedPortFiberEquiv.symm_apply_apply,
    canonicalLocalTransitionFiberMate_involutive,
    canonicalExpandedPortFiberEquiv.apply_symm_apply]

theorem canonicalLocalTransitionMate_ne
    {p a : ℕ} {C : AbstractContractedCore p a}
    (T : CanonicalLocalTransitionSystem C) (z : CanonicalExpandedPort C) :
    canonicalLocalTransitionMate T z ≠ z := by
  intro h
  exact (T (canonicalExpandedPortVertex z)).2.2 ⟨z, rfl⟩
    (Subtype.ext h)

/-- One forward Euler step crosses an indexed edge and then takes the stored
local transition at the arrival vertex. -/
def canonicalEulerStep
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C)
    (T : CanonicalLocalTransitionSystem C) :
    CanonicalExpandedPort C → CanonicalExpandedPort C :=
  canonicalLocalTransitionMate T ∘ canonicalExpandedEdgeMate hC

/-- The canonical vertex word read from a starting port and transition
system. -/
def canonicalEulerVertexAt
    {p a : ℕ} {C : AbstractContractedCore p a}
    (hC : CanonicalCoreCompatible C)
    (T : CanonicalLocalTransitionSystem C)
    (start : CanonicalExpandedPort C) (k : ℕ) :
    CanonicalExpandedVertex C :=
  canonicalExpandedPortVertex ((canonicalEulerStep hC T)^[k] start)

#print axioms canonicalDirectPort_mate_not_link
#print axioms canonicalDirectPortMate_involutive
#print axioms canonicalDirectPortMate_ne
#print axioms canonicalExpandedEdgeMate_involutive
#print axioms canonicalExpandedEdgeMate_ne
#print axioms canonicalLocalTransitionMate_vertex
#print axioms canonicalLocalTransitionMate_involutive
#print axioms canonicalLocalTransitionMate_ne

end

end Problem56
