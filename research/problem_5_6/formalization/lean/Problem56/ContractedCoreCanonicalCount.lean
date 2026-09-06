import Problem56.ContractedCoreCanonical
import Problem56.ContractedCoreAbstractCode

/-!
# Counting source-realizable canonical Euler data

An arbitrary semantic contracted core may have many more expanded vertices
than a source equality partition.  The encoder therefore carries the sharp
source bounds as a proposition on its canonical payload.  This file proves a
uniform cardinality estimate for precisely those bounded payloads; no source
partition or decoder is used here.
-/

namespace Problem56

open scoped BigOperators

noncomputable section

/-- Numerical bounds enjoyed by a canonical expansion that comes from a
`2p`-occurrence equality partition with exceptional parameter `a`. -/
structure CanonicalSourceBounds {p a : ℕ}
    (C : AbstractContractedCore p a) : Prop where
  expandedPort_card_le : Fintype.card (CanonicalExpandedPort C) ≤ 8 * p
  expandedVertex_card_le : Fintype.card (CanonicalExpandedVertex C) ≤ p
  port_card_le : ∀ v : CanonicalExpandedVertex C,
    Fintype.card (CanonicalExpandedPortsAt C v) ≤ 4 * p + 1
  port_card_pos : ∀ v : CanonicalExpandedVertex C,
    0 < Fintype.card (CanonicalExpandedPortsAt C v)
  port_card_even : ∀ v : CanonicalExpandedVertex C,
    Even (Fintype.card (CanonicalExpandedPortsAt C v))
  excess_sum_le :
    (∑ v : CanonicalExpandedVertex C,
      (Fintype.card (CanonicalExpandedPortsAt C v) - 4) / 2) ≤ 2 * a

/-- A started local transition system on a source-realizable canonical core.
The proof component is subsingleton data and has no counting cost. -/
abbrev BoundedCanonicalPayload {p a : ℕ}
    (C : AbstractContractedCore p a) :=
  {d : CanonicalExpandedPort C × CanonicalLocalTransitionSystem C //
    CanonicalSourceBounds C}

noncomputable instance boundedCanonicalPayloadFintype
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype (BoundedCanonicalPayload C) :=
  Fintype.ofFinite _

/-- The semantic core together with all of its source-bounded Euler data. -/
abbrev BoundedCanonicalEqualityData (p a : ℕ) :=
  Σ C : AbstractContractedCore p a, BoundedCanonicalPayload C

noncomputable instance boundedCanonicalEqualityDataFintype (p a : ℕ) :
    Fintype (BoundedCanonicalEqualityData p a) :=
  Sigma.instFintype

@[simp] theorem equalityHalfEdge_card (p : ℕ) :
    Fintype.card (EqualityHalfEdge p) = 4 * p := by
  simp [EqualityHalfEdge]
  omega

theorem equalityVertex_card {p s t : ℕ}
    (Q : SelectorEqualityData p s t) :
    Fintype.card (EqualityVertex Q.1) = p - s := by
  simpa only [EqualityVertex, Fintype.card_coe] using Q.2.2.1

theorem equalityPortsAt_card_le_coreBase
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) :
    Fintype.card (EqualityPortsAt Q u) ≤ 4 * p + 1 := by
  rw [equalityPortsAt_card hp Q u]
  have hblock : u.1.card ≤ 2 * p := by
    calc
      u.1.card ≤ (Finset.univ : Finset (Fin (2 * p))).card :=
        Finset.card_le_card (Q.1.le u.2)
      _ = 2 * p := by simp
  omega

theorem equalityPortsAt_card_pos
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) :
    0 < Fintype.card (EqualityPortsAt Q u) := by
  rw [equalityPortsAt_card hp Q u]
  have htwo := Q.2.1 u.1 u.2
  omega

theorem equalityPortsAt_card_even
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) :
    Even (Fintype.card (EqualityPortsAt Q u)) := by
  rw [equalityPortsAt_card hp Q u]
  exact ⟨u.1.card, by omega⟩

/-- The exact local-transition excess of a source equality partition.  This
is the block excess identity rewritten in terms of indexed port fibers. -/
theorem equalityPortsAt_transitionExcess_sum
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (∑ u : EqualityVertex Q.1,
      (Fintype.card (EqualityPortsAt Q u) - 4) / 2) = 2 * s := by
  classical
  have hpartsne : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  have hpartspos : 0 < Q.1.parts.card := Finset.card_pos.mpr hpartsne
  have hslt : s < p := by
    rw [Q.2.2.1] at hpartspos
    omega
  have hpoint (u : EqualityVertex Q.1) :
      (Fintype.card (EqualityPortsAt Q u) - 4) / 2 = u.1.card - 2 := by
    rw [equalityPortsAt_card hp Q u]
    have htwo := Q.2.1 u.1 u.2
    omega
  calc
    (∑ u : EqualityVertex Q.1,
        (Fintype.card (EqualityPortsAt Q u) - 4) / 2) =
        ∑ B ∈ Q.1.parts, (B.card - 2) := by
      simp_rw [hpoint]
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach Q.1.parts (fun B ↦ B.card - 2)
    _ = 2 * s := by
      rw [Finset.sum_tsub_distrib Q.1.parts Q.2.1]
      rw [Q.1.sum_card_parts]
      simp only [Finset.card_univ, Fintype.card_fin,
        Finset.sum_const_nat]
      rw [Q.2.2.1]
      omega

private theorem canonicalLocalTransitionSystem_card_le
    {p a : ℕ} (C : AbstractContractedCore p a)
    (hC : CanonicalSourceBounds C) :
    Fintype.card (CanonicalLocalTransitionSystem C) ≤
      3 ^ p * (4 * p + 1) ^ (2 * a) := by
  classical
  let n := Fintype.card (CanonicalExpandedVertex C)
  let r := ∑ v : CanonicalExpandedVertex C,
    (Fintype.card (CanonicalExpandedPortsAt C v) - 4) / 2
  have hlocal := localFixedPointFreeInvolutionSystem_card_le
    (fun v : CanonicalExpandedVertex C ↦ CanonicalExpandedPortsAt C v)
    (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)
    (4 * p + 1) n r hC.port_card_le hC.port_card_pos
    hC.port_card_even rfl rfl
  have hcard : Fintype.card (CanonicalLocalTransitionSystem C) =
      ∏ v : CanonicalExpandedVertex C,
        Fintype.card
          (FixedPointFreeInvolution (CanonicalExpandedPortsAt C v)) := by
    simp only [CanonicalLocalTransitionSystem, Fintype.card_pi]
  rw [hcard]
  exact hlocal.trans (Nat.mul_le_mul
    (Nat.pow_le_pow_right (by omega) hC.expandedVertex_card_le)
    (pow_le_pow (by omega) (by omega) hC.excess_sum_le))

/-- Every fixed semantic core has at most the public Euler-transition budget
many source-bounded started transition systems. -/
theorem boundedCanonicalPayload_card_le
    {p a : ℕ} (C : AbstractContractedCore p a) :
    Fintype.card (BoundedCanonicalPayload C) ≤
      8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a) := by
  classical
  by_cases hC : CanonicalSourceBounds C
  · have hambient : Fintype.card (BoundedCanonicalPayload C) ≤
        Fintype.card
          (CanonicalExpandedPort C × CanonicalLocalTransitionSystem C) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    rw [Fintype.card_prod] at hambient
    calc
      Fintype.card (BoundedCanonicalPayload C) ≤
          Fintype.card (CanonicalExpandedPort C) *
            Fintype.card (CanonicalLocalTransitionSystem C) := hambient
      _ ≤ (8 * p) *
          (3 ^ p * (4 * p + 1) ^ (2 * a)) :=
        Nat.mul_le_mul hC.expandedPort_card_le
          (canonicalLocalTransitionSystem_card_le C hC)
      _ = 8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a) := by ring
  · have hempty : IsEmpty (BoundedCanonicalPayload C) :=
      ⟨fun d ↦ hC d.2⟩
    have hzero : Fintype.card (BoundedCanonicalPayload C) = 0 :=
      Fintype.card_eq_zero_iff.mpr hempty
    rw [hzero]
    exact Nat.zero_le _

/-- Total source-bounded canonical data fit in the exact public core and
Euler-transition product budget. -/
theorem boundedCanonicalEqualityData_card_le (p a : ℕ) :
    Fintype.card (BoundedCanonicalEqualityData p a) ≤
      (4 * p + 1) ^ (72 * a) *
        (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a)) := by
  classical
  rw [show Fintype.card (BoundedCanonicalEqualityData p a) =
      ∑ C : AbstractContractedCore p a,
        Fintype.card (BoundedCanonicalPayload C) by
    simp only [BoundedCanonicalEqualityData, Fintype.card_sigma]]
  calc
    (∑ C : AbstractContractedCore p a,
        Fintype.card (BoundedCanonicalPayload C)) ≤
        ∑ _C : AbstractContractedCore p a,
          (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a)) := by
      apply Finset.sum_le_sum
      intro C _
      exact boundedCanonicalPayload_card_le C
    _ = Fintype.card (AbstractContractedCore p a) *
        (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a)) := by simp
    _ ≤ (4 * p + 1) ^ (72 * a) *
        (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a)) :=
      Nat.mul_le_mul_right _ (abstractContractedCore_card_le p a)

/-- Any faithful source map into the bounded canonical data supplies the
decoder-bearing public encoding object.  The decoder itself is obtained from
the resulting finite injection by the general count/encoding equivalence. -/
theorem equalityEncoding_nonempty_of_boundedCanonicalInjection
    {p s t : ℕ}
    (f : SelectorEqualityData p s t ↪
      BoundedCanonicalEqualityData p (s + t)) :
    Nonempty (EqualityEncoding p s t) := by
  apply (equality_encoding_nonempty_iff_card_bound p s t).mpr
  change Fintype.card (SelectorEqualityData p s t) ≤ _
  exact (Fintype.card_le_of_injective f f.injective).trans
    (boundedCanonicalEqualityData_card_le p (s + t))

theorem contracted_core_encoding_bound_of_boundedCanonicalInjection
    {p s t : ℕ}
    (f : SelectorEqualityData p s t ↪
      BoundedCanonicalEqualityData p (s + t)) :
    Fintype.card (ContractedCoreCode p (s + t)) ≤
        (4 * p + 1) ^ (72 * (s + t)) ∧
      Nonempty (EqualityEncoding p s t) :=
  ⟨contracted_core_code_card_bound p s t,
    equalityEncoding_nonempty_of_boundedCanonicalInjection f⟩

#print axioms boundedCanonicalPayload_card_le
#print axioms boundedCanonicalEqualityData_card_le
#print axioms equalityPortsAt_transitionExcess_sum
#print axioms equalityHalfEdge_card
#print axioms equalityVertex_card
#print axioms equalityPortsAt_card_le_coreBase
#print axioms equalityPortsAt_card_pos
#print axioms equalityPortsAt_card_even
#print axioms equalityEncoding_nonempty_of_boundedCanonicalInjection
#print axioms contracted_core_encoding_bound_of_boundedCanonicalInjection

end

end Problem56
