import Problem56.ContractedCoreCanonicalCard
import Problem56.ContractedCoreCanonicalEncoding
import Problem56.ContractedCoreZeroParameter

/-!
# Closing the contracted-core encoding interface

The positive-parameter branch upgrades the explicit canonical-to-source port
injection to an equivalence by the exact cardinality calculation.  The
zero-parameter branch uses the separately classified canonical families.
-/

namespace Problem56

noncomputable section

/-- The explicit canonical-to-source port map is bijective. -/
theorem equalityCanonicalExpandedPortSourceHalfEdge_bijective
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Function.Bijective
      (equalityCanonicalExpandedPortSourceHalfEdge hp Q ha) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨equalityCanonicalExpandedPortSourceHalfEdge_injective hp Q ha,
    equalityCanonicalExpandedPort_card hp Q ha⟩

/-- Canonical expanded ports and indexed source half-edges are equivalent. -/
noncomputable def equalityCanonicalExpandedPortEquivSourceHalfEdge
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    CanonicalExpandedPort (equalityAbstractContractedCore hp Q ha) ≃
      EqualityHalfEdge p :=
  Equiv.ofBijective
    (equalityCanonicalExpandedPortSourceHalfEdge hp Q ha)
    (equalityCanonicalExpandedPortSourceHalfEdge_bijective hp Q ha)

/-- Every positive-parameter equality object is realized on its extracted
compatible canonical core, preserving both vertices and edge mates. -/
noncomputable def equalityCanonicalSourceRealizationData
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    CanonicalSourceRealizationData Q
      (equalityAbstractContractedCore hp Q ha) where
  compatible := equalityAbstractContractedCore_compatible hp Q ha
  portEquiv :=
    (equalityCanonicalExpandedPortEquivSourceHalfEdge hp Q ha).symm
  vertexEquiv := equalityVertexEquivCanonicalExpandedVertex hp Q ha
  port_vertex := by
    intro h
    let E := equalityCanonicalExpandedPortEquivSourceHalfEdge hp Q ha
    have hvert := equalityCanonicalExpandedPortSourceHalfEdge_vertex hp Q ha
      (E.symm h)
    exact hvert.symm.trans (congrArg
      (equalityVertexEquivCanonicalExpandedVertex hp Q ha ∘
        equalityHalfEdgeVertex Q)
      (E.apply_symm_apply h))
  opposite := by
    intro h
    apply (equalityCanonicalExpandedPortEquivSourceHalfEdge hp Q ha).injective
    rw [Equiv.apply_symm_apply]
    symm
    change equalityCanonicalExpandedPortSourceHalfEdge hp Q ha
        (canonicalExpandedEdgeMate
          (equalityAbstractContractedCore_compatible hp Q ha)
          ((equalityCanonicalExpandedPortEquivSourceHalfEdge hp Q ha).symm h)) =
      _
    rw [equalityCanonicalExpandedPortSourceHalfEdge_edgeMate]
    exact congrArg equalityOppositeHalfEdge
      ((equalityCanonicalExpandedPortEquivSourceHalfEdge hp Q ha).apply_symm_apply h)

/-- The corrected public contracted-core/Euler encoding interface is
unconditional in both the positive- and zero-parameter branches. -/
theorem contracted_core_encoding_bound_closed
    (p s t : ℕ) (hp : 2 ≤ p) :
    Fintype.card (ContractedCoreCode p (s + t)) ≤
        (4 * p + 1) ^ (72 * (s + t)) ∧
      Nonempty (EqualityEncoding p s t) := by
  by_cases ha : 0 < s + t
  · exact contracted_core_encoding_bound_of_realizations hp
      (fun Q ↦ equalityAbstractContractedCore hp Q ha)
      (fun Q ↦ equalityCanonicalSourceRealizationData hp Q ha)
  · have hsum : s + t = 0 := by omega
    have hs : s = 0 := by omega
    have ht : t = 0 := by omega
    subst s
    subst t
    exact contracted_core_encoding_bound_zero_of_eulerInjection
      (zeroParameterInjection hp)

#print axioms equalityCanonicalExpandedPortSourceHalfEdge_bijective
#print axioms equalityCanonicalExpandedPortEquivSourceHalfEdge
#print axioms equalityCanonicalSourceRealizationData
#print axioms contracted_core_encoding_bound_closed

end

end Problem56
