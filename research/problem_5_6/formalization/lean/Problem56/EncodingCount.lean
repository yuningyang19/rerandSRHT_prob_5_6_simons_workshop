import Problem56.Definitions

/-!
Exact cardinalities of the finite coding spaces and the decoder-based injection
used by the Euler-transition count.
-/

namespace Problem56

private def contractedCoreCodeEquiv (p a : ℕ) :
    ContractedCoreCode p a ≃
      Fin ((4 * p + 1) ^ a) ×
      (Fin (8 * a) → Fin (4 * p + 1)) ×
      (Fin (18 * a) → Fin (4 * p + 1)) ×
      (Fin (36 * a) → Fin (4 * p + 1)) ×
      (Fin (9 * a) → Fin (4 * p + 1)) where
  toFun c := (c.vertexDegreeChoice, c.degreeVector, c.halfEdgePairing,
    c.doubledLinkPorts, c.linkLengths)
  invFun c :=
    { vertexDegreeChoice := c.1
      degreeVector := c.2.1
      halfEdgePairing := c.2.2.1
      doubledLinkPorts := c.2.2.2.1
      linkLengths := c.2.2.2.2 }
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, c, d, e⟩; rfl

private def eulerTransitionCodeEquiv (p a : ℕ) :
    EulerTransitionCode p a ≃
      Fin (8 * p) × (Fin p → Fin 3) ×
        (Fin (2 * a) → Fin (4 * p + 1)) where
  toFun c := (c.startingDirectedEdgeAndCase, c.localDegreeFourTransitions,
    c.excessTransitions)
  invFun c :=
    { startingDirectedEdgeAndCase := c.1
      localDegreeFourTransitions := c.2.1
      excessTransitions := c.2.2 }
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, c⟩; rfl

theorem contracted_core_code_card (p a : ℕ) :
    Fintype.card (ContractedCoreCode p a) = (4 * p + 1) ^ (72 * a) := by
  rw [Fintype.card_congr (contractedCoreCodeEquiv p a)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  simp only [← pow_add]
  congr 2
  omega

theorem euler_transition_code_card (p a : ℕ) :
    Fintype.card (EulerTransitionCode p a) =
      8 * p * 3 ^ p * (4 * p + 1) ^ (2 * a) := by
  rw [Fintype.card_congr (eulerTransitionCodeEquiv p a)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  ring

private def encodedEqualityData {p s t : ℕ} (enc : EqualityEncoding p s t) :
    SelectorEqualityData p s t →
      (Σ c : ContractedCoreCode p (s + t), EulerTransitions c) :=
  fun Q ↦ ⟨enc.encodeCore Q, enc.encodeTransition Q⟩

private theorem encodedEqualityData_injective {p s t : ℕ}
    (enc : EqualityEncoding p s t) :
    Function.Injective (encodedEqualityData enc) := by
  intro Q R hQR
  have hdecode := congrArg
    (fun z : (Σ c : ContractedCoreCode p (s + t), EulerTransitions c) ↦
      enc.decode z.1 z.2) hQR
  have hsome : some Q = some R := by
    simpa only [encodedEqualityData, enc.decode_encode] using hdecode
  exact Option.some.inj hsome

private def encodedSpaceEquiv (p a : ℕ) :
    (Σ c : ContractedCoreCode p a, EulerTransitions c) ≃
      ContractedCoreCode p a × EulerTransitionCode p a where
  toFun z := (z.1, z.2)
  invFun z := ⟨z.1, z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

theorem euler_transition_count (p s t : ℕ) (enc : EqualityEncoding p s t) :
    (∀ c : ContractedCoreCode p (s + t),
      Fintype.card (EulerTransitions c) ≤
        8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) ∧
    selectorEqualityCount p s t ≤
      (4 * p + 1) ^ (72 * (s + t)) *
        (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) := by
  constructor
  · intro c
    exact (euler_transition_code_card p (s + t)).le
  · have hinj : selectorEqualityCount p s t ≤
        Fintype.card (Σ c : ContractedCoreCode p (s + t), EulerTransitions c) := by
      dsimp only [selectorEqualityCount]
      exact Fintype.card_le_of_injective (encodedEqualityData enc)
        (encodedEqualityData_injective enc)
    calc
      selectorEqualityCount p s t ≤
          Fintype.card (Σ c : ContractedCoreCode p (s + t), EulerTransitions c) := hinj
      _ = Fintype.card (ContractedCoreCode p (s + t)) *
          Fintype.card (EulerTransitionCode p (s + t)) := by
        rw [Fintype.card_congr (encodedSpaceEquiv p (s + t)), Fintype.card_prod]
      _ = (4 * p + 1) ^ (72 * (s + t)) *
          (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) := by
        rw [contracted_core_code_card, euler_transition_code_card]

#print axioms contracted_core_code_card
#print axioms euler_transition_count

end Problem56
