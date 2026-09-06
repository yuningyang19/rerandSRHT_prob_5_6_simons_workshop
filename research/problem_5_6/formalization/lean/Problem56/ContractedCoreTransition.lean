import Problem56.ContractedCoreExtraction
import Problem56.AggregatePartitionCumulant

/-!
# Euler transition data for the equality circuit

The cyclic trace order supplies, at every equality vertex, a pairing between
the arriving half-edge and the next departing half-edge.  This file packages
that pairing without identifying loops or parallel indexed occurrences.
-/

namespace Problem56

open scoped BigOperators

noncomputable section

/-- Addition by one, viewed as the cyclic-successor equivalence. -/
def cyclicSuccEquiv (q : ℕ) [NeZero q] : Fin q ≃ Fin q :=
  Equiv.addRight (1 : Fin q)

@[simp] theorem cyclicSuccEquiv_apply {q : ℕ} [NeZero q]
    (i : Fin q) : cyclicSuccEquiv q i = cyclicSucc i := by
  apply Fin.ext
  simp [cyclicSuccEquiv, cyclicSucc, Fin.add_def]

/-- At a vertex, pair an outgoing cyclic occurrence with the arrival along
its predecessor, and pair an arrival with the next cyclic occurrence. -/
noncomputable def equalityCyclicTransitionOpposite
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) : EqualityPortsAt Q u → EqualityPortsAt Q u :=
  fun h ↦ by
    letI : NeZero (2 * p) := ⟨by omega⟩
    rcases h with ⟨⟨e, b⟩, he⟩
    cases b with
    | false =>
        let f := (cyclicSuccEquiv (2 * p)).symm e
        refine ⟨(f, true), ?_⟩
        change equalityVertexAt Q.1 (cyclicSucc f) = u
        rw [← cyclicSuccEquiv_apply,
          (cyclicSuccEquiv (2 * p)).apply_symm_apply]
        exact he
    | true =>
        refine ⟨(cyclicSucc e, false), ?_⟩
        exact he

@[simp] theorem equalityCyclicTransitionOpposite_involutive
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (h : EqualityPortsAt Q u) :
    equalityCyclicTransitionOpposite hp Q u
        (equalityCyclicTransitionOpposite hp Q u h) = h := by
  letI : NeZero (2 * p) := ⟨by omega⟩
  rcases h with ⟨⟨e, b⟩, he⟩
  cases b with
  | false =>
      apply Subtype.ext
      apply Prod.ext
      · change cyclicSucc ((cyclicSuccEquiv (2 * p)).symm e) = e
        rw [← cyclicSuccEquiv_apply,
          (cyclicSuccEquiv (2 * p)).apply_symm_apply]
      · rfl
  | true =>
      apply Subtype.ext
      apply Prod.ext
      · change (cyclicSuccEquiv (2 * p)).symm (cyclicSucc e) = e
        rw [← cyclicSuccEquiv_apply,
          (cyclicSuccEquiv (2 * p)).symm_apply_apply]
      · rfl

theorem equalityCyclicTransitionOpposite_ne
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) (h : EqualityPortsAt Q u) :
    equalityCyclicTransitionOpposite hp Q u h ≠ h := by
  rcases h with ⟨⟨e, b⟩, he⟩
  cases b <;> intro hEq
  · have hb := congrArg (fun z : EqualityPortsAt Q u ↦ z.1.2) hEq
    simp [equalityCyclicTransitionOpposite] at hb
  · have hb := congrArg (fun z : EqualityPortsAt Q u ↦ z.1.2) hEq
    simp [equalityCyclicTransitionOpposite] at hb

/-- The local transition pairing induced by the original cyclic trace word. -/
noncomputable def equalityCyclicTransitionPairing
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (u : EqualityVertex Q.1) :
    Pairing (Finset.univ : Finset (EqualityPortsAt Q u)) :=
  pairingOfFixedPointFreeInvolution
    (equalityCyclicTransitionOpposite hp Q u)
    (equalityCyclicTransitionOpposite_involutive hp Q u)
    (equalityCyclicTransitionOpposite_ne hp Q u)

/-- Recovering the mate from the orbit pairing returns the original
fixed-point-free involution. -/
theorem pairingMate_pairingOfFixedPointFreeInvolution
    {α : Type*} [Fintype α] [DecidableEq α]
    (op : α → α) (hinv : Function.Involutive op)
    (hne : ∀ x, op x ≠ x) (x : α) :
    pairingMate (pairingOfFixedPointFreeInvolution op hinv hne) x (by simp) =
      op x := by
  let P := pairingOfFixedPointFreeInvolution op hinv hne
  apply (pairing_existsUnique_mate P x (by simp)).unique
  · exact ⟨pairingMate_mem P x (by simp), pairingMate_ne P x (by simp)⟩
  · refine ⟨?_, hne x⟩
    change op x ∈
      (pairingOfFixedPointFreeInvolution op hinv hne).1.part x
    simp [pairingOfFixedPointFreeInvolution,
      Finpartition.mem_part_ofSetoid_iff_rel]

/-- A fixed-point-free involution kept as data.  This form transports cleanly
through an equivalence of port fibers; its orbit pairing supplies the sharp
cardinality bound. -/
def FixedPointFreeInvolution (α : Type*) :=
  {op : α → α // Function.Involutive op ∧ ∀ x, op x ≠ x}

noncomputable instance fixedPointFreeInvolutionFintype
    {α : Type*} [Fintype α] : Fintype (FixedPointFreeInvolution α) := by
  classical
  unfold FixedPointFreeInvolution
  exact Fintype.ofFinite _

/-- Forget the presentation and retain the two-element orbit partition. -/
noncomputable def fixedPointFreeInvolutionPairing
    {α : Type*} [Fintype α] [DecidableEq α] :
    FixedPointFreeInvolution α →
      Pairing (Finset.univ : Finset α) := fun f ↦
  pairingOfFixedPointFreeInvolution f.1 f.2.1 f.2.2

theorem fixedPointFreeInvolutionPairing_injective
    {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective
      (fixedPointFreeInvolutionPairing (α := α)) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have hm := congrArg
    (fun P : Pairing (Finset.univ : Finset α) ↦
      pairingMate P x (by simp)) hfg
  simpa [fixedPointFreeInvolutionPairing,
    pairingMate_pairingOfFixedPointFreeInvolution] using hm

theorem fixedPointFreeInvolution_card_le_pairing
    {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card (FixedPointFreeInvolution α) ≤
      Fintype.card (Pairing (Finset.univ : Finset α)) :=
  Fintype.card_le_of_injective fixedPointFreeInvolutionPairing
    fixedPointFreeInvolutionPairing_injective

/-- All local half-edge transition pairings on a fixed equality multigraph. -/
abbrev EqualityLocalTransitionSystem
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :=
  (u : EqualityVertex Q.1) →
    Pairing (Finset.univ : Finset (EqualityPortsAt Q u))

/-- The transition system supplied by the original cyclic trace order. -/
noncomputable def equalityCyclicTransitionSystem
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    EqualityLocalTransitionSystem Q :=
  fun u ↦ equalityCyclicTransitionPairing hp Q u

/-- Abstract product bound for local pairings.  Keeping the vertex and port
families opaque avoids unfolding a source partition while the same lemma is
reused for the canonical expanded core. -/
theorem localPairingSystem_card_le
    {V : Type*} [Fintype V]
    (Port : V → Type*)
    (portFintype : ∀ v, Fintype (Port v))
    (portLinearOrder : ∀ v, LinearOrder (Port v))
    (M n r : ℕ)
    (hcap : ∀ v, Fintype.card (Port v) ≤ M)
    (hpos : ∀ v, 0 < Fintype.card (Port v))
    (heven : ∀ v, Even (Fintype.card (Port v)))
    (hvertices : Fintype.card V = n)
    (hsum : (∑ v : V, (Fintype.card (Port v) - 4) / 2) = r) :
    (∏ v : V, Fintype.card
      (Pairing (Finset.univ : Finset (Port v)))) ≤ 3 ^ n * M ^ r := by
  classical
  letI (v : V) : Fintype (Port v) := portFintype v
  letI (v : V) : LinearOrder (Port v) := portLinearOrder v
  have hpoint (v : V) :
      Fintype.card (Pairing (Finset.univ : Finset (Port v))) ≤
        3 * M ^ ((Fintype.card (Port v) - 4) / 2) :=
    pairing_univ_card_sharp_bound M (hcap v) (hpos v) (heven v)
  calc
    (∏ v : V, Fintype.card
        (Pairing (Finset.univ : Finset (Port v)))) ≤
        ∏ v : V, 3 * M ^ ((Fintype.card (Port v) - 4) / 2) := by
      apply Finset.prod_le_prod
      · intro v _
        exact Nat.zero_le _
      · intro v _
        exact hpoint v
    _ = 3 ^ n * M ^ r := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, hvertices,
        Finset.prod_pow_eq_pow_sum, hsum]

/-- The corresponding product bound for transport-friendly involution data. -/
theorem localFixedPointFreeInvolutionSystem_card_le
    {V : Type*} [Fintype V]
    (Port : V → Type*)
    (portFintype : ∀ v, Fintype (Port v))
    (portLinearOrder : ∀ v, LinearOrder (Port v))
    (M n r : ℕ)
    (hcap : ∀ v, Fintype.card (Port v) ≤ M)
    (hpos : ∀ v, 0 < Fintype.card (Port v))
    (heven : ∀ v, Even (Fintype.card (Port v)))
    (hvertices : Fintype.card V = n)
    (hsum : (∑ v : V, (Fintype.card (Port v) - 4) / 2) = r) :
    (∏ v : V, Fintype.card (FixedPointFreeInvolution (Port v))) ≤
      3 ^ n * M ^ r := by
  classical
  letI (v : V) : Fintype (Port v) := portFintype v
  letI (v : V) : LinearOrder (Port v) := portLinearOrder v
  calc
    (∏ v : V, Fintype.card (FixedPointFreeInvolution (Port v))) ≤
        ∏ v : V,
          Fintype.card (Pairing (Finset.univ : Finset (Port v))) := by
      apply Finset.prod_le_prod
      · intro v _
        exact Nat.zero_le _
      · intro v _
        exact fixedPointFreeInvolution_card_le_pairing
    _ ≤ 3 ^ n * M ^ r :=
      localPairingSystem_card_le Port portFintype portLinearOrder M n r
        hcap hpos heven hvertices hsum

#print axioms cyclicSuccEquiv_apply
#print axioms equalityCyclicTransitionOpposite
#print axioms equalityCyclicTransitionOpposite_involutive
#print axioms equalityCyclicTransitionOpposite_ne
#print axioms equalityCyclicTransitionPairing
#print axioms pairingMate_pairingOfFixedPointFreeInvolution
#print axioms fixedPointFreeInvolutionPairing_injective
#print axioms fixedPointFreeInvolution_card_le_pairing
#print axioms equalityCyclicTransitionSystem
#print axioms localPairingSystem_card_le
#print axioms localFixedPointFreeInvolutionSystem_card_le
#print axioms pairing_card_parallel_bound

end


end Problem56
