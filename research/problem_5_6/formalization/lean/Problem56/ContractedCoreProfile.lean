import Problem56.ContractedCoreSerialization

/-!
# Numerical retained-core profiles

This file labels the retained vertices and their ports only after the
source-side contraction has been proved.  The labels are auxiliary: a profile
records a retained-vertex count and its even degree vector, while the actual
vertices remain recoverable from the later Euler traversal.
-/

namespace Problem56

open scoped BigOperators

/-- A numerical retained-vertex degree profile.  The vertex count itself is
stored in one `a`-digit field, and the positive degree entries occupy the first
`q ≤ 8a` slots of the padded degree vector. -/
structure ContractedCoreDegreeProfile (p a : ℕ) where
  vertexCountCode : Fin ((4 * p + 1) ^ a)
  vertexCount_le : vertexCountCode.1 ≤ 8 * a
  degree : Fin vertexCountCode.1 → Fin (4 * p + 1)
  degree_pos : ∀ i, 0 < (degree i).1
  degree_even : ∀ i, Even (degree i).1
  totalDegree_le_parameter : (∑ i, (degree i).1) ≤ 36 * a
  totalDegree_le_edges : (∑ i, (degree i).1) ≤ 4 * p
  deriving Fintype

/-- The fixed-size storage occupied by the vertex count and padded degree
vector. -/
abbrev ContractedCoreDegreeProfileRaw (p a : ℕ) :=
  Fin ((4 * p + 1) ^ a) × (Fin (8 * a) → Fin (4 * p + 1))

/-- Pad a profile's degree vector by zero outside its active prefix. -/
def contractedCoreDegreeProfilePadded {p a : ℕ}
    (c : ContractedCoreDegreeProfile p a) :
    Fin (8 * a) → Fin (4 * p + 1) := fun i ↦
  if hi : i.1 < c.vertexCountCode.1 then c.degree ⟨i.1, hi⟩ else 0

/-- Forget the validity proofs and store a profile in its designated fields. -/
def contractedCoreDegreeProfileToRaw {p a : ℕ} :
    ContractedCoreDegreeProfile p a → ContractedCoreDegreeProfileRaw p a :=
  fun c ↦ ⟨c.vertexCountCode, contractedCoreDegreeProfilePadded c⟩

theorem contractedCoreDegreeProfileToRaw_injective {p a : ℕ} :
    Function.Injective
      (contractedCoreDegreeProfileToRaw (p := p) (a := a)) := by
  intro c d h
  have hq : c.vertexCountCode = d.vertexCountCode := congrArg Prod.fst h
  cases c with
  | mk cq cqle cdeg cpos ceven csumA csumP =>
    cases d with
    | mk dq dqle ddeg dpos deven dsumA dsumP =>
      dsimp only at hq
      subst dq
      have hfun : contractedCoreDegreeProfilePadded
            (ContractedCoreDegreeProfile.mk cq cqle cdeg cpos ceven csumA csumP) =
          contractedCoreDegreeProfilePadded
            (ContractedCoreDegreeProfile.mk cq dqle ddeg dpos deven dsumA dsumP) :=
        congrArg Prod.snd h
      have hdeg : cdeg = ddeg := by
        funext i
        have hi := congrFun hfun ⟨i.1, lt_of_lt_of_le i.2 cqle⟩
        simpa [contractedCoreDegreeProfilePadded, i.2] using hi
      subst ddeg
      rfl

/-- The profile fields use at most `9a` base-`4p+1` digits. -/
theorem contractedCoreDegreeProfile_card_le (p a : ℕ) :
    Fintype.card (ContractedCoreDegreeProfile p a) ≤
      (4 * p + 1) ^ (9 * a) := by
  calc
    Fintype.card (ContractedCoreDegreeProfile p a) ≤
        Fintype.card (ContractedCoreDegreeProfileRaw p a) :=
      Fintype.card_le_of_injective contractedCoreDegreeProfileToRaw
        contractedCoreDegreeProfileToRaw_injective
    _ = (4 * p + 1) ^ a * (4 * p + 1) ^ (8 * a) := by
      simp only [ContractedCoreDegreeProfileRaw, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fun]
    _ = (4 * p + 1) ^ (9 * a) := by
      rw [← pow_add]
      congr 1
      omega

/-- The elementary inequality that lets one store any count `q ≤ 8a` in an
`a`-digit base-`4p+1` field when `p ≥ 2` and `a > 0`. -/
theorem eight_mul_add_one_le_coreBase_pow
    (p a : ℕ) (hp : 2 ≤ p) (ha : 0 < a) :
    8 * a + 1 ≤ (4 * p + 1) ^ a := by
  have hbase : 9 ≤ 4 * p + 1 := by omega
  have hlinear : 8 * a + 1 ≤ 9 ^ a := by
    induction a with
    | zero => omega
    | succ a ih =>
      by_cases ha0 : a = 0
      · subst a
        norm_num
      · have ih' : 8 * a + 1 ≤ 9 ^ a := ih (Nat.pos_of_ne_zero ha0)
        rw [pow_succ]
        calc
          8 * (a + 1) + 1 ≤ 9 * (8 * a + 1) := by omega
          _ ≤ 9 * 9 ^ a := Nat.mul_le_mul_left 9 ih'
          _ = 9 ^ a * 9 := by ac_rfl
  exact hlinear.trans (Nat.pow_le_pow_left hbase a)

/-- Canonical auxiliary labels for the retained vertices. -/
noncomputable def equalityRetainedVertexEquivFin
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    EqualityRetainedVertex Q ≃
      Fin (Fintype.card (EqualityRetainedVertex Q)) :=
  Fintype.equivFin _

/-- The degree, in indexed half-edge ports, of the retained vertex with a
given auxiliary label. -/
noncomputable def equalityRetainedDegreeAtLabel
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (i : Fin (Fintype.card (EqualityRetainedVertex Q))) : ℕ :=
  Fintype.card
    (EqualityPortsAt Q ((equalityRetainedVertexEquivFin Q).symm i).1)

theorem equalityRetainedDegreeAtLabel_sum
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :
    (∑ i, equalityRetainedDegreeAtLabel Q i) =
      Fintype.card (EqualityRetainedPorts Q) := by
  classical
  rw [show Fintype.card (EqualityRetainedPorts Q) =
      ∑ u : EqualityRetainedVertex Q,
        Fintype.card (EqualityPortsAt Q u.1) by
    simp only [EqualityRetainedPorts, Fintype.card_sigma]]
  simpa only [equalityRetainedDegreeAtLabel] using
    Equiv.sum_comp (equalityRetainedVertexEquivFin Q).symm
      (fun u : EqualityRetainedVertex Q ↦
        Fintype.card (EqualityPortsAt Q u.1))

theorem equalityRetainedDegreeAtLabel_pos
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (i : Fin (Fintype.card (EqualityRetainedVertex Q))) :
    0 < equalityRetainedDegreeAtLabel Q i := by
  rw [equalityRetainedDegreeAtLabel, equalityPortsAt_card hp Q]
  have hmem :
      (((equalityRetainedVertexEquivFin Q).symm i).1 :
          Finset (Fin (2 * p))).Nonempty :=
    Q.1.nonempty_of_mem_parts
      ((equalityRetainedVertexEquivFin Q).symm i).1.2
  exact Nat.mul_pos (by omega) (Finset.card_pos.mpr hmem)

theorem equalityRetainedDegreeAtLabel_even
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (i : Fin (Fintype.card (EqualityRetainedVertex Q))) :
    Even (equalityRetainedDegreeAtLabel Q i) := by
  rw [equalityRetainedDegreeAtLabel, equalityPortsAt_card hp Q]
  exact ⟨((equalityRetainedVertexEquivFin Q).symm i).1.1.card, by omega⟩

theorem equalityRetainedDegreeAtLabel_lt_coreBase
    {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (i : Fin (Fintype.card (EqualityRetainedVertex Q))) :
    equalityRetainedDegreeAtLabel Q i < 4 * p + 1 := by
  have hsingle : equalityRetainedDegreeAtLabel Q i ≤
      ∑ j, equalityRetainedDegreeAtLabel Q j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
  rw [equalityRetainedDegreeAtLabel_sum Q] at hsingle
  have h := equalityRetainedPorts_card_le_four_p Q
  omega

/-- The source equality graph's retained degree profile. -/
noncomputable def equalityContractedCoreDegreeProfile
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) : ContractedCoreDegreeProfile p (s + t) where
  vertexCountCode :=
    ⟨Fintype.card (EqualityRetainedVertex Q), by
      have hq := equality_retained_card_le_of_parameter_pos hp Q ha
      have hcard : Fintype.card (EqualityRetainedVertex Q) =
          (equalityRetainedVertices Q).card := by simp
      have hpow := eight_mul_add_one_le_coreBase_pow p (s + t) hp ha
      omega⟩
  vertexCount_le := by
    change Fintype.card (EqualityRetainedVertex Q) ≤ 8 * (s + t)
    simpa only [Fintype.card_coe] using
      equality_retained_card_le_of_parameter_pos hp Q ha
  degree := fun i ↦
    ⟨equalityRetainedDegreeAtLabel Q i,
      equalityRetainedDegreeAtLabel_lt_coreBase Q i⟩
  degree_pos := equalityRetainedDegreeAtLabel_pos hp Q
  degree_even := equalityRetainedDegreeAtLabel_even hp Q
  totalDegree_le_parameter := by
    simp only [Fin.sum_univ_eq_sum_range]
    rw [equalityRetainedDegreeAtLabel_sum Q]
    exact equalityRetainedPorts_card_le_of_parameter_pos hp Q ha
  totalDegree_le_edges := by
    simp only [Fin.sum_univ_eq_sum_range]
    rw [equalityRetainedDegreeAtLabel_sum Q]
    exact equalityRetainedPorts_card_le_four_p Q

/-! ## Standard port labels attached to a profile -/

/-- Ports of a numerical profile, grouped in consecutive fibers over the
auxiliary vertex labels. -/
abbrev ContractedCorePort {p a : ℕ}
    (c : ContractedCoreDegreeProfile p a) :=
  Σ i : Fin c.vertexCountCode.1, Fin (c.degree i).1

theorem contractedCorePort_card {p a : ℕ}
    (c : ContractedCoreDegreeProfile p a) :
    Fintype.card (ContractedCorePort c) = ∑ i, (c.degree i).1 := by
  simp only [ContractedCorePort, Fintype.card_sigma, Fintype.card_fin]

/-- Identify the actual retained ports with the consecutive dependent port
fibers of their numerical degree profile. -/
noncomputable def equalityRetainedPortsEquivContractedCorePort
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    EqualityRetainedPorts Q ≃
      ContractedCorePort (equalityContractedCoreDegreeProfile hp Q ha) := by
  let eV := equalityRetainedVertexEquivFin Q
  apply Equiv.sigmaCongr eV
  intro u
  let eLocal := Fintype.equivFin (EqualityPortsAt Q u.1)
  refine eLocal.trans (finCongr ?_)
  change Fintype.card (EqualityPortsAt Q u.1) =
    equalityRetainedDegreeAtLabel Q (eV u)
  change Fintype.card (EqualityPortsAt Q u.1) =
    Fintype.card (EqualityPortsAt Q
      ((equalityRetainedVertexEquivFin Q).symm
        ((equalityRetainedVertexEquivFin Q) u)).1)
  rw [Equiv.symm_apply_apply]

/-- Transport the contracted mate operation to the standard numerical port
type. -/
noncomputable def equalityStandardContractedPortOpposite
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    ContractedCorePort (equalityContractedCoreDegreeProfile hp Q ha) →
      ContractedCorePort (equalityContractedCoreDegreeProfile hp Q ha) :=
  let E := equalityRetainedPortsEquivContractedCorePort hp Q ha
  E ∘ equalityContractedRetainedPortOpposite hp Q ha ∘ E.symm

@[simp] theorem equalityStandardContractedPortOpposite_involutive
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : ContractedCorePort (equalityContractedCoreDegreeProfile hp Q ha)) :
    equalityStandardContractedPortOpposite hp Q ha
        (equalityStandardContractedPortOpposite hp Q ha z) = z := by
  let E := equalityRetainedPortsEquivContractedCorePort hp Q ha
  apply E.symm.injective
  simp [equalityStandardContractedPortOpposite, E, Function.comp_apply]

theorem equalityStandardContractedPortOpposite_ne
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t)
    (z : ContractedCorePort (equalityContractedCoreDegreeProfile hp Q ha)) :
    equalityStandardContractedPortOpposite hp Q ha z ≠ z := by
  let E := equalityRetainedPortsEquivContractedCorePort hp Q ha
  intro h
  have hE := congrArg E.symm h
  have hfix : equalityContractedRetainedPortOpposite hp Q ha (E.symm z) =
      E.symm z := by
    simpa [equalityStandardContractedPortOpposite, E,
      Function.comp_apply] using hE
  exact equalityContractedRetainedPortOpposite_ne hp Q ha (E.symm z) hfix

/-- The contracted multigraph pairing on the standard numerical port type. -/
noncomputable def equalityStandardContractedPortPairing
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (ha : 0 < s + t) :
    Pairing (Finset.univ : Finset
      (ContractedCorePort (equalityContractedCoreDegreeProfile hp Q ha))) :=
  pairingOfFixedPointFreeInvolution
    (equalityStandardContractedPortOpposite hp Q ha)
    (equalityStandardContractedPortOpposite_involutive hp Q ha)
    (equalityStandardContractedPortOpposite_ne hp Q ha)

#print axioms contractedCoreDegreeProfileToRaw_injective
#print axioms contractedCoreDegreeProfile_card_le
#print axioms eight_mul_add_one_le_coreBase_pow
#print axioms equalityRetainedDegreeAtLabel_sum
#print axioms equalityContractedCoreDegreeProfile
#print axioms contractedCorePort_card
#print axioms equalityRetainedPortsEquivContractedCorePort
#print axioms equalityStandardContractedPortOpposite_involutive
#print axioms equalityStandardContractedPortOpposite_ne
#print axioms equalityStandardContractedPortPairing

end Problem56
