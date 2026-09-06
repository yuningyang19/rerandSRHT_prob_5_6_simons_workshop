import Problem56.ContractedCoreProfile
import Problem56.ContractedCorePairingCode

/-!
# Counted contracted-core topology

The degree profile fixes consecutive numerical port fibers.  A topology then
consists of a pairing of all retained ports, an ordered family of four
distinct ports for each positive doubled link, and its positive length.  The
three payloads occupy exactly the remaining `18a + 36a + 9a` core digits.
-/

namespace Problem56

open scoped BigOperators

noncomputable section

/-- The four distinguished ports of each ordered positive doubled link. -/
abbrev ContractedCoreLinkPortIndex (ell : ℕ) :=
  Fin ell × (Fin 2 × Fin 2)

@[simp] theorem contractedCoreLinkPortIndex_card (ell : ℕ) :
    Fintype.card (ContractedCoreLinkPortIndex ell) = 4 * ell := by
  simp [ContractedCoreLinkPortIndex, Nat.mul_comm]

/-- Positive-link data over a fixed retained degree profile. -/
structure ContractedCoreLinkData {p a : ℕ}
    (c : ContractedCoreDegreeProfile p a) where
  linkCount : Fin (9 * a + 1)
  linkPorts : ContractedCoreLinkPortIndex linkCount.1 ↪ ContractedCorePort c
  linkLength : Fin linkCount.1 → Fin (4 * p + 1)
  linkLength_pos : ∀ i, 0 < (linkLength i).1
  deriving Fintype

/-- A port plus a padding symbol fits in the core alphabet because the total
retained degree is at most `4p`. -/
noncomputable def contractedCorePortOptionEmbedding
    {p a : ℕ} (c : ContractedCoreDegreeProfile p a) :
    Option (ContractedCorePort c) ↪ Fin (4 * p + 1) where
  toFun
    | none => 0
    | some z =>
        ⟨(Fintype.equivFin (ContractedCorePort c) z).1 + 1, by
          have hcard := c.totalDegree_le_edges
          rw [← contractedCorePort_card c] at hcard
          have hz := (Fintype.equivFin (ContractedCorePort c) z).2
          omega⟩
  inj' := by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            have hv := congrArg Fin.val h
            simp at hv
    | some x =>
        cases y with
        | none =>
            have hv := congrArg Fin.val h
            simp at hv
        | some y =>
            congr 1
            apply (Fintype.equivFin (ContractedCorePort c)).injective
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa using hv

/-- The link-port domain fits in the designated `36a` slots. -/
theorem contractedCoreLinkPortIndex_card_le
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a}
    (d : ContractedCoreLinkData c) :
    Fintype.card (ContractedCoreLinkPortIndex d.linkCount.1) ≤ 36 * a := by
  rw [contractedCoreLinkPortIndex_card]
  have h := d.linkCount.2
  omega

/-- Padded link-port serialization.  Active entries are encoded with `some`,
so zero is reserved for padding and the active prefix remains recoverable. -/
noncomputable def contractedCoreLinkPortsPadded
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a}
    (d : ContractedCoreLinkData c) :
    Fin (36 * a) → Fin (4 * p + 1) := fun i ↦
  if hi : i.1 < Fintype.card
      (ContractedCoreLinkPortIndex d.linkCount.1) then
    contractedCorePortOptionEmbedding c
      (some (d.linkPorts
        ((Fintype.equivFin
          (ContractedCoreLinkPortIndex d.linkCount.1)).symm ⟨i.1, hi⟩)))
  else 0

/-- Padded positive link lengths. -/
def contractedCoreLinkLengthsPadded
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a}
    (d : ContractedCoreLinkData c) :
    Fin (9 * a) → Fin (4 * p + 1) := fun i ↦
  if hi : i.1 < d.linkCount.1 then d.linkLength ⟨i.1, hi⟩ else 0

/-- The two fixed arrays used for link designations and lengths. -/
abbrev ContractedCoreLinkRaw (p a : ℕ) :=
  (Fin (36 * a) → Fin (4 * p + 1)) ×
    (Fin (9 * a) → Fin (4 * p + 1))

noncomputable def contractedCoreLinkDataToRaw
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a} :
    ContractedCoreLinkData c → ContractedCoreLinkRaw p a := fun d ↦
  ⟨contractedCoreLinkPortsPadded d,
    contractedCoreLinkLengthsPadded d⟩

private theorem contractedCoreLinkData_count_eq_of_lengthCode_eq
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a}
    (d e : ContractedCoreLinkData c)
    (h : contractedCoreLinkLengthsPadded d =
      contractedCoreLinkLengthsPadded e) :
    d.linkCount.1 = e.linkCount.1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hiBound : d.linkCount.1 < 9 * a :=
      lt_of_lt_of_le hlt (Nat.le_of_lt_succ e.linkCount.2)
    let i : Fin (9 * a) := ⟨d.linkCount.1, hiBound⟩
    have hi := congrFun h i
    have hpos := e.linkLength_pos
      (⟨d.linkCount.1, hlt⟩ : Fin e.linkCount.1)
    have hv := congrArg Fin.val hi
    simp [contractedCoreLinkLengthsPadded, i, hlt] at hv
    omega
  · have hiBound : e.linkCount.1 < 9 * a :=
      lt_of_lt_of_le hgt (Nat.le_of_lt_succ d.linkCount.2)
    let i : Fin (9 * a) := ⟨e.linkCount.1, hiBound⟩
    have hi := congrFun h i
    have hpos := d.linkLength_pos
      (⟨e.linkCount.1, hgt⟩ : Fin d.linkCount.1)
    have hv : (d.linkLength ⟨e.linkCount.1, hgt⟩).val = 0 := by
      simpa [contractedCoreLinkLengthsPadded, i, hgt] using congrArg Fin.val hi
    exact (Nat.ne_of_gt hpos) hv

theorem contractedCoreLinkDataToRaw_injective
    {p a : ℕ} {c : ContractedCoreDegreeProfile p a} :
    Function.Injective
      (contractedCoreLinkDataToRaw (p := p) (a := a) (c := c)) := by
  intro d e hraw
  have hlengthCode : contractedCoreLinkLengthsPadded d =
      contractedCoreLinkLengthsPadded e := congrArg Prod.snd hraw
  have hcountVal :=
    contractedCoreLinkData_count_eq_of_lengthCode_eq d e hlengthCode
  have hcount : d.linkCount = e.linkCount := Fin.ext hcountVal
  cases d with
  | mk dc dp dl dlpos =>
    cases e with
    | mk ec ep el elpos =>
      dsimp only at hcount hcountVal
      subst ec
      have hlength : dl = el := by
        funext i
        have hiBound : i.1 < 9 * a := lt_of_lt_of_le i.2 (Nat.le_of_lt_succ dc.2)
        have hi := congrFun hlengthCode ⟨i.1, hiBound⟩
        simpa [contractedCoreLinkLengthsPadded, i.2] using hi
      have hportCode : contractedCoreLinkPortsPadded
            (ContractedCoreLinkData.mk dc dp dl dlpos) =
          contractedCoreLinkPortsPadded
            (ContractedCoreLinkData.mk dc ep el elpos) :=
        congrArg Prod.fst hraw
      have hports : dp = ep := by
        apply Function.Embedding.ext
        intro z
        let j := Fintype.equivFin (ContractedCoreLinkPortIndex dc.1) z
        have hjBound : j.1 < 36 * a := lt_of_lt_of_le j.2
          (contractedCoreLinkPortIndex_card_le
            (ContractedCoreLinkData.mk dc dp dl dlpos))
        let i : Fin (36 * a) := ⟨j.1, hjBound⟩
        have hi := congrFun hportCode i
        have hactive : i.1 < Fintype.card
            (ContractedCoreLinkPortIndex dc.1) := by
          simpa [i, j] using j.2
        have hjActive :
            (Fintype.equivFin (ContractedCoreLinkPortIndex dc.1) z).1 <
              dc.1 * 4 := by
          simpa [i, j, ContractedCoreLinkPortIndex, Nat.mul_comm] using hactive
        have hc : some (dp z) = some (ep z) :=
          (contractedCorePortOptionEmbedding c).injective
          (by
            simpa [contractedCoreLinkPortsPadded, i, j, hactive,
              hjActive] using hi)
        exact Option.some.inj hc
      subst el
      subst ep
      rfl

/-- Each fixed-profile link fiber occupies at most `45a` core digits. -/
theorem contractedCoreLinkData_card_le
    {p a : ℕ} (c : ContractedCoreDegreeProfile p a) :
    Fintype.card (ContractedCoreLinkData c) ≤
      (4 * p + 1) ^ (45 * a) := by
  calc
    Fintype.card (ContractedCoreLinkData c) ≤
        Fintype.card (ContractedCoreLinkRaw p a) :=
      Fintype.card_le_of_injective contractedCoreLinkDataToRaw
        contractedCoreLinkDataToRaw_injective
    _ = (4 * p + 1) ^ (36 * a) *
        (4 * p + 1) ^ (9 * a) := by
      simp only [ContractedCoreLinkRaw, Fintype.card_prod,
        Fintype.card_fun, Fintype.card_fin]
    _ = (4 * p + 1) ^ (45 * a) := by
      rw [← pow_add]
      congr 1
      omega

/-- Complete semantic topology over one retained degree profile. -/
structure ContractedCoreTopology {p a : ℕ}
    (c : ContractedCoreDegreeProfile p a) where
  portPairing : Pairing (Finset.univ : Finset (ContractedCorePort c))
  links : ContractedCoreLinkData c
  deriving Fintype

/-- A fixed profile has at most `63a` topology payload digits. -/
theorem contractedCoreTopology_card_le
    {p a : ℕ} (c : ContractedCoreDegreeProfile p a) :
    Fintype.card (ContractedCoreTopology c) ≤
      (4 * p + 1) ^ (63 * a) := by
  have hpair := Fintype.card_le_of_injective
    (contractedCorePairingEmbeddingOfCard (α := ContractedCorePort c)
      p a (by
        rw [contractedCorePort_card]
        exact c.totalDegree_le_parameter)
      (by
        rw [contractedCorePort_card]
        exact c.totalDegree_le_edges))
    (contractedCorePairingEmbeddingOfCard (α := ContractedCorePort c)
      p a (by
        rw [contractedCorePort_card]
        exact c.totalDegree_le_parameter)
      (by
        rw [contractedCorePort_card]
        exact c.totalDegree_le_edges)).injective
  have hpair' :
      Fintype.card (Pairing (Finset.univ : Finset (ContractedCorePort c))) ≤
        (4 * p + 1) ^ (18 * a) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using hpair
  have htop : Fintype.card (ContractedCoreTopology c) =
      Fintype.card (Pairing (Finset.univ : Finset (ContractedCorePort c))) *
        Fintype.card (ContractedCoreLinkData c) := by
    let e : ContractedCoreTopology c ≃
        Pairing (Finset.univ : Finset (ContractedCorePort c)) ×
          ContractedCoreLinkData c :=
      { toFun := fun t ↦ (t.portPairing, t.links)
        invFun := fun t ↦ ⟨t.1, t.2⟩
        left_inv := by intro t; cases t; rfl
        right_inv := by intro t; cases t; rfl }
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [htop]
  calc
    Fintype.card (Pairing (Finset.univ : Finset (ContractedCorePort c))) *
        Fintype.card (ContractedCoreLinkData c) ≤
        (4 * p + 1) ^ (18 * a) * (4 * p + 1) ^ (45 * a) :=
      Nat.mul_le_mul hpair' (contractedCoreLinkData_card_le c)
    _ = (4 * p + 1) ^ (63 * a) := by
      rw [← pow_add]
      congr 1
      omega

#print axioms contractedCorePortOptionEmbedding
#print axioms contractedCoreLinkDataToRaw_injective
#print axioms contractedCoreLinkData_card_le
#print axioms contractedCoreTopology_card_le

end

end Problem56
