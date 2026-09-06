import Problem56.Definitions

/-! Pairing count and parallel-edge multiplicity product bounds. -/

open scoped BigOperators

namespace Problem56

private theorem pairing_existsUnique_mate {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    ∃! y, y ∈ P.1.part x ∧ y ≠ x := by
  have hxpart : x ∈ P.1.part x := P.1.mem_part hx
  have hcard : (P.1.part x).card = 2 := P.2 _ (P.1.part_mem.2 hx)
  have herase : ((P.1.part x).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxpart, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp herase
  refine ⟨y, ?_, ?_⟩
  · have hyerase : y ∈ (P.1.part x).erase x := by rw [hy]; simp
    exact ⟨Finset.mem_of_mem_erase hyerase, Finset.ne_of_mem_erase hyerase⟩
  · intro z hz
    have hzerase : z ∈ (P.1.part x).erase x :=
      Finset.mem_erase.mpr ⟨hz.2, hz.1⟩
    rw [hy] at hzerase
    simpa using hzerase

private def pairingMate {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : α :=
  Finset.choose (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)

private theorem pairingMate_mem {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : pairingMate P x hx ∈ P.1.part x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)).1

private theorem pairingMate_ne {α : Type*} [DecidableEq α] {S : Finset α}
    (P : Pairing S) (x : α) (hx : x ∈ S) : pairingMate P x hx ≠ x :=
  (Finset.choose_spec (fun y ↦ y ≠ x) (P.1.part x)
    (pairing_existsUnique_mate P x hx)).2

private theorem pairingMate_mem_support {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    pairingMate P x hx ∈ S :=
  P.1.part_subset x (pairingMate_mem P x hx)

private theorem pairingMate_involutive {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    pairingMate P (pairingMate P x hx) (pairingMate_mem_support P x hx) = x := by
  let y := pairingMate P x hx
  have hyPart : y ∈ P.1.part x := pairingMate_mem P x hx
  have hyS : y ∈ S := pairingMate_mem_support P x hx
  have hpart : P.1.part y = P.1.part x :=
    P.1.part_eq_of_mem (P.1.part_mem.2 hx) hyPart
  apply (pairing_existsUnique_mate P y hyS).unique
  · exact (Finset.choose_spec (fun z ↦ z ≠ y) (P.1.part y)
      (pairing_existsUnique_mate P y hyS))
  · constructor
    · rw [hpart]
      exact P.1.mem_part hx
    · exact (pairingMate_ne P x hx).symm

private theorem pairing_part_eq_pair {α : Type*} [DecidableEq α]
    {S : Finset α} (P : Pairing S) (x : α) (hx : x ∈ S) :
    P.1.part x = {x, pairingMate P x hx} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact P.1.mem_part hx
    · exact pairingMate_mem P x hx
  · rw [P.2 _ (P.1.part_mem.2 hx)]
    simp [(pairingMate_ne P x hx).symm]

private def fullPairingMate {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) : Fin ell :=
  pairingMate P x (Finset.mem_univ x)

private theorem fullPairingMate_ne {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) :
    fullPairingMate P x ≠ x :=
  pairingMate_ne P x (Finset.mem_univ x)

private theorem fullPairingMate_involutive {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) :
    fullPairingMate P (fullPairingMate P x) = x := by
  unfold fullPairingMate
  exact pairingMate_involutive P x (Finset.mem_univ x)

private theorem fullPairingMate_injective {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) :
    Function.Injective (fullPairingMate P) := by
  intro x y hxy
  have := congrArg (fullPairingMate P) hxy
  simpa [fullPairingMate_involutive] using this

private def pairingLowerSet {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) : Finset (Fin ell) :=
  Finset.univ.filter fun x ↦ x < fullPairingMate P x

private theorem pairingLowerSet_mate_not_mem {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) {x : Fin ell}
    (hx : x ∈ pairingLowerSet P) : fullPairingMate P x ∉ pairingLowerSet P := by
  simp only [pairingLowerSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rw [fullPairingMate_involutive]
  exact not_lt_of_ge hx.le

private theorem pairingLowerSet_mate_mem_of_not_mem {ell : ℕ}
    (P : Pairing (Finset.univ : Finset (Fin ell))) {x : Fin ell}
    (hx : x ∉ pairingLowerSet P) : fullPairingMate P x ∈ pairingLowerSet P := by
  rw [pairingLowerSet, Finset.mem_filter] at hx ⊢
  simp only [Finset.mem_univ, true_and] at hx ⊢
  rw [fullPairingMate_involutive]
  exact lt_of_le_of_ne (le_of_not_gt hx) (fullPairingMate_ne P x)

private theorem pairingLowerSet_card_bound (s t ell : ℕ)
    (hell : ell ≤ 4 * t + 12 * s + 2)
    (P : Pairing (Finset.univ : Finset (Fin ell))) :
    (pairingLowerSet P).card ≤ 2 * t + 6 * s + 1 := by
  classical
  let upper := (pairingLowerSet P).image (fullPairingMate P)
  have hcardUpper : upper.card = (pairingLowerSet P).card := by
    exact Finset.card_image_of_injective _ (fullPairingMate_injective P)
  have hdisjoint : Disjoint (pairingLowerSet P) upper := by
    rw [Finset.disjoint_left]
    intro x hx hxu
    change x ∈ (pairingLowerSet P).image (fullPairingMate P) at hxu
    rw [Finset.mem_image] at hxu
    obtain ⟨y, hy, hyx⟩ := hxu
    subst x
    exact pairingLowerSet_mate_not_mem P hy hx
  have hunion : (pairingLowerSet P ∪ upper).card ≤ ell := by
    calc
      (pairingLowerSet P ∪ upper).card ≤
          (Finset.univ : Finset (Fin ell)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = ell := by simp
  rw [Finset.card_union_of_disjoint hdisjoint, hcardUpper] at hunion
  omega

private def pairingLowerCode (s t ell : ℕ)
    (P : Pairing (Finset.univ : Finset (Fin ell))) :
    Fin (2 * t + 6 * s + 1) → Option (Fin ell) := fun i ↦
  if hi : i.1 < (pairingLowerSet P).card then
    let j : Fin (pairingLowerSet P).card := ⟨i.1, hi⟩
    let x : Fin ell := (pairingLowerSet P).orderEmbOfFin rfl j
    some (fullPairingMate P x)
  else
    none

private theorem pairingLowerCode_complement_support (s t ell : ℕ)
    (hell : ell ≤ 4 * t + 12 * s + 2)
    (P : Pairing (Finset.univ : Finset (Fin ell))) (x : Fin ell) :
    x ∉ pairingLowerSet P ↔ ∃ i, pairingLowerCode s t ell P i = some x := by
  constructor
  · intro hx
    let y := fullPairingMate P x
    have hy : y ∈ pairingLowerSet P := pairingLowerSet_mate_mem_of_not_mem P hx
    let j : Fin (pairingLowerSet P).card :=
      ((pairingLowerSet P).orderIsoOfFin rfl).symm ⟨y, hy⟩
    have hj : j.1 < 2 * t + 6 * s + 1 :=
      lt_of_lt_of_le j.2 (pairingLowerSet_card_bound s t ell hell P)
    let i : Fin (2 * t + 6 * s + 1) := ⟨j.1, hj⟩
    refine ⟨i, ?_⟩
    have henum : (pairingLowerSet P).orderEmbOfFin rfl j = y := by
      exact congrArg Subtype.val
        (((pairingLowerSet P).orderIsoOfFin rfl).apply_symm_apply ⟨y, hy⟩)
    simp [pairingLowerCode, i, j, henum, y, fullPairingMate_involutive]
  · rintro ⟨i, hi⟩
    simp only [pairingLowerCode] at hi
    split at hi
    · let j : Fin (pairingLowerSet P).card :=
        ⟨i.1, ‹i.1 < (pairingLowerSet P).card›⟩
      let y : Fin ell := (pairingLowerSet P).orderEmbOfFin rfl j
      have hy : y ∈ pairingLowerSet P :=
        (pairingLowerSet P).orderEmbOfFin_mem rfl j
      have hnot : fullPairingMate P y ∉ pairingLowerSet P :=
        pairingLowerSet_mate_not_mem P hy
      have heq : fullPairingMate P y = x := Option.some.inj hi
      rwa [heq] at hnot
    · simp at hi

private theorem pairingLowerCode_injective (s t ell : ℕ)
    (hell : ell ≤ 4 * t + 12 * s + 2) :
    Function.Injective
      (pairingLowerCode s t ell :
        Pairing (Finset.univ : Finset (Fin ell)) →
          Fin (2 * t + 6 * s + 1) → Option (Fin ell)) := by
  intro P R hcode
  have hlower : pairingLowerSet P = pairingLowerSet R := by
    ext x
    constructor
    · intro hxP
      by_contra hxR
      obtain ⟨i, hi⟩ :=
        (pairingLowerCode_complement_support s t ell hell R x).mp hxR
      have hiP : pairingLowerCode s t ell P i = some x := by
        rw [hcode]
        exact hi
      exact ((pairingLowerCode_complement_support s t ell hell P x).mpr ⟨i, hiP⟩) hxP
    · intro hxR
      by_contra hxP
      obtain ⟨i, hi⟩ :=
        (pairingLowerCode_complement_support s t ell hell P x).mp hxP
      have hiR : pairingLowerCode s t ell R i = some x := by
        rw [← hcode]
        exact hi
      exact ((pairingLowerCode_complement_support s t ell hell R x).mpr ⟨i, hiR⟩) hxR
  have hmateLower : ∀ (x : Fin ell), x ∈ pairingLowerSet P →
      fullPairingMate P x = fullPairingMate R x := by
    intro x hx
    have hxR : x ∈ pairingLowerSet R := by rw [← hlower]; exact hx
    let j : Fin (pairingLowerSet P).card :=
      ((pairingLowerSet P).orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hj : j.1 < 2 * t + 6 * s + 1 :=
      lt_of_lt_of_le j.2 (pairingLowerSet_card_bound s t ell hell P)
    let i : Fin (2 * t + 6 * s + 1) := ⟨j.1, hj⟩
    have henumP : (pairingLowerSet P).orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val
        (((pairingLowerSet P).orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    have hi : i.1 < (pairingLowerSet P).card := j.2
    have hiR : i.1 < (pairingLowerSet R).card := by
      rw [← hlower]
      exact hi
    have henumR :
        (pairingLowerSet R).orderEmbOfFin rfl
          (⟨i.1, hiR⟩ : Fin (pairingLowerSet R).card) = x := by
      simpa [Finset.orderEmbOfFin_apply, hlower, i] using henumP
    have hc := congrFun hcode i
    simpa [pairingLowerCode, i, j, hi, hiR, henumP, henumR] using hc
  have hmate : ∀ x : Fin ell, fullPairingMate P x = fullPairingMate R x := by
    intro x
    by_cases hx : x ∈ pairingLowerSet P
    · exact hmateLower x hx
    · let y := fullPairingMate P x
      have hy : y ∈ pairingLowerSet P := pairingLowerSet_mate_mem_of_not_mem P hx
      have hyMate : fullPairingMate R y = x := by
        rw [← hmateLower y hy]
        exact fullPairingMate_involutive P x
      calc
        fullPairingMate P x = y := rfl
        _ = fullPairingMate R (fullPairingMate R y) :=
          (fullPairingMate_involutive R y).symm
        _ = fullPairingMate R x := congrArg (fullPairingMate R) hyMate
  have hPRval : P.1 = R.1 := by
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      obtain ⟨x, hx⟩ := P.1.nonempty_of_mem_parts hB
      have hPx : P.1.part x = B := P.1.part_eq_of_mem hB hx
      rw [← hPx, pairing_part_eq_pair P x (Finset.mem_univ x)]
      change {x, fullPairingMate P x} ∈ R.1.parts
      rw [hmate x]
      have hpartR : R.1.part x = {x, fullPairingMate R x} := by
        simpa [fullPairingMate] using pairing_part_eq_pair R x (Finset.mem_univ x)
      rw [← hpartR]
      exact R.1.part_mem.2 (Finset.mem_univ x)
    · intro hB
      obtain ⟨x, hx⟩ := R.1.nonempty_of_mem_parts hB
      have hRx : R.1.part x = B := R.1.part_eq_of_mem hB hx
      rw [← hRx, pairing_part_eq_pair R x (Finset.mem_univ x)]
      change {x, fullPairingMate R x} ∈ P.1.parts
      rw [← hmate x]
      have hpartP : P.1.part x = {x, fullPairingMate P x} := by
        simpa [fullPairingMate] using pairing_part_eq_pair P x (Finset.mem_univ x)
      rw [← hpartP]
      exact P.1.part_mem.2 (Finset.mem_univ x)
  exact Subtype.ext hPRval

private theorem parallelMultiplicityProductBound (p s : ℕ) :
    ∀ (g : ℕ), g ≤ p → ∀ a : Fin g → ℕ,
      (∀ e, 0 < a e ∧ Even (a e)) →
      (∑ e, (a e - 4)) ≤ 2 * s →
      (∏ e, 3 * (4 * p) ^ ((a e - 4) / 2)) ≤
        3 ^ p * (4 * p + 1) ^ s := by
  intro g hg a ha hbudget
  have hfour : Even (4 : ℕ) := ⟨2, rfl⟩
  have hdiv : ∀ e ∈ (Finset.univ : Finset (Fin g)), 2 ∣ (a e - 4) := by
    intro e _
    by_cases hfourle : 4 ≤ a e
    · exact even_iff_two_dvd.mp ((Nat.even_sub hfourle).2
        ⟨fun _ ↦ hfour, fun _ ↦ (ha e).2⟩)
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (lt_of_not_ge hfourle))]
      exact dvd_zero 2
  have hhalf : (∑ e, (a e - 4) / 2) ≤ s := by
    rw [← Nat.sum_div hdiv]
    exact Nat.div_le_of_le_mul hbudget
  calc
    (∏ e, 3 * (4 * p) ^ ((a e - 4) / 2)) =
        3 ^ g * (4 * p) ^ (∑ e, (a e - 4) / 2) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum]
    _ ≤ 3 ^ p * (4 * p + 1) ^ s := by
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_right (by omega) hg)
        (pow_le_pow (by omega) (by omega) hhalf)

theorem loop_parallel_pairing_bound (p s t ell : ℕ)
    (hp : 2 ≤ p) (hell : ell ≤ 4 * t + 12 * s + 2) (hellp : ell ≤ 2 * p) :
    Fintype.card (Pairing (Finset.univ : Finset (Fin ell))) ≤
        (4 * p + 1) ^ (2 * t + 6 * s + 1) ∧
    (∀ (g : ℕ), g ≤ p → ∀ a : Fin g → ℕ,
      (∀ e, 0 < a e ∧ Even (a e)) →
      (∑ e, (a e - 4)) ≤ 2 * s →
      (∏ e, 3 * (4 * p) ^ ((a e - 4) / 2)) ≤
        3 ^ p * (4 * p + 1) ^ s) := by
  have _hp := hp
  constructor
  · calc
      Fintype.card (Pairing (Finset.univ : Finset (Fin ell))) ≤
          Fintype.card (Fin (2 * t + 6 * s + 1) → Option (Fin ell)) :=
        Fintype.card_le_of_injective (pairingLowerCode s t ell)
          (pairingLowerCode_injective s t ell hell)
      _ = (ell + 1) ^ (2 * t + 6 * s + 1) := by
        simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
      _ ≤ (4 * p + 1) ^ (2 * t + 6 * s + 1) :=
        Nat.pow_le_pow_left (by omega) _
  · exact parallelMultiplicityProductBound p s

end Problem56
