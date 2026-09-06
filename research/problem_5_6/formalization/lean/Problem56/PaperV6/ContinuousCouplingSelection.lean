import Problem56.PaperV6.ContinuousCouplingExpected
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

def KeysOrdered {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    (u : α → ℝ) (K : FixedSubset α k) : Prop :=
  ∀ i, i ∈ K.val → ∀ j, j ∉ K.val → u i ≤ u j

theorem exists_keysOrdered {α : Type} [Fintype α] [DecidableEq α]
    (k : ℕ) (hk : k ≤ Fintype.card α) (u : α → ℝ) :
    ∃ K : FixedSubset α k, KeysOrdered u K := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hk
  letI : Nonempty (FixedSubset α k) := ⟨s, hs⟩
  obtain ⟨K, _, hK⟩ := Finset.exists_min_image
    (Finset.univ : Finset (FixedSubset α k)) (fun K ↦ ∑ i ∈ K.val, u i)
    Finset.univ_nonempty
  refine ⟨K, ?_⟩
  intro i hi j hj
  have hje : j ∉ K.val.erase i := fun h ↦ hj (Finset.mem_of_mem_erase h)
  let L : FixedSubset α k := ⟨insert j (K.val.erase i), by
    rw [Finset.card_insert_of_notMem hje, Finset.card_erase_of_mem hi]
    have hkpos : 0 < K.val.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hcard := K.property
    omega⟩
  have hmin := hK L (Finset.mem_univ L)
  have heq : (∑ a ∈ K.val, u a) = u i + ∑ a ∈ K.val.erase i, u a := by
    exact (Finset.add_sum_erase K.val u hi).symm
  change (∑ a ∈ K.val, u a) ≤ ∑ a ∈ insert j (K.val.erase i), u a at hmin
  rw [Finset.sum_insert hje, heq] at hmin
  linarith

theorem keysOrdered_measurableSet {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    (K : FixedSubset α k) : MeasurableSet {u : α → ℝ | KeysOrdered u K} := by
  simp only [KeysOrdered, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hj
  exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)

theorem exists_measurable_keysOrdered {α : Type} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : k ≤ Fintype.card α) [MeasurableSpace (FixedSubset α k)] :
    ∃ J : (α → ℝ) → FixedSubset α k, Measurable J ∧ ∀ u, KeysOrdered u (J u) := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hk
  let base : FixedSubset α k := ⟨s, hs⟩
  letI : Encodable (FixedSubset α k) := Fintype.toEncodable _
  let enum : ℕ → FixedSubset α k := fun n ↦ (Encodable.decode n).getD base
  have hen : Function.Surjective enum := Encodable.surjective_decode_getD _ base
  have hex : ∀ u : α → ℝ, ∃ n, KeysOrdered u (enum n) := by
    intro u
    obtain ⟨K, hK⟩ := exists_keysOrdered k hk u
    obtain ⟨n, rfl⟩ := hen K
    exact ⟨n, hK⟩
  refine ⟨fun u ↦ enum (Nat.find (hex u)), ?_, fun u ↦ Nat.find_spec (hex u)⟩
  exact Measurable.find (fun _ ↦ measurable_const)
    (fun n ↦ keysOrdered_measurableSet (enum n)) hex

theorem keysOrdered_unique {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    {u : α → ℝ} (hu : Function.Injective u) {K L : FixedSubset α k}
    (hK : KeysOrdered u K) (hL : KeysOrdered u L) : K = L := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le ?_ (by rw [K.property, L.property])
  intro i hi
  by_contra hiL
  have hLK : L.val ⊆ K.val := by
    intro j hj
    by_contra hjK
    have heq := hu (le_antisymm (hK i hi j hjK) (hL j hj i hiL))
    exact hiL (heq.symm ▸ hj)
  have heq : L.val = K.val := Finset.eq_of_subset_of_card_le hLK
    (by rw [K.property, L.property])
  exact hiL (heq.symm ▸ hi)

theorem keysOrdered_count_sandwich {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    {u : α → ℝ} {K : FixedSubset α k} (hK : KeysOrdered u K)
    (θminus θplus : ℝ)
    (hminus : (continuousThresholdSet θminus u).card ≤ k)
    (hplus : k ≤ (continuousThresholdSet θplus u).card) :
    continuousThresholdSet θminus u ⊆ K.val ∧
      K.val ⊆ continuousThresholdSet θplus u := by
  classical
  have hmem (θ : ℝ) (i : α) : i ∈ continuousThresholdSet θ u ↔ u i ≤ θ := by
    simp [continuousThresholdSet]
  constructor
  · intro i hi
    by_contra hiK
    have hsub : K.val ⊆ continuousThresholdSet θminus u := by
      intro j hj
      exact (hmem _ _).mpr ((hK j hj i hiK).trans ((hmem _ _).mp hi))
    have hlt : K.val.card < (continuousThresholdSet θminus u).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro heq
        exact hiK (heq.symm ▸ hi)⟩)
    rw [K.property] at hlt
    omega
  · intro i hi
    by_contra hiB
    have hiθ : θplus < u i := lt_of_not_ge (fun h ↦ hiB ((hmem _ _).mpr h))
    have hsub : continuousThresholdSet θplus u ⊆ K.val := by
      intro j hj
      by_contra hjK
      exact (not_lt_of_ge ((hK i hi j hjK).trans ((hmem _ _).mp hj))) hiθ
    have hlt : (continuousThresholdSet θplus u).card < K.val.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro heq
        exact hiB (heq.symm ▸ hi)⟩)
    rw [K.property] at hlt
    omega

end Problem56.PaperV6
