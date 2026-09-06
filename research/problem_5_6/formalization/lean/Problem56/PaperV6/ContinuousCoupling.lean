import Problem56.PaperV6.ContinuousCouplingNoTies
import Problem56.PaperV6.ContinuousCouplingSelection
import Mathlib.Logic.Equiv.Sum

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

theorem exists_perm_fixedSubsets {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    (K L : FixedSubset α k) :
    ∃ p : Equiv.Perm α, ∀ i, p i ∈ L.val ↔ i ∈ K.val := by
  classical
  let e : {i // i ∈ K.val} ≃ {i // i ∈ L.val} :=
    Fintype.equivOfCardEq (by simp [K.property, L.property])
  let ec : {i // i ∉ K.val} ≃ {i // i ∉ L.val} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
      simp [K.property, L.property])
  let p : Equiv.Perm α := (Equiv.sumCompl (fun i ↦ i ∈ K.val)).symm.trans
    ((e.sumCongr ec).trans (Equiv.sumCompl (fun i ↦ i ∈ L.val)))
  refine ⟨p, ?_⟩
  intro i
  by_cases hi : i ∈ K.val
  · have hp : p i = (e ⟨i, hi⟩).val := by
      simp [p, Equiv.sumCompl_symm_apply_of_pos hi]
    rw [hp]
    exact iff_of_true (e ⟨i, hi⟩).property hi
  · have hp : p i = (ec ⟨i, hi⟩).val := by
      simp [p, Equiv.sumCompl_symm_apply_of_neg hi]
    rw [hp]
    exact iff_of_false (ec ⟨i, hi⟩).property hi

theorem keysOrdered_relabel {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    (K L : FixedSubset α k) (p : Equiv.Perm α)
    (hp : ∀ i, p i ∈ L.val ↔ i ∈ K.val) (u : α → ℝ) :
    KeysOrdered (fun i ↦ u (p.symm i)) L ↔ KeysOrdered u K := by
  constructor
  · intro h i hi j hj
    have hle := h (p i) ((hp i).mpr hi) (p j) (fun h ↦ hj ((hp j).mp h))
    simpa using hle
  · intro h i hi j hj
    have hiK : p.symm i ∈ K.val := (hp (p.symm i)).mp (by simpa using hi)
    have hjK : p.symm j ∉ K.val := fun hmem ↦
      hj (by simpa using (hp (p.symm j)).mpr hmem)
    exact h _ hiK _ hjK

theorem keysOrdered_equal_probability {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    (K L : FixedSubset α k) :
    (continuousKeyLaw α).real {u | KeysOrdered u K} =
      (continuousKeyLaw α).real {u | KeysOrdered u L} := by
  obtain ⟨p, hp⟩ := exists_perm_fixedSubsets K L
  have hmap := (continuousKey_permutation_invariant p).map_eq
  have h := congrArg (fun ν : Measure (α → ℝ) ↦ ν {u | KeysOrdered u L}) hmap
  rw [Measure.map_apply (continuousKey_permutation_invariant p).measurable
    (keysOrdered_measurableSet L)] at h
  have hset : (fun u : α → ℝ ↦ fun i ↦ u (p.symm i)) ⁻¹' {u | KeysOrdered u L} =
      {u | KeysOrdered u K} := by
    ext u
    exact keysOrdered_relabel K L p hp u
  rw [hset] at h
  exact congrArg ENNReal.toReal h

theorem keysOrdered_uniform {α : Type} [Fintype α] [DecidableEq α] {k : ℕ}
    [MeasurableSpace (FixedSubset α k)] [MeasurableSingletonClass (FixedSubset α k)]
    (J : (α → ℝ) → FixedSubset α k) (hJ : Measurable J)
    (hord : ∀ u, KeysOrdered u (J u)) (K : FixedSubset α k) :
    (continuousKeyLaw α).real {u | J u = K} = 1 / Fintype.card (FixedSubset α k) := by
  classical
  letI : Nonempty (FixedSubset α k) := ⟨K⟩
  have hfiber (L : FixedSubset α k) : {u | J u = L} =ᵐ[continuousKeyLaw α]
      {u | KeysOrdered u L} := by
    filter_upwards [continuousKey_no_ties (α := α)] with u hu
    change (J u = L) = KeysOrdered u L
    apply propext
    constructor
    · intro heq
      simpa only [heq] using hord u
    · exact fun h ↦ keysOrdered_unique hu (hord u) h
  have hequal (L : FixedSubset α k) :
      (continuousKeyLaw α).real {u | J u = L} = (continuousKeyLaw α).real {u | J u = K} := by
    rw [measureReal_congr (hfiber L), measureReal_congr (hfiber K)]
    exact keysOrdered_equal_probability L K
  have htotal : (∑ L : FixedSubset α k, (continuousKeyLaw α).real {u | J u = L}) = 1 := by
    have h := sum_measureReal_preimage_singleton (μ := continuousKeyLaw α)
      (f := J) Finset.univ (fun L _ ↦ hJ (measurableSet_singleton L))
    have hsets (L : FixedSubset α k) : J ⁻¹' {L} = {u | J u = L} := by
      ext u
      simp
    simp_rw [hsets] at h
    simpa using h
  simp_rw [hequal] at htotal
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hn : (Fintype.card (FixedSubset α k) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (eq_div_iff hn).mpr
  nlinarith

/-- Literal continuous-uniform common-order coupling used in frozen C. -/
theorem continuousCoupling : ContinuousCouplingExpected := by
  intro α _ _ k hk _ _ _ _
  refine ⟨inferInstance, continuousKey_eval_law, continuousKey_independent,
    continuousKey_no_ties, ?_⟩
  obtain ⟨J, hJ, hord⟩ := exists_measurable_keysOrdered hk
  refine ⟨J, hJ, hord, keysOrdered_uniform J hJ hord,
    continuousThreshold_measurable, continuousThreshold_law, ?_, ?_⟩
  · intro u θminus θplus hminus hplus
    exact keysOrdered_count_sandwich (hord u) θminus θplus hminus hplus
  · intro Ω _ μ _ r X hX
    exact ⟨continuousKey_frame_independent μ X J hX hJ,
      fun θ ↦ continuousKey_frame_independent μ X (continuousThreshold θ) hX
        (continuousThreshold_measurable θ)⟩

end Problem56.PaperV6
