import Problem56.PaperV6.GeneralSamplingExpected

/-!
The finite-noise law bridge for frozen v6 `lem:sampling`.
The underlying probability space is arbitrary. Independence is used only for
the intersection of a frame event with one sampling singleton; the finitely
many disjoint intersections exhaust the joint event.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Function

namespace Problem56.PaperV6

/-- An arbitrary independent realization has exactly the finite weighted
failure probability specified by its sampling marginals. -/
theorem finiteNoiseFailureLaw : FiniteNoiseFailureLawExpected := by
  classical
  intro Ω α β _ _ _ _ _ _ μ _ r X S q event hX hS hInd hEvent _hq _hqsum hMarg
  let A : β → Set Ω := fun b ↦ {ω | event (X ω) b}
  let B : β → Set Ω := fun b ↦ {ω | S ω = b}
  have hA : ∀ b, MeasurableSet (A b) := fun b ↦ (hEvent b).preimage hX
  have hB : ∀ b, MeasurableSet (B b) := fun b ↦
    hS (measurableSet_singleton b)
  have hUnion : {ω | event (X ω) (S ω)} = ⋃ b, A b ∩ B b := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, A, B]
    exact ⟨fun h ↦ ⟨S ω, h, rfl⟩, fun ⟨b, h, hb⟩ ↦ hb.symm ▸ h⟩
  have hDisjoint : Pairwise (Disjoint on fun b ↦ A b ∩ B b) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    intro ω hb hc
    exact hbc (hb.2.symm.trans hc.2)
  have hProduct : ∀ b, μ.real (A b ∩ B b) = μ.real (A b) * q b := by
    intro b
    have h := hInd.measure_inter_preimage_eq_mul
      {a : α → Fin r → ℝ | event a b} {b} (hEvent b) (measurableSet_singleton b)
    change μ (A b ∩ B b) = μ (A b) * μ (B b) at h
    have hReal : μ.real (A b ∩ B b) = μ.real (A b) * μ.real (B b) := by
      simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
    rw [hReal, hMarg b]
  have hIntegrable : ∀ b, Integrable (fun ω ↦ if event (X ω) b then q b else 0) μ := by
    intro b
    change Integrable ((A b).indicator (fun _ ↦ q b)) μ
    exact (integrable_const (q b)).indicator (hA b)
  have hIntegral : ∀ b, (∫ ω, if event (X ω) b then q b else 0 ∂μ) =
      μ.real (A b) * q b := by
    intro b
    simpa only [Set.indicator, Set.mem_ofPred_eq, A, smul_eq_mul] using
      (integral_indicator_const (μ := μ) (q b) (hA b))
  rw [hUnion, measureReal_iUnion_fintype hDisjoint (fun b ↦ (hA b).inter (hB b)),
    integral_finsetSum _ (fun b _ ↦ hIntegrable b)]
  exact Finset.sum_congr rfl (fun b _ ↦ (hProduct b).trans (hIntegral b).symm)

end Problem56.PaperV6
