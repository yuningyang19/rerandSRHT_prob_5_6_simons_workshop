import Problem56.PaperV6.ContinuousCouplingBasics

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Problem56.PaperV6

instance continuousUnitUniform_nullSingleton : NullSingletonClass continuousUnitUniform := by
  unfold continuousUnitUniform
  infer_instance

theorem continuousUnitUniform_diagonal_null :
    (continuousUnitUniform.prod continuousUnitUniform) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  apply Measure.measure_prod_null_of_ae_null (measurableSet_eq_fun measurable_fst measurable_snd)
  filter_upwards [] with x
  have hset : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
    ext y
    simp [eq_comm]
  rw [hset, measure_singleton]
  rfl

theorem continuousKey_pair_no_tie {α : Type} [Fintype α] {i j : α} (hij : i ≠ j) :
    ∀ᵐ u ∂continuousKeyLaw α, u i ≠ u j := by
  have hind := (continuousKey_independent (α := α)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  rw [continuousKey_eval_law, continuousKey_eval_law] at hmap
  have hnull : (continuousKeyLaw α) {u | u i = u j} = 0 := by
    have h := congrArg (fun ν : Measure (ℝ × ℝ) ↦ ν {p | p.1 = p.2}) hmap
    rw [Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      (measurableSet_eq_fun measurable_fst measurable_snd),
      continuousUnitUniform_diagonal_null] at h
    exact h
  exact compl_mem_ae_iff.mpr hnull

theorem continuousKey_no_ties {α : Type} [Fintype α] :
    ∀ᵐ u ∂continuousKeyLaw α, Function.Injective u := by
  have h : ∀ᵐ u ∂continuousKeyLaw α, ∀ i j : α, i ≠ j → u i ≠ u j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hij).elim)
    · exact (continuousKey_pair_no_tie hij).mono (fun _ hu _ ↦ hu)
  filter_upwards [h] with u hu i j heq
  by_contra hij
  exact hu i j hij heq

theorem continuousKey_permutation_invariant {α : Type} [Fintype α] (p : Equiv.Perm α) :
    MeasurePreserving (fun u : α → ℝ ↦ fun i ↦ u (p.symm i))
      (continuousKeyLaw α) (continuousKeyLaw α) := by
  have h := measurePreserving_piCongrLeft (fun _ : α ↦ continuousUnitUniform) p
  have heq : (fun u : α → ℝ ↦ fun i ↦ u (p.symm i)) =
      MeasurableEquiv.piCongrLeft (fun _ : α ↦ ℝ) p := by
    funext u i
    have hh := MeasurableEquiv.piCongrLeft_apply_apply p (β := fun _ : α ↦ ℝ) u (p.symm i)
    simpa using hh.symm
  rw [heq]
  exact h

end Problem56.PaperV6
