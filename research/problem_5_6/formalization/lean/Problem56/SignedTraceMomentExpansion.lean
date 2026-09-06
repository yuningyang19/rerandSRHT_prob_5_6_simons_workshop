import Problem56.SignedTraceEntryCumulant
import Problem56.SignedTraceExpectationExpansion

/-!
# Exact selector/entry-partition expansion of the signed trace

This module joins the finite cyclic trace/expectation expansion to the full
moment--cumulant inverse for the centered random-projection entries.  It still
contains no triangle inequality and no relaxation of injective row labels.
-/

open scoped BigOperators Matrix

namespace Problem56

set_option maxHeartbeats 8000000

noncomputable section

/-- Exact signed trace expansion into a selector moment times a sum over all
entry cumulant partitions, with the absolute value still outside the entire
finite expression. -/
theorem signBernoulliExpectation_trace_eq_selector_entryPartition_sum
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ) (hp : 1 ≤ p) :
    signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p))) =
      ∑ x : Fin (2 * p) → WalshIndex m,
        bernoulliExpectation θ (fun e ↦
          ∏ f : Fin (2 * p), centeredBernoulliValue θ e (x f)) *
        (∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
          ∏ B ∈ P.parts,
            jointCumulantOn (fun f : B ↦
              centeredRandomProjectionEntry V
                (x f.1) (x (cyclicSucc f.1)))) := by
  rw [signBernoulliExpectation_trace_centered_product_pow_expansion V θ hp]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact signPairExpectation_cyclic_centeredProjection_product_expansion V x

#print axioms signBernoulliExpectation_trace_eq_selector_entryPartition_sum

end

end Problem56
