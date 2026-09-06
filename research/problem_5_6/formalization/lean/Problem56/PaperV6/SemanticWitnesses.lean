import Problem56.PaperV6.FixedFrameExpected
import Problem56.PaperV6.GeneralCumulantsExpected
import Problem56.PaperV6.GeneralSamplingJointExpected

/-! Definitions-only witnesses: non-finite sample domains, probability mass,
and the distinction between the custom Euclidean norm and the sup norm. -/
open scoped BigOperators
open MeasureTheory

namespace Problem56.PaperV6

theorem l2_two_coordinates_squared :
    euclideanNorm (fun _ : Fin 2 ↦ (1 : ℝ)) ^ 2 = 2 := by
  norm_num [euclideanNorm, Fin.sum_univ_two, Real.sq_sqrt]

theorem bool_uniform_half :
    uniformProbability (fun b : Bool ↦ b = true) = 1 / 2 := by
  norm_num [uniformProbability, Finset.filter_insert, Finset.filter_singleton]

theorem singleton_uniform_mass :
    uniformProbability (fun _ : Unit ↦ True) = 1 := by
  norm_num [uniformProbability]

/-- An uncountable sample type is accepted without a finite-domain instance. -/
theorem real_sample_domain_finite_moments (c : Fin 2 → ℝ) :
    FiniteJointMoments (Measure.dirac (0 : ℝ)) (fun j (_ : ℝ) ↦ c j) := by
  intro B
  exact integrable_const _

theorem dirac_real_probability_normalization :
    (Measure.dirac (0 : ℝ)).real Set.univ = 1 := by simp

end Problem56.PaperV6
