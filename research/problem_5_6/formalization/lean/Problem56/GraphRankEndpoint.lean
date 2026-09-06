import Problem56.GraphOperatorL2

/-!
Small endpoint estimate used after the bridgeless graph has been converted to
an operator between two genuine rank-`r` vertices.  It is kept independent of
the still-open conversion and rank-edge interfaces.
-/

open scoped BigOperators Matrix

namespace Problem56

theorem euclideanNorm_const_one_fin_sq (r : ℕ) :
    euclideanNorm (fun _ : Fin r => (1 : ℝ)) ^ 2 = r := by
  rw [euclideanNorm_eq_norm_toLp, EuclideanSpace.real_norm_sq_eq]
  simp

/-- Pairing an `r × r` matrix with the two all-ones boundary vectors costs
exactly the product of their two `sqrt r` norms. -/
theorem abs_sum_all_entries_le_card_mul_operatorNorm
    (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) :
    |∑ a, ∑ b, A a b| ≤ (r : ℝ) * euclideanOperatorNorm A := by
  let one : Fin r → ℝ := fun _ => 1
  have hpair :
      (∑ a, ∑ b, A a b) =
        @inner ℝ (EuclideanSpace ℝ (Fin r)) _
          (WithLp.toLp 2 one) (WithLp.toLp 2 (A.mulVec one)) := by
    simp [one, PiLp.inner_apply, RCLike.inner_apply, Matrix.mulVec, dotProduct]
  rw [hpair]
  have hcs := abs_real_inner_le_norm
    (WithLp.toLp 2 one) (WithLp.toLp 2 (A.mulVec one))
  have hact :
      ‖WithLp.toLp 2 (A.mulVec one)‖ ≤
        euclideanOperatorNorm A * ‖WithLp.toLp 2 one‖ := by
    simpa [← euclideanNorm_eq_norm_toLp] using
      euclideanNorm_mulVec_le A one
  calc
    |@inner ℝ (EuclideanSpace ℝ (Fin r)) _
        (WithLp.toLp 2 one) (WithLp.toLp 2 (A.mulVec one))| ≤
        ‖WithLp.toLp 2 one‖ * ‖WithLp.toLp 2 (A.mulVec one)‖ := hcs
    _ ≤ ‖WithLp.toLp 2 one‖ *
        (euclideanOperatorNorm A * ‖WithLp.toLp 2 one‖) :=
      mul_le_mul_of_nonneg_left hact (norm_nonneg _)
    _ = (r : ℝ) * euclideanOperatorNorm A := by
      have hone : ‖WithLp.toLp 2 one‖ ^ 2 = (r : ℝ) := by
        simpa [one, euclideanNorm_eq_norm_toLp] using
          euclideanNorm_const_one_fin_sq r
      rw [show ‖WithLp.toLp 2 one‖ *
          (euclideanOperatorNorm A * ‖WithLp.toLp 2 one‖) =
          ‖WithLp.toLp 2 one‖ ^ 2 * euclideanOperatorNorm A by ring,
        hone]

theorem abs_sum_all_entries_le_card_mul_operatorNorm_of_dim_eq
    (a b r : ℕ) (ha : a = r) (hb : b = r)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    |∑ i, ∑ j, A i j| ≤ (r : ℝ) * euclideanOperatorNorm A := by
  subst a
  subst b
  exact abs_sum_all_entries_le_card_mul_operatorNorm r A

#print axioms abs_sum_all_entries_le_card_mul_operatorNorm
#print axioms abs_sum_all_entries_le_card_mul_operatorNorm_of_dim_eq

end Problem56
