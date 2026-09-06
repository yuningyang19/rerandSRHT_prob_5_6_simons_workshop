import Problem56.PaperV6.TracePowerExpected

namespace Problem56.PaperV6

theorem rectangular_mul_pow_succ {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ) (j : ℕ) :
    (A * B) ^ (j + 1) = A * (B * A) ^ j * B := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (A * B) (j + 1), ih, pow_succ (B * A) j]
    simp only [Matrix.mul_assoc]

theorem rectangular_trace_mul_pow {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ) (j : ℕ) (hj : 0 < j) :
    Matrix.trace ((A * B) ^ j) = Matrix.trace ((B * A) ^ j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [rectangular_mul_pow_succ]
  rw [Matrix.trace_mul_comm (A * (B * A) ^ k) B]
  rw [← Matrix.mul_assoc, ← pow_succ']

theorem rectangular_trace_power : RectangularTracePowerExpected := by
  intro ι κ _ _ _ _ X W j hj
  simpa only [Matrix.mul_assoc] using rectangular_trace_mul_pow (X.transpose * W) X j hj

theorem gram_centering : GramCenteringExpected := by
  intro ι κ _ _ _ _ X E θ hθ hX
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hX, smul_sub, smul_smul, inv_mul_cancel₀ hθ, one_smul]

end Problem56.PaperV6
