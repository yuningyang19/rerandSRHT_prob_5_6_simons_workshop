import Problem56.PaperV6.TracePower

-- Independent expanded client statements, C389--397.
namespace Problem56.PaperV6.ReversePass2Checks

example (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (W : Matrix ι ι ℝ) (j : ℕ) (hj : 0 < j) :
    Matrix.trace ((X.transpose * W * X) ^ j) =
      Matrix.trace (((X * X.transpose) * W) ^ j) :=
  Problem56.PaperV6.rectangular_trace_power ι κ X W j hj

example (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (θ : ℝ)
    (hθ : θ ≠ 0) (hX : X.transpose * X = 1) :
    θ⁻¹ • (X.transpose * E * X) - 1 =
      θ⁻¹ • (X.transpose * (E - θ • 1) * X) :=
  Problem56.PaperV6.gram_centering ι κ X E θ hθ hX
end Problem56.PaperV6.ReversePass2Checks
