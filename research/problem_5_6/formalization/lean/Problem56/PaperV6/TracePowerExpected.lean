import Problem56.Statements

namespace Problem56.PaperV6

/-- C main.tex 393--397: the rectangular cyclic trace identity used to pass
from the sampled Gram matrix to the ambient projection. No orthonormality or
diagonal-weight assumption is needed for this algebraic identity. The positive
power restriction is essential when the two dimensions differ. -/
def RectangularTracePowerExpected : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (W : Matrix ι ι ℝ) (j : ℕ), 0 < j →
    Matrix.trace ((X.transpose * W * X) ^ j) =
      Matrix.trace (((X * X.transpose) * W) ^ j)

/-- C eq:gram-centering. Bernoulli projection structure is unnecessary for
this exact algebraic bridge; nonzero normalization and frame orthonormality
are explicit. -/
def GramCenteringExpected : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (θ : ℝ),
    θ ≠ 0 → X.transpose * X = 1 →
    θ⁻¹ • (X.transpose * E * X) - 1 =
      θ⁻¹ • (X.transpose * (E - θ • 1) * X)

end Problem56.PaperV6
