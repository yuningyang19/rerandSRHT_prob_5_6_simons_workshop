import Problem56.GraphOperatorRegression

namespace Problem56.PaperV6

example : euclideanOperatorNorm (1 : Matrix (Fin 0) (Fin 0) ℝ) = 0 :=
  GraphOperatorRegression.zero_dimensional_domain_has_zero_norm _

example : euclideanOperatorNorm (1 : Matrix (Fin 0) (Fin 0) ℝ) ≠ 1 := by
  rw [GraphOperatorRegression.zero_dimensional_domain_has_zero_norm]
  norm_num

end Problem56.PaperV6
