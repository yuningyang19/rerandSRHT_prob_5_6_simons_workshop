import Problem56.GraphOperatorL2

/-!
Vertex weights in a scalar graph contraction can be represented by one
diagonal loop at each vertex.  This is the first exact modification needed by
the bridgeless graph-to-DAG conversion: it keeps indexed original edges
separate, works with vertex-dependent dimensions, and costs no operator norm
when the weights are bounded by one.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

abbrev WeightLoopEdge (ι ε : Type*) := ε ⊕ ι

def weightDiagonal {α : Type*} [DecidableEq α] (w : α → ℝ) : Matrix α α ℝ :=
  fun i j => if i = j then w i else 0

def weightLoopSrc {ι ε : Type*} (src : ε → ι) : WeightLoopEdge ι ε → ι
  | Sum.inl e => src e
  | Sum.inr v => v

def weightLoopDst {ι ε : Type*} (dst : ε → ι) : WeightLoopEdge ι ε → ι
  | Sum.inl e => dst e
  | Sum.inr v => v

noncomputable def weightLoopMatrix {ι ε : Type*} [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) :
    ∀ e : WeightLoopEdge ι ε,
      Matrix (Fin (dim (weightLoopSrc src e)))
        (Fin (dim (weightLoopDst dst e))) ℝ
  | Sum.inl e => M e
  | Sum.inr v => weightDiagonal (w v)

theorem euclideanOperatorNorm_weightDiagonal_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    euclideanOperatorNorm (weightDiagonal w) ≤ 1 := by
  apply euclideanOperatorNorm_le_of_energy_bound _ 1 (by norm_num)
  intro x
  have hmul : (weightDiagonal w).mulVec x = fun i => w i * x i := by
    ext i
    simp [weightDiagonal, Matrix.mulVec, dotProduct]
  rw [hmul]
  simp only [one_pow, one_mul]
  apply Finset.sum_le_sum
  intro i _
  have habs : |w i| ^ 2 ≤ 1 :=
    (sq_le_one_iff₀ (abs_nonneg (w i))).2 (hw i)
  have hwi : w i ^ 2 ≤ 1 := by simpa only [sq_abs] using habs
  calc
    (w i * x i) ^ 2 = w i ^ 2 * x i ^ 2 := by ring
    _ ≤ 1 * x i ^ 2 :=
      mul_le_mul_of_nonneg_right hwi (sq_nonneg (x i))
    _ = x i ^ 2 := one_mul _

theorem graphContraction_weightLoopMatrix
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) :
    graphContraction dim (weightLoopSrc src) (weightLoopDst dst)
        (weightLoopMatrix dim src dst M w) (fun _ _ => 1) =
      graphContraction dim src dst M w := by
  classical
  simp only [graphContraction]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Fintype.prod_sum_type]
  simp only [weightLoopSrc, weightLoopDst, weightLoopMatrix,
    Finset.prod_const_one, mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp [weightDiagonal]

theorem weightLoopMatrix_norm_product_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (hweight : ∀ v i, |w v i| ≤ 1) :
    (∏ e : WeightLoopEdge ι ε,
        euclideanOperatorNorm (weightLoopMatrix dim src dst M w e)) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [Fintype.prod_sum_type]
  simp only [weightLoopMatrix]
  have hdiag : (∏ v, euclideanOperatorNorm (weightDiagonal (w v))) ≤ 1 := by
    exact Finset.prod_le_one
      (fun v _ => euclideanOperatorNorm_nonneg (weightDiagonal (w v)))
      (fun v _ => euclideanOperatorNorm_weightDiagonal_le_one (w v) (hweight v))
  have horig : 0 ≤ ∏ e, euclideanOperatorNorm (M e) :=
    Finset.prod_nonneg fun e _ => euclideanOperatorNorm_nonneg (M e)
  exact mul_le_of_le_one_right horig hdiag

end Problem56

#print axioms Problem56.euclideanOperatorNorm_weightDiagonal_le_one
#print axioms Problem56.graphContraction_weightLoopMatrix
#print axioms Problem56.weightLoopMatrix_norm_product_le
