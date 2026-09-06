import Problem56.Definitions

/-!
# Finite cyclic trace expansion

An exact finite-index expansion of a positive matrix power trace.  The
recursive path representation keeps the reindexing explicit and is intended
for the selector-equality expansion in the signed-trace proof.
-/

namespace Problem56

open scoped BigOperators Matrix

set_option maxHeartbeats 2000000

section Paths

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Split a nonempty finite coordinate tuple into its zeroth entry and tail. -/
def finConsEquiv (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun x := (x 0, fun k ↦ x k.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv x := by
    funext k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext k
      rfl

/-- Weight of a path with `n` internal vertices, hence `n+1` matrix edges. -/
def matrixPathWeight (A : Matrix α α ℝ) :
    (n : ℕ) → α → (Fin n → α) → α → ℝ
  | 0, i, _, j => A i j
  | n + 1, i, x, j =>
      A i (x 0) * matrixPathWeight A n (x 0) (fun k ↦ x k.succ) j

@[simp] theorem matrixPathWeight_zero (A : Matrix α α ℝ) (i j : α)
    (x : Fin 0 → α) :
    matrixPathWeight A 0 i x j = A i j := rfl

@[simp] theorem matrixPathWeight_succ (A : Matrix α α ℝ) (n : ℕ)
    (i j : α) (x : Fin (n + 1) → α) :
    matrixPathWeight A (n + 1) i x j =
      A i (x 0) * matrixPathWeight A n (x 0) (fun k ↦ x k.succ) j := rfl

theorem matrix_pow_succ_apply_eq_sum_pathWeight
    (A : Matrix α α ℝ) (n : ℕ) (i j : α) :
    (A ^ (n + 1)) i j =
      ∑ x : Fin n → α, matrixPathWeight A n i x j := by
  classical
  induction n generalizing i j with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply]
      simp_rw [ih]
      simp_rw [Finset.mul_sum]
      let e := finConsEquiv (α := α) n
      calc
        (∑ k, ∑ tail : Fin n → α,
            A i k * matrixPathWeight A n k tail j) =
            ∑ p : α × (Fin n → α),
              A i p.1 * matrixPathWeight A n p.1 p.2 j :=
          (Fintype.sum_prod_type (fun p : α × (Fin n → α) ↦
            A i p.1 * matrixPathWeight A n p.1 p.2 j)).symm
        _ = ∑ x : Fin (n + 1) → α,
            matrixPathWeight A (n + 1) i x j := by
          symm
          exact Fintype.sum_equiv e
            (fun x ↦ matrixPathWeight A (n + 1) i x j)
            (fun p ↦ A i p.1 * matrixPathWeight A n p.1 p.2 j)
            (fun x ↦ rfl)

/-- A positive-length cyclic matrix monomial, rooted at coordinate zero. -/
def rootedCyclicMatrixMonomial (A : Matrix α α ℝ) (n : ℕ)
    (x : Fin (n + 1) → α) : ℝ :=
  matrixPathWeight A n (x 0) (fun k ↦ x k.succ) (x 0)

theorem matrixPathWeight_eq_prod_adjacent
    (A : Matrix α α ℝ) (n : ℕ) (x : Fin (n + 2) → α) :
    matrixPathWeight A n (x 0) (fun k ↦ x k.succ.castSucc)
        (x (Fin.last (n + 1))) =
      ∏ f : Fin (n + 1), A (x f.castSucc) (x f.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [matrixPathWeight_succ, Fin.prod_univ_succ]
      congr 1
      simpa using ih (fun k : Fin (n + 2) ↦ x k.succ)

omit [Fintype α] [DecidableEq α] in
theorem fin_snoc_succ_eq_cyclicSucc (n : ℕ) (x : Fin (n + 1) → α)
    (f : Fin (n + 1)) :
    (Fin.snoc (α := fun _ : Fin (n + 2) ↦ α) x (x 0)) f.succ =
      x (cyclicSucc f) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) f
  · simp [cyclicSucc]
  · rw [show i.castSucc.succ = i.succ.castSucc by
      apply Fin.ext
      rfl]
    rw [Fin.snoc_castSucc]
    apply congrArg x
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc, cyclicSucc]
    rw [Nat.mod_eq_of_lt]
    omega

theorem rootedCyclicMatrixMonomial_eq_prod
    (A : Matrix α α ℝ) (n : ℕ) (x : Fin (n + 1) → α) :
    rootedCyclicMatrixMonomial A n x =
      ∏ f, A (x f) (x (cyclicSucc f)) := by
  let y : Fin (n + 2) → α :=
    Fin.snoc (α := fun _ : Fin (n + 2) ↦ α) x (x 0)
  calc
    rootedCyclicMatrixMonomial A n x =
        ∏ f : Fin (n + 1), A (y f.castSucc) (y f.succ) := by
      rw [rootedCyclicMatrixMonomial]
      simpa only [y, Fin.snoc_apply_zero, Fin.snoc_castSucc,
        Fin.snoc_last] using matrixPathWeight_eq_prod_adjacent A n y
    _ = ∏ f, A (x f) (x (cyclicSucc f)) := by
      apply Finset.prod_congr rfl
      intro f _
      rw [show y f.castSucc = x f by simp [y],
        show y f.succ = x (cyclicSucc f) by
          exact fin_snoc_succ_eq_cyclicSucc n x f]

theorem trace_pow_succ_eq_sum_rootedCyclicMatrixMonomial
    (A : Matrix α α ℝ) (n : ℕ) :
    Matrix.trace (A ^ (n + 1)) =
      ∑ x : Fin (n + 1) → α, rootedCyclicMatrixMonomial A n x := by
  classical
  rw [Matrix.trace]
  calc
    (∑ i, (A ^ (n + 1)) i i) =
        ∑ i, ∑ tail : Fin n → α, matrixPathWeight A n i tail i := by
      apply Finset.sum_congr rfl
      intro i _
      exact matrix_pow_succ_apply_eq_sum_pathWeight A n i i
    _ = ∑ x : Fin (n + 1) → α, rootedCyclicMatrixMonomial A n x := by
      let e := finConsEquiv (α := α) n
      calc
        (∑ i, ∑ tail : Fin n → α, matrixPathWeight A n i tail i) =
            ∑ p : α × (Fin n → α), matrixPathWeight A n p.1 p.2 p.1 :=
          (Fintype.sum_prod_type (fun p : α × (Fin n → α) ↦
            matrixPathWeight A n p.1 p.2 p.1)).symm
        _ = ∑ x : Fin (n + 1) → α,
            rootedCyclicMatrixMonomial A n x := by
          symm
          exact Fintype.sum_equiv e
            (rootedCyclicMatrixMonomial A n)
            (fun p ↦ matrixPathWeight A n p.1 p.2 p.1)
            (fun x ↦ rfl)

theorem matrix_mul_diagonal_apply (A : Matrix α α ℝ) (w : α → ℝ)
    (i j : α) :
    (A * Matrix.diagonal w) i j = A i j * w j := by
  exact Matrix.mul_diagonal w A i j

theorem matrixPathWeight_mul_diagonal
    (A : Matrix α α ℝ) (w : α → ℝ) (n : ℕ)
    (i j : α) (x : Fin n → α) :
    matrixPathWeight (A * Matrix.diagonal w) n i x j =
      matrixPathWeight A n i x j * ((∏ k, w (x k)) * w j) := by
  induction n generalizing i with
  | zero =>
      rw [matrixPathWeight_zero, matrixPathWeight_zero,
        matrix_mul_diagonal_apply]
      simp
  | succ n ih =>
      rw [matrixPathWeight_succ, matrixPathWeight_succ,
        matrix_mul_diagonal_apply, ih, Fin.prod_univ_succ]
      ring

theorem rootedCyclicMatrixMonomial_mul_diagonal
    (A : Matrix α α ℝ) (w : α → ℝ) (n : ℕ)
    (x : Fin (n + 1) → α) :
    rootedCyclicMatrixMonomial (A * Matrix.diagonal w) n x =
      rootedCyclicMatrixMonomial A n x * ∏ k, w (x k) := by
  rw [rootedCyclicMatrixMonomial, rootedCyclicMatrixMonomial,
    matrixPathWeight_mul_diagonal, Fin.prod_univ_succ]
  ring

def centeredBernoulliValue {β : Type*} (θ : ℝ) (e : SignLayer β)
    (i : β) : ℝ :=
  (if e i then 1 else 0) - θ

theorem centeredBernoulliProjection_eq_diagonal
    {β : Type*} [Fintype β] [DecidableEq β]
    (θ : ℝ) (e : SignLayer β) :
    bernoulliProjection e - θ • (1 : Matrix β β ℝ) =
      Matrix.diagonal (centeredBernoulliValue θ e) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [bernoulliProjection, centeredBernoulliValue]
  · simp [bernoulliProjection, centeredBernoulliValue, hij]

theorem trace_centeredSelector_product_pow_expansion
    (R : Matrix α α ℝ) (θ : ℝ) (e : SignLayer α) (n : ℕ) :
    Matrix.trace
        ((R * (bernoulliProjection e - θ • (1 : Matrix α α ℝ))) ^ (n + 1)) =
      ∑ x : Fin (n + 1) → α,
        (∏ f, R (x f) (x (cyclicSucc f))) *
          ∏ k, centeredBernoulliValue θ e (x k) := by
  rw [centeredBernoulliProjection_eq_diagonal]
  rw [trace_pow_succ_eq_sum_rootedCyclicMatrixMonomial]
  apply Finset.sum_congr rfl
  intro x _
  rw [rootedCyclicMatrixMonomial_mul_diagonal,
    rootedCyclicMatrixMonomial_eq_prod]

#print axioms matrix_pow_succ_apply_eq_sum_pathWeight
#print axioms trace_pow_succ_eq_sum_rootedCyclicMatrixMonomial
#print axioms rootedCyclicMatrixMonomial_eq_prod
#print axioms trace_centeredSelector_product_pow_expansion

end Paths

end Problem56
