import Problem56.TwoProjection
import Problem56.SpectralRoot
import Problem56.GraphOperatorL2

/-!
Kernel-checked spectral bookkeeping for the two-projection transfer theorem.
This module imports only definitions and already closed implementation modules;
it does not import the admitted statement layer.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

noncomputable def matrixBlock {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (block : ι → ι) (b : ι) :
    Matrix {i // block i = b} {i // block i = b} ℝ := by
  classical
  exact M.toBlock (fun i ↦ block i = b) (fun i ↦ block i = b)

@[simp] theorem matrixBlock_apply {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (block : ι → ι) (b : ι)
    (i j : {i // block i = b}) :
    matrixBlock M block b i j = M i.1 j.1 := by
  rfl

theorem matrixBlock_complement_to_block_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (block : ι → ι)
    (hM : ∀ i j, block i ≠ block j → M i j = 0) (b : ι) :
    M.toBlock (fun i ↦ ¬ block i = b) (fun i ↦ block i = b) = 0 := by
  classical
  ext i j
  simp only [Matrix.toBlock_apply, Matrix.zero_apply]
  apply hM
  intro hEq
  exact i.2 (hEq.trans j.2)

theorem matrixBlock_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (block : ι → ι)
    (hM : ∀ i j, block i ≠ block j → M i j = 0)
    (b : ι) (n : ℕ) :
    matrixBlock (M ^ n) block b = (matrixBlock M block b) ^ n := by
  classical
  induction n with
  | zero =>
      ext i j
      simp [matrixBlock, Matrix.one_apply, Subtype.ext_iff]
  | succ n ih =>
      rw [pow_succ, matrixBlock]
      rw [Matrix.toBlock_mul_eq_add (fun i ↦ block i = b)
        (fun i ↦ block i = b) (fun i ↦ block i = b)]
      rw [matrixBlock_complement_to_block_eq_zero M block hM b,
        Matrix.mul_zero, add_zero]
      change matrixBlock (M ^ n) block b * matrixBlock M block b = _
      rw [ih, pow_succ]

theorem trace_pow_eq_sum_matrixBlock
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (block : ι → ι)
    (hM : ∀ i j, block i ≠ block j → M i j = 0) (n : ℕ) :
    Matrix.trace (M ^ n) =
      ∑ b ∈ (Finset.univ : Finset ι).image block,
        Matrix.trace ((matrixBlock M block b) ^ n) := by
  classical
  rw [Matrix.trace]
  symm
  calc
    (∑ b ∈ (Finset.univ : Finset ι).image block,
        Matrix.trace ((matrixBlock M block b) ^ n)) =
        ∑ b ∈ (Finset.univ : Finset ι).image block,
          ∑ i ∈ (Finset.univ : Finset ι).filter (fun i ↦ block i = b),
            (M ^ n) i i := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← matrixBlock_pow M block hM b n]
      simp only [Matrix.trace, Matrix.diag_apply, matrixBlock_apply]
      rw [← Finset.sum_subtype_eq_sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · intro i _
        rfl
    _ = ∑ i ∈ (Finset.univ : Finset ι), (M ^ n) i i :=
      Finset.sum_fiberwise_of_maps_to
        (fun i _ ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        (fun i ↦ (M ^ n) i i)
    _ = ∑ i, (M ^ n) i i := rfl

theorem matrix_fin_two_sq_eq_trace_smul_sub_det_smul
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M ^ 2 = Matrix.trace M • M - Matrix.det M • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two, Matrix.one_apply] <;> ring

theorem matrix_fin_two_pow_recurrence
    (M : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    M ^ (n + 2) =
      Matrix.trace M • M ^ (n + 1) - Matrix.det M • M ^ n := by
  calc
    M ^ (n + 2) = M ^ n * M ^ 2 := by rw [pow_add]
    _ = M ^ n * (Matrix.trace M • M - Matrix.det M • 1) := by
      rw [matrix_fin_two_sq_eq_trace_smul_sub_det_smul]
    _ = Matrix.trace M • M ^ (n + 1) - Matrix.det M • M ^ n := by
      simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, pow_succ]

theorem matrix_fin_two_trace_pow_eq_root_power_sum
    (M : Matrix (Fin 2) (Fin 2) ℂ) (t d z₁ z₂ : ℂ)
    (htrace : Matrix.trace M = t) (hdet : Matrix.det M = d)
    (hsum : z₁ + z₂ = t) (hprod : z₁ * z₂ = d) (n : ℕ) :
    Matrix.trace (M ^ n) = z₁ ^ n + z₂ ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Matrix.trace_fin_two]
  | one => simpa [htrace] using hsum.symm
  | more n hn hn1 =>
      have hz₁sq : z₁ ^ 2 = t * z₁ - d := by
        rw [← hsum, ← hprod]
        ring
      have hz₂sq : z₂ ^ 2 = t * z₂ - d := by
        rw [← hsum, ← hprod]
        ring
      rw [matrix_fin_two_pow_recurrence, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_smul, htrace, hdet, hn, hn1]
      rw [show z₁ ^ (n + 2) = z₁ ^ n * z₁ ^ 2 by rw [pow_add],
        show z₂ ^ (n + 2) = z₂ ^ n * z₂ ^ 2 by rw [pow_add],
        hz₁sq, hz₂sq]
      ring

theorem complex_quadratic_roots (t d : ℝ) :
    ∃ z₁ z₂ : ℂ, z₁ + z₂ = t ∧ z₁ * z₂ = d := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self
    (((t : ℂ) ^ 2 - 4 * d))
  refine ⟨((t : ℂ) + w) / 2, ((t : ℂ) - w) / 2, ?_, ?_⟩
  · ring
  · calc
      ((t : ℂ) + w) / 2 * (((t : ℂ) - w) / 2) =
          ((t : ℂ) ^ 2 - w * w) / 4 := by ring
      _ = ((t : ℂ) ^ 2 - ((t : ℂ) ^ 2 - 4 * d)) / 4 := by rw [← hw]
      _ = d := by ring

noncomputable def twoProjectionPairTransferMatrix
    (lam δ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - δ) * (lam - θ),
      (1 - δ) * Real.sqrt (lam * (1 - lam));
    -δ * Real.sqrt (lam * (1 - lam)),
      -δ * (1 - lam - θ)]

theorem twoProjectionPairTransferMatrix_trace
    (lam δ θ : ℝ) :
    Matrix.trace (twoProjectionPairTransferMatrix lam δ θ) =
      lam - δ - θ + 2 * δ * θ := by
  rw [Matrix.trace_fin_two]
  simp [twoProjectionPairTransferMatrix]
  ring

theorem twoProjectionPairTransferMatrix_det
    (lam δ θ : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    Matrix.det (twoProjectionPairTransferMatrix lam δ θ) =
      δ * (1 - δ) * θ * (1 - θ) := by
  have hsquare : (Real.sqrt (lam * (1 - lam))) ^ 2 =
      lam * (1 - lam) := Real.sq_sqrt (mul_nonneg hlam.1 (sub_nonneg.mpr hlam.2))
  rw [Matrix.det_fin_two]
  simp [twoProjectionPairTransferMatrix]
  calc
    -((1 - δ) * (lam - θ) * (δ * (1 - lam - θ))) +
        (1 - δ) * Real.sqrt (lam * (1 - lam)) *
          (δ * Real.sqrt (lam * (1 - lam))) =
        δ * (1 - δ) *
          (-(lam - θ) * (1 - lam - θ) +
            (Real.sqrt (lam * (1 - lam))) ^ 2) := by ring
    _ = δ * (1 - δ) * θ * (1 - θ) := by rw [hsquare]; ring

theorem real_matrix_fin_two_trace_pow_eq_root_power_sum_re
    (M : Matrix (Fin 2) (Fin 2) ℝ) (t d : ℝ) (z₁ z₂ : ℂ)
    (htrace : Matrix.trace M = t) (hdet : Matrix.det M = d)
    (hsum : z₁ + z₂ = t) (hprod : z₁ * z₂ = d) (n : ℕ) :
    Matrix.trace (M ^ n) = (z₁ ^ n + z₂ ^ n).re := by
  let MC : Matrix (Fin 2) (Fin 2) ℂ := M.map (algebraMap ℝ ℂ)
  have htraceC : Matrix.trace MC = (t : ℂ) := by
    rw [Matrix.trace_fin_two] at htrace ⊢
    change (M 0 0 : ℂ) + (M 1 1 : ℂ) = (t : ℂ)
    exact_mod_cast htrace
  have hdetC : Matrix.det MC = (d : ℂ) := by
    rw [Matrix.det_fin_two] at hdet ⊢
    change (M 0 0 : ℂ) * (M 1 1 : ℂ) -
      (M 0 1 : ℂ) * (M 1 0 : ℂ) = (d : ℂ)
    exact_mod_cast hdet
  have hpowers := matrix_fin_two_trace_pow_eq_root_power_sum MC t d z₁ z₂
    htraceC hdetC hsum hprod n
  have hmap : MC ^ n = (M ^ n).map (algebraMap ℝ ℂ) := by
    simpa [MC] using (map_pow ((algebraMap ℝ ℂ).mapMatrix) M n).symm
  rw [hmap, Matrix.trace_fin_two] at hpowers
  have hre := congrArg Complex.re hpowers
  rw [Matrix.trace_fin_two]
  change (((M ^ n) 0 0 : ℂ) + ((M ^ n) 1 1 : ℂ)).re =
    (z₁ ^ n + z₂ ^ n).re at hre
  simpa using hre

theorem twoProjectionPairTransferMatrix_trace_even_power_lower
    (lam δ θ : ℝ) (p : ℕ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hδ : 0 ≤ δ ∧ δ ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ (2 * p)) ≥
      -2 * (δ * (1 - δ) * θ * (1 - θ)) ^ p := by
  let a2 := δ * (1 - δ) * θ * (1 - θ)
  let t := lam - δ - θ + 2 * δ * θ
  have ha2 : 0 ≤ a2 := by
    simp only [a2]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hδ.1 (sub_nonneg.mpr hδ.2)) hθ.1)
      (sub_nonneg.mpr hθ.2)
  obtain ⟨z₁, z₂, hsum, hprod⟩ := complex_quadratic_roots t a2
  have hprodSqrt : z₁ * z₂ = (Real.sqrt a2 : ℂ) ^ 2 := by
    rw [hprod]
    norm_cast
    exact (Real.sq_sqrt ha2).symm
  have hroot := quadratic_root_even_power_bound (Real.sqrt a2) t p
    (Real.sqrt_nonneg a2) z₁ z₂ ⟨hsum, hprodSqrt⟩
  have htrace := real_matrix_fin_two_trace_pow_eq_root_power_sum_re
    (twoProjectionPairTransferMatrix lam δ θ) t a2 z₁ z₂
    (twoProjectionPairTransferMatrix_trace lam δ θ)
    (twoProjectionPairTransferMatrix_det lam δ θ hlam) hsum hprod (2 * p)
  have hsqrtpow : (Real.sqrt a2) ^ (2 * p) = a2 ^ p := by
    rw [pow_mul, Real.sq_sqrt ha2]
  rw [← htrace, hsqrtpow] at hroot
  exact hroot

theorem even_power_eq_abs_power (x : ℝ) (p : ℕ) :
    x ^ (2 * p) = |x| ^ (2 * p) := by
  rw [← abs_pow, abs_of_nonneg]
  exact Even.pow_nonneg ⟨p, by omega⟩ x

theorem even_power_strict_mono_of_abs_gt
    (x q : ℝ) (p : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hx : |x| > q) : x ^ (2 * p) > q ^ (2 * p) := by
  rw [even_power_eq_abs_power]
  exact pow_lt_pow_left₀ hx hq (by omega)

theorem twoProjectionPairTransferMatrix_trace_even_power_gt_of_large_real_root
    (lam δ θ q z₁ z₂ : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hq : 0 ≤ q)
    (hsum : z₁ + z₂ = lam - δ - θ + 2 * δ * θ)
    (hprod : z₁ * z₂ = δ * (1 - δ) * θ * (1 - θ))
    (hlarge : max |z₁| |z₂| > q) :
    Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ (2 * p)) >
      q ^ (2 * p) := by
  have htrace := real_matrix_fin_two_trace_pow_eq_root_power_sum_re
    (twoProjectionPairTransferMatrix lam δ θ)
    (lam - δ - θ + 2 * δ * θ)
    (δ * (1 - δ) * θ * (1 - θ)) z₁ z₂
    (twoProjectionPairTransferMatrix_trace lam δ θ)
    (twoProjectionPairTransferMatrix_det lam δ θ hlam)
    (by exact_mod_cast hsum) (by exact_mod_cast hprod) (2 * p)
  have htraceReal :
      Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ (2 * p)) =
        z₁ ^ (2 * p) + z₂ ^ (2 * p) := by
    rw [htrace]
    norm_cast
  have hz₁nonneg : 0 ≤ z₁ ^ (2 * p) := Even.pow_nonneg ⟨p, by omega⟩ z₁
  have hz₂nonneg : 0 ≤ z₂ ^ (2 * p) := Even.pow_nonneg ⟨p, by omega⟩ z₂
  rw [htraceReal]
  rcases lt_max_iff.mp hlarge with hlarge | hlarge
  · have hpow := even_power_strict_mono_of_abs_gt z₁ q p hp hq hlarge
    nlinarith
  · have hpow := even_power_strict_mono_of_abs_gt z₂ q p hp hq hlarge
    nlinarith

noncomputable def centeredTwoProjectionProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E : Matrix ι ι ℝ) (δ θ : ℝ) : Matrix ι ι ℝ :=
  (P - δ • 1) * (E - θ • 1)

theorem orthogonalConjugate_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q A B : Matrix ι ι ℝ) (hQQt : Q * Q.transpose = 1) :
    orthogonalConjugate Q (A * B) =
      orthogonalConjugate Q A * orthogonalConjugate Q B := by
  simp only [orthogonalConjugate]
  calc
    Q.transpose * (A * B) * Q = Q.transpose * A * B * Q := by
      simp only [Matrix.mul_assoc]
    _ = Q.transpose * A * (Q * Q.transpose) * B * Q := by
      rw [hQQt]
      simp only [Matrix.mul_one]
    _ = (Q.transpose * A * Q) * (Q.transpose * B * Q) := by
      simp only [Matrix.mul_assoc]

theorem orthogonalConjugate_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQtQ : Q.transpose * Q = 1) :
    orthogonalConjugate Q 1 = 1 := by
  simpa [orthogonalConjugate]

theorem orthogonalConjugate_sub_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q A : Matrix ι ι ℝ) (c : ℝ) (hQtQ : Q.transpose * Q = 1) :
    orthogonalConjugate Q (A - c • 1) =
      orthogonalConjugate Q A - c • 1 := by
  simp only [orthogonalConjugate, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hQtQ]

theorem orthogonalConjugate_centeredTwoProjectionProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (δ θ : ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) :
    orthogonalConjugate Q (centeredTwoProjectionProduct P E δ θ) =
      centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ := by
  rw [centeredTwoProjectionProduct, orthogonalConjugate_mul Q _ _ hQQt,
    orthogonalConjugate_sub_smul_one Q P δ hQtQ,
    orthogonalConjugate_sub_smul_one Q E θ hQtQ]
  rfl

theorem orthogonalConjugate_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q A : Matrix ι ι ℝ) (hQtQ : Q.transpose * Q = 1)
    (hQQt : Q * Q.transpose = 1) (n : ℕ) :
    orthogonalConjugate Q (A ^ n) = (orthogonalConjugate Q A) ^ n := by
  induction n with
  | zero => simp [orthogonalConjugate_one Q hQtQ]
  | succ n ih =>
      rw [pow_succ, orthogonalConjugate_mul Q _ _ hQQt, ih, pow_succ]

theorem trace_orthogonalConjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q A : Matrix ι ι ℝ) (hQQt : Q * Q.transpose = 1) :
    Matrix.trace (orthogonalConjugate Q A) = Matrix.trace A := by
  rw [orthogonalConjugate, Matrix.trace_mul_cycle]
  rw [hQQt]
  simp

theorem trace_centeredTwoProjectionProduct_pow_eq_conjugated
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (δ θ : ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) (n : ℕ) :
    Matrix.trace ((centeredTwoProjectionProduct P E δ θ) ^ n) =
      Matrix.trace ((centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ) ^ n) := by
  rw [← orthogonalConjugate_centeredTwoProjectionProduct P E Q δ θ hQtQ hQQt]
  rw [← orthogonalConjugate_pow Q _ hQtQ hQQt]
  exact (trace_orthogonalConjugate Q _ hQQt).symm

theorem conjugated_centeredTwoProjectionProduct_off_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (δ θ : ℝ) (i j : ι) (hij : block i ≠ block j) :
    centeredTwoProjectionProduct (orthogonalConjugate Q P)
      (orthogonalConjugate Q E) δ θ i j = 0 := by
  rcases hD with ⟨_, _, _, hoff, _, _⟩
  let P' := orthogonalConjugate Q P
  let E' := orthogonalConjugate Q E
  have hP (u v : ι) (huv : block u ≠ block v) :
      (P' - δ • 1) u v = 0 := by
    have hne : u ≠ v := fun h ↦ huv (congrArg block h)
    simp [P', hoff u v huv |>.1, hne]
  have hE (u v : ι) (huv : block u ≠ block v) :
      (E' - θ • 1) u v = 0 := by
    have hne : u ≠ v := fun h ↦ huv (congrArg block h)
    simp [E', hoff u v huv |>.2, hne]
  simp only [centeredTwoProjectionProduct, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : block i = block k
  · rw [hE k j (fun hkj ↦ hij (hik.trans hkj)), mul_zero]
  · rw [hP i k hik, zero_mul]

theorem blockSubtype_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (block : ι → ι) (b : ι) :
    Fintype.card {i // block i = b} =
      ((Finset.univ : Finset ι).filter fun i ↦ block i = b).card := by
  classical
  exact Fintype.card_ofFinset
    ((Finset.univ : Finset ι).filter fun i ↦ block i = b) (by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro h <;> exact h)

noncomputable def finTwoEquivOfPair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (block : ι → ι) (b : ι)
    (hi : block i = b) (hj : block j = b)
    (hcard : Fintype.card {k // block k = b} = 2) :
    Fin 2 ≃ {k // block k = b} := by
  let f : Fin 2 → {k // block k = b} := fun k ↦
    if k = 0 then ⟨i, hi⟩ else ⟨j, hj⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro u v huv
    fin_cases u <;> fin_cases v
    · rfl
    · simp [f] at huv
      exact (hij huv).elim
    · simp [f] at huv
      exact (hij huv.symm).elim
    · rfl
  · simpa using hcard.symm

@[simp] theorem finTwoEquivOfPair_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (block : ι → ι) (b : ι)
    (hi : block i = b) (hj : block j = b)
    (hcard : Fintype.card {k // block k = b} = 2) :
    finTwoEquivOfPair i j hij block b hi hj hcard 0 = ⟨i, hi⟩ := by
  simp [finTwoEquivOfPair]

@[simp] theorem finTwoEquivOfPair_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (block : ι → ι) (b : ι)
    (hi : block i = b) (hj : block j = b)
    (hcard : Fintype.card {k // block k = b} = 2) :
    finTwoEquivOfPair i j hij block b hi hj hcard 1 = ⟨j, hj⟩ := by
  simp [finTwoEquivOfPair]

theorem trace_reindexAlgEquiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (M : Matrix ι ι ℝ) :
    Matrix.trace ((Matrix.reindexAlgEquiv ℝ ℝ e) M) = Matrix.trace M := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i ↦ M i i)

theorem trace_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (M : Matrix ι ι ℝ) :
    Matrix.trace (M.submatrix e e) = Matrix.trace M := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i ↦ M i i)

theorem matrixBlock_centeredTwoProjectionProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (δ θ : ℝ) (b : ι) :
    matrixBlock
        (centeredTwoProjectionProduct (orthogonalConjugate Q P)
          (orthogonalConjugate Q E) δ θ) block b =
      matrixBlock (orthogonalConjugate Q P - δ • 1) block b *
        matrixBlock (orthogonalConjugate Q E - θ • 1) block b := by
  classical
  rcases hD with ⟨_, _, _, hoff, _, _⟩
  have hP (i j : ι) (hij : block i ≠ block j) :
      (orthogonalConjugate Q P - δ • 1) i j = 0 := by
    have hne : i ≠ j := fun h ↦ hij (congrArg block h)
    simp [hoff i j hij |>.1, hne]
  have hE (i j : ι) (hij : block i ≠ block j) :
      (orthogonalConjugate Q E - θ • 1) i j = 0 := by
    have hne : i ≠ j := fun h ↦ hij (congrArg block h)
    simp [hoff i j hij |>.2, hne]
  rw [centeredTwoProjectionProduct, matrixBlock]
  rw [Matrix.toBlock_mul_eq_add (fun i ↦ block i = b)
    (fun i ↦ block i = b) (fun i ↦ block i = b)]
  rw [matrixBlock_complement_to_block_eq_zero _ block hE b,
    Matrix.mul_zero, add_zero]
  rfl

theorem twoProjection_two_block_trace_even_power_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (δ θ : ℝ) (p : ℕ)
    (hδ : 0 ≤ δ ∧ δ ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (i : ι)
    (hi : ((Finset.univ : Finset ι).filter fun j ↦
      block j = block i).card = 2) :
    Matrix.trace ((matrixBlock
      (centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ) block (block i)) ^ (2 * p)) ≥
      -2 * (δ * (1 - δ) * θ * (1 - θ)) ^ p := by
  classical
  obtain ⟨j, hji, hjblock, lam, hlam0, hlam1, hPij, hPji,
    hEij, hEji, hdiag⟩ := hD.2.2.2.2.2 i hi
  have hcard : Fintype.card {k // block k = block i} = 2 := by
    rw [blockSubtype_card]
    exact hi
  let B := centeredTwoProjectionProduct (orthogonalConjugate Q P)
    (orthogonalConjugate Q E) δ θ
  rcases hdiag with hdiag | hdiag
  · let e := finTwoEquivOfPair i j (Ne.symm hji) block (block i) rfl
      hjblock hcard
    have he0 : e 0 = ⟨i, rfl⟩ := by
      exact finTwoEquivOfPair_zero i j (Ne.symm hji) block (block i) rfl
        hjblock hcard
    have he1 : e 1 = ⟨j, hjblock⟩ := by
      exact finTwoEquivOfPair_one i j (Ne.symm hji) block (block i) rfl
        hjblock hcard
    have he01 : (e 0).1 ≠ (e 1).1 := by
      intro h
      have heq : e 0 = e 1 := Subtype.ext h
      exact Fin.zero_ne_one (e.injective heq)
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      (matrixBlock B block (block i)).submatrix e e
    have hM : M = twoProjectionPairTransferMatrix lam δ θ := by
      dsimp only [M]
      rw [show matrixBlock B block (block i) =
          matrixBlock (orthogonalConjugate Q P - δ • 1) block (block i) *
            matrixBlock (orthogonalConjugate Q E - θ • 1) block (block i) by
        exact matrixBlock_centeredTwoProjectionProduct P E Q block hD δ θ (block i)]
      rw [← Matrix.submatrix_mul_equiv _ _ e e e]
      ext u v
      fin_cases u <;> fin_cases v <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.submatrix_apply, matrixBlock_apply, Matrix.sub_apply,
          Matrix.smul_apply] <;>
        simp only [e, finTwoEquivOfPair_zero, finTwoEquivOfPair_one] <;>
        simp [Matrix.one_apply, he01, Ne.symm he01, hji, hPij, hPji, hEij, hEji, hdiag,
          twoProjectionPairTransferMatrix] <;> ring
    have hpow (n : ℕ) :
        ((matrixBlock B block (block i)) ^ n).submatrix e e = M ^ n := by
      induction n with
      | zero => simp [M, Matrix.submatrix_one_equiv]
      | succ n hn =>
          rw [pow_succ, pow_succ,
            ← Matrix.submatrix_mul_equiv _ _ e e e, hn]
    calc
      Matrix.trace ((matrixBlock B block (block i)) ^ (2 * p)) =
          Matrix.trace (M ^ (2 * p)) := by
            rw [← hpow, trace_submatrix_equiv]
      _ = Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ (2 * p)) := by
        rw [hM]
      _ ≥ -2 * (δ * (1 - δ) * θ * (1 - θ)) ^ p :=
        twoProjectionPairTransferMatrix_trace_even_power_lower lam δ θ p
          ⟨hlam0.le, hlam1.le⟩ hδ hθ

  · let e := finTwoEquivOfPair j i hji block (block i) hjblock rfl hcard
    have he0 : e 0 = ⟨j, hjblock⟩ := by
      exact finTwoEquivOfPair_zero j i hji block (block i) hjblock rfl hcard
    have he1 : e 1 = ⟨i, rfl⟩ := by
      exact finTwoEquivOfPair_one j i hji block (block i) hjblock rfl hcard
    have he01 : (e 0).1 ≠ (e 1).1 := by
      intro h
      have heq : e 0 = e 1 := Subtype.ext h
      exact Fin.zero_ne_one (e.injective heq)
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      (matrixBlock B block (block i)).submatrix e e
    have hM : M = twoProjectionPairTransferMatrix lam δ θ := by
      dsimp only [M]
      rw [show matrixBlock B block (block i) =
          matrixBlock (orthogonalConjugate Q P - δ • 1) block (block i) *
            matrixBlock (orthogonalConjugate Q E - θ • 1) block (block i) by
        exact matrixBlock_centeredTwoProjectionProduct P E Q block hD δ θ (block i)]
      rw [← Matrix.submatrix_mul_equiv _ _ e e e]
      ext u v
      fin_cases u <;> fin_cases v <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.submatrix_apply, matrixBlock_apply, Matrix.sub_apply,
          Matrix.smul_apply] <;>
        simp only [e, finTwoEquivOfPair_zero, finTwoEquivOfPair_one] <;>
        simp [Matrix.one_apply, he01, Ne.symm he01, hji, hPij, hPji, hEij, hEji, hdiag,
          twoProjectionPairTransferMatrix] <;> ring
    have hpow (n : ℕ) :
        ((matrixBlock B block (block i)) ^ n).submatrix e e = M ^ n := by
      induction n with
      | zero => simp [M, Matrix.submatrix_one_equiv]
      | succ n hn =>
          rw [pow_succ, pow_succ,
            ← Matrix.submatrix_mul_equiv _ _ e e e, hn]
    calc
      Matrix.trace ((matrixBlock B block (block i)) ^ (2 * p)) =
          Matrix.trace (M ^ (2 * p)) := by
            rw [← hpow, trace_submatrix_equiv]
      _ = Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ (2 * p)) := by
        rw [hM]
      _ ≥ -2 * (δ * (1 - δ) * θ * (1 - θ)) ^ p :=
        twoProjectionPairTransferMatrix_trace_even_power_lower lam δ θ p
          ⟨hlam0.le, hlam1.le⟩ hδ hθ

theorem twoProjection_two_block_trace_eq_canonical_of_primary_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (δ θ lam : ℝ) (n : ℕ) (i : ι)
    (hi : ((Finset.univ : Finset ι).filter fun j ↦
      block j = block i).card = 2)
    (hPii : orthogonalConjugate Q P i i = 1)
    (hEii : orthogonalConjugate Q E i i = lam) :
    Matrix.trace ((matrixBlock
      (centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ) block (block i)) ^ n) =
      Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ n) := by
  classical
  obtain ⟨j, hji, hjblock, mu, hmu0, hmu1, hPij, hPji,
    hEij, hEji, hdiag⟩ := hD.2.2.2.2.2 i hi
  rcases hdiag with hdiag | hdiag
  · have hmueq : mu = lam := by
      rw [← hEii, hdiag.2.2.1]
    subst mu
    have hcard : Fintype.card {k // block k = block i} = 2 := by
      rw [blockSubtype_card]
      exact hi
    let B := centeredTwoProjectionProduct (orthogonalConjugate Q P)
      (orthogonalConjugate Q E) δ θ
    let e := finTwoEquivOfPair i j (Ne.symm hji) block (block i) rfl
      hjblock hcard
    have he01 : (e 0).1 ≠ (e 1).1 := by
      intro h
      have heq : e 0 = e 1 := Subtype.ext h
      exact Fin.zero_ne_one (e.injective heq)
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      (matrixBlock B block (block i)).submatrix e e
    have hM : M = twoProjectionPairTransferMatrix lam δ θ := by
      dsimp only [M]
      rw [show matrixBlock B block (block i) =
          matrixBlock (orthogonalConjugate Q P - δ • 1) block (block i) *
            matrixBlock (orthogonalConjugate Q E - θ • 1) block (block i) by
        exact matrixBlock_centeredTwoProjectionProduct P E Q block hD δ θ (block i)]
      rw [← Matrix.submatrix_mul_equiv _ _ e e e]
      ext u v
      fin_cases u <;> fin_cases v <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.submatrix_apply, matrixBlock_apply, Matrix.sub_apply,
          Matrix.smul_apply] <;>
        simp only [e, finTwoEquivOfPair_zero, finTwoEquivOfPair_one] <;>
        simp [Matrix.one_apply, he01, Ne.symm he01, hPij, hPji, hEij, hEji,
          hdiag, twoProjectionPairTransferMatrix] <;> ring
    have hpow : ((matrixBlock B block (block i)) ^ n).submatrix e e = M ^ n := by
      induction n with
      | zero => simp [M, Matrix.submatrix_one_equiv]
      | succ n hn =>
          rw [pow_succ, pow_succ,
            ← Matrix.submatrix_mul_equiv _ _ e e e, hn]
    calc
      Matrix.trace ((matrixBlock
          (centeredTwoProjectionProduct (orthogonalConjugate Q P)
            (orthogonalConjugate Q E) δ θ) block (block i)) ^ n) =
          Matrix.trace (M ^ n) := by
            change Matrix.trace ((matrixBlock B block (block i)) ^ n) = _
            rw [← hpow, trace_submatrix_equiv]
      _ = Matrix.trace ((twoProjectionPairTransferMatrix lam δ θ) ^ n) := by
        rw [hM]
  · have hzero : orthogonalConjugate Q P i i = 0 := hdiag.2.1
    linarith [hPii, hzero]

theorem matrix_trace_even_power_nonneg_of_card_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (p : ℕ) (hcard : Fintype.card ι = 1) :
    0 ≤ Matrix.trace (M ^ (2 * p)) := by
  classical
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  letI : Unique ι := ⟨⟨i⟩, hi⟩
  have hpow (n : ℕ) : (M ^ n) default default = (M default default) ^ n := by
    induction n with
    | zero => simp
    | succ n hn =>
        rw [pow_succ, pow_succ, Matrix.mul_apply, Fintype.sum_unique, hn]
  rw [Matrix.trace]
  rw [Fintype.sum_unique]
  simp only [Matrix.diag_apply, hpow]
  rw [show 2 * p = p + p by omega, pow_add]
  exact mul_self_nonneg ((M default default) ^ p)

theorem matrix_trace_pow_eq_diagonal_pow_of_card_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (n : ℕ) (i : ι) (hcard : Fintype.card ι = 1) :
    Matrix.trace (M ^ n) = (M i i) ^ n := by
  classical
  obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.mp hcard
  letI : Unique ι := ⟨⟨j⟩, hj⟩
  have hpow (k : ℕ) : (M ^ k) default default = (M default default) ^ k := by
    induction k with
    | zero => simp
    | succ k hk =>
        rw [pow_succ, pow_succ, Matrix.mul_apply, Fintype.sum_unique, hk]
  rw [Matrix.trace, Fintype.sum_unique]
  simp only [Matrix.diag_apply, hpow]
  have hi : i = default := Subsingleton.elim _ _
  rw [hi]

theorem twoProjection_singleton_block_trace_even_power_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (δ θ : ℝ) (p : ℕ) (i : ι)
    (hi : ((Finset.univ : Finset ι).filter fun j ↦
      block j = block i).card = 1) :
    0 ≤ Matrix.trace ((matrixBlock
      (centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ) block (block i)) ^ (2 * p)) := by
  apply matrix_trace_even_power_nonneg_of_card_eq_one
  rw [blockSubtype_card]
  exact hi

theorem twoProjection_singleton_block_trace_pow_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (δ θ pval eval : ℝ) (n : ℕ) (i : ι)
    (hi : ((Finset.univ : Finset ι).filter fun j ↦
      block j = block i).card = 1)
    (hPii : orthogonalConjugate Q P i i = pval)
    (hEii : orthogonalConjugate Q E i i = eval) :
    Matrix.trace ((matrixBlock
      (centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ) block (block i)) ^ n) =
      ((pval - δ) * (eval - θ)) ^ n := by
  classical
  let B := centeredTwoProjectionProduct (orthogonalConjugate Q P)
    (orthogonalConjugate Q E) δ θ
  have hcard : Fintype.card {j // block j = block i} = 1 := by
    rw [blockSubtype_card]
    exact hi
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hcard
  letI : Unique {j // block j = block i} := ⟨⟨u⟩, hu⟩
  let ii : {j // block j = block i} := ⟨i, rfl⟩
  calc
    Matrix.trace ((matrixBlock
        (centeredTwoProjectionProduct (orthogonalConjugate Q P)
          (orthogonalConjugate Q E) δ θ) block (block i)) ^ n) =
        (matrixBlock B block (block i) ii ii) ^ n := by
          exact matrix_trace_pow_eq_diagonal_pow_of_card_eq_one
            (matrixBlock B block (block i)) n ii hcard
    _ = ((pval - δ) * (eval - θ)) ^ n := by
      rw [show matrixBlock B block (block i) =
          matrixBlock (orthogonalConjugate Q P - δ • 1) block (block i) *
            matrixBlock (orthogonalConjugate Q E - θ • 1) block (block i) by
        exact matrixBlock_centeredTwoProjectionProduct P E Q block hD δ θ (block i)]
      simp only [Matrix.mul_apply]
      rw [Fintype.sum_unique]
      have hdefault :
          (default : {j // block j = block i}) = ii := Subsingleton.elim _ _
      rw [hdefault]
      simp [ii, matrixBlock_apply, hPii, hEii, Matrix.one_apply]

theorem two_block_index_card_eq_twice_image_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] (block : ι → ι) :
    ((Finset.univ : Finset ι).filter (fun i ↦
        ((Finset.univ : Finset ι).filter fun j ↦ block j = block i).card = 2)).card =
      2 * (((Finset.univ : Finset ι).image block).filter (fun b ↦
        ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)).card := by
  classical
  let fiberCard : ι → ℕ := fun b ↦
    ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card
  have heq (i : ι) (hi : i ∈ (Finset.univ : Finset ι)) :
      (if fiberCard (block i) = 2 then 2 else 0) =
        ∑ j ∈ (Finset.univ : Finset ι) with block j = block i,
          if fiberCard (block j) = 2 then 1 else 0 := by
    by_cases hc : fiberCard (block i) = 2
    · simp only [hc, if_true]
      calc
        2 = ((Finset.univ : Finset ι).filter fun j ↦ block j = block i).card :=
          hc.symm
        _ = ∑ j ∈ (Finset.univ : Finset ι) with block j = block i, 1 := by
          simp
        _ = ∑ j ∈ (Finset.univ : Finset ι) with block j = block i,
            if fiberCard (block j) = 2 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : block j = block i := by simpa using hj
          simp [fiberCard, hji, hc]
    · simp only [hc, if_false]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hji : block j = block i := by simpa using hj
      simp [fiberCard, hji, hc]
  have hsum := Finset.sum_image' (s := (Finset.univ : Finset ι))
    (g := block)
    (f := fun b ↦ if fiberCard b = 2 then (2 : ℕ) else 0)
    (h := fun i ↦ if fiberCard (block i) = 2 then (1 : ℕ) else 0) heq
  have hleft :
      (∑ b ∈ (Finset.univ : Finset ι).image block,
        if fiberCard b = 2 then (2 : ℕ) else 0) =
        2 * (((Finset.univ : Finset ι).image block).filter
          (fun b ↦ fiberCard b = 2)).card := by
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : fiberCard b = 2 <;> simp [h]
  have hright :
      (∑ i ∈ (Finset.univ : Finset ι),
        if fiberCard (block i) = 2 then (1 : ℕ) else 0) =
        ((Finset.univ : Finset ι).filter
          (fun i ↦ fiberCard (block i) = 2)).card := by
    rw [Finset.card_filter]
  calc
    ((Finset.univ : Finset ι).filter (fun i ↦
        ((Finset.univ : Finset ι).filter fun j ↦ block j = block i).card = 2)).card =
        ∑ i ∈ (Finset.univ : Finset ι),
          if fiberCard (block i) = 2 then (1 : ℕ) else 0 := by
            rw [hright]
    _ = ∑ b ∈ (Finset.univ : Finset ι).image block,
          if fiberCard b = 2 then (2 : ℕ) else 0 := hsum.symm
    _ = 2 * (((Finset.univ : Finset ι).image block).filter (fun b ↦
        ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)).card := by
          rw [hleft]

theorem twoProjection_trace_even_power_lower_of_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (hcount : ((Finset.univ : Finset ι).filter (fun i ↦
      ((Finset.univ : Finset ι).filter fun j ↦
        block j = block i).card = 2)).card / 2 ≤ r)
    (δ θ : ℝ) (p : ℕ)
    (hδ : 0 ≤ δ ∧ δ ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    Matrix.trace ((centeredTwoProjectionProduct P E δ θ) ^ (2 * p)) ≥
      -2 * r * (δ * (1 - δ) * θ * (1 - θ)) ^ p := by
  classical
  let B := centeredTwoProjectionProduct (orthogonalConjugate Q P)
    (orthogonalConjugate Q E) δ θ
  let a2 := δ * (1 - δ) * θ * (1 - θ)
  let imageBlocks := (Finset.univ : Finset ι).image block
  let twoBlocks := imageBlocks.filter (fun b ↦
    ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)
  have hcardEq := two_block_index_card_eq_twice_image_card block
  have htwoBlocks : twoBlocks.card ≤ r := by
    change (((Finset.univ : Finset ι).image block).filter (fun b ↦
      ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)).card ≤ r
    rw [hcardEq] at hcount
    simpa using hcount
  have ha2 : 0 ≤ a2 := by
    dsimp only [a2]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hδ.1 (sub_nonneg.mpr hδ.2)) hθ.1)
      (sub_nonneg.mpr hθ.2)
  have hblock (b : ι) (hb : b ∈ imageBlocks) :
      (if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
        then -2 * a2 ^ p else 0) ≤
        Matrix.trace ((matrixBlock B block b) ^ (2 * p)) := by
    obtain ⟨i, hi, hib⟩ := Finset.mem_image.mp hb
    have hiuniv : i ∈ (Finset.univ : Finset ι) := by simpa using hi
    subst b
    by_cases htwo : ((Finset.univ : Finset ι).filter fun j ↦
        block j = block i).card = 2
    · simp only [htwo, if_true]
      exact twoProjection_two_block_trace_even_power_lower P E Q block hD δ θ p
        hδ hθ i htwo
    · simp only [htwo, if_false]
      have hmem : i ∈ ((Finset.univ : Finset ι).filter fun j ↦
          block j = block i) := by simp
      have hpos : 0 < ((Finset.univ : Finset ι).filter fun j ↦
          block j = block i).card := Finset.card_pos.mpr ⟨i, hmem⟩
      have hle := hD.2.2.1 i
      have hone : ((Finset.univ : Finset ι).filter fun j ↦
          block j = block i).card = 1 := by omega
      exact twoProjection_singleton_block_trace_even_power_nonneg
        P E Q block δ θ p i hone
  have hsumLower :
      (∑ b ∈ imageBlocks,
        if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
          then -2 * a2 ^ p else 0) ≤
        ∑ b ∈ imageBlocks, Matrix.trace ((matrixBlock B block b) ^ (2 * p)) := by
    exact Finset.sum_le_sum hblock
  have hindicator :
      (∑ b ∈ imageBlocks,
        if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
          then -2 * a2 ^ p else 0) =
        (twoBlocks.card : ℝ) * (-2 * a2 ^ p) := by
    calc
      (∑ b ∈ imageBlocks,
        if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
          then -2 * a2 ^ p else 0) =
          ∑ b ∈ twoBlocks, (-2 * a2 ^ p) := by
            symm
            exact Finset.sum_filter _ _
      _ = (twoBlocks.card : ℝ) * (-2 * a2 ^ p) := by
        simp [nsmul_eq_mul]
  have hcardReal : (twoBlocks.card : ℝ) ≤ r := by exact_mod_cast htwoBlocks
  have hpowNonneg : 0 ≤ a2 ^ p := pow_nonneg ha2 p
  have hnumeric :
      -2 * r * a2 ^ p ≤ (twoBlocks.card : ℝ) * (-2 * a2 ^ p) := by
    nlinarith
  have htraceB :
      Matrix.trace (B ^ (2 * p)) ≥ -2 * r * a2 ^ p := by
    rw [trace_pow_eq_sum_matrixBlock B block
      (conjugated_centeredTwoProjectionProduct_off_block P E Q block hD δ θ)
      (2 * p)]
    change -2 * r * a2 ^ p ≤
      ∑ b ∈ imageBlocks, Matrix.trace ((matrixBlock B block b) ^ (2 * p))
    exact hnumeric.trans (hindicator ▸ hsumLower)
  rw [trace_centeredTwoProjectionProduct_pow_eq_conjugated P E Q δ θ
    hD.1 hD.2.1 (2 * p)]
  simpa [B, a2] using htraceB

theorem twoProjection_trace_plus_compensation_gt_of_bad_block
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (P E Q : Matrix ι ι ℝ) (block : ι → ι)
    (hD : IsTwoProjectionBlockDecomposition P E Q block)
    (hcount : ((Finset.univ : Finset ι).filter (fun i ↦
      ((Finset.univ : Finset ι).filter fun j ↦
        block j = block i).card = 2)).card / 2 ≤ r)
    (δ θ q : ℝ) (p : ℕ)
    (hδ : 0 ≤ δ ∧ δ ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (b₀ : ι) (hb₀ : b₀ ∈ (Finset.univ : Finset ι).image block)
    (hbad : Matrix.trace ((matrixBlock
      (centeredTwoProjectionProduct (orthogonalConjugate Q P)
        (orthogonalConjugate Q E) δ θ) block b₀) ^ (2 * p)) >
      q ^ (2 * p)) :
    Matrix.trace ((centeredTwoProjectionProduct P E δ θ) ^ (2 * p)) +
        2 * r * (δ * (1 - δ) * θ * (1 - θ)) ^ p > q ^ (2 * p) := by
  classical
  let B := centeredTwoProjectionProduct (orthogonalConjugate Q P)
    (orthogonalConjugate Q E) δ θ
  let a2 := δ * (1 - δ) * θ * (1 - θ)
  let imageBlocks := (Finset.univ : Finset ι).image block
  let twoBlocks := imageBlocks.filter (fun b ↦
    ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)
  let remainingTwoBlocks := (imageBlocks.erase b₀).filter (fun b ↦
    ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)
  have hcardEq := two_block_index_card_eq_twice_image_card block
  have htwoBlocks : twoBlocks.card ≤ r := by
    change (((Finset.univ : Finset ι).image block).filter (fun b ↦
      ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2)).card ≤ r
    rw [hcardEq] at hcount
    simpa using hcount
  have hremainingSubset : remainingTwoBlocks ⊆ twoBlocks := by
    intro b hb
    simp only [remainingTwoBlocks, twoBlocks, Finset.mem_filter,
      Finset.mem_erase] at hb ⊢
    exact ⟨hb.1.2, hb.2⟩
  have hremaining : remainingTwoBlocks.card ≤ r :=
    (Finset.card_le_card hremainingSubset).trans htwoBlocks
  have ha2 : 0 ≤ a2 := by
    dsimp only [a2]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hδ.1 (sub_nonneg.mpr hδ.2)) hθ.1)
      (sub_nonneg.mpr hθ.2)
  have hblock (b : ι) (hb : b ∈ imageBlocks.erase b₀) :
      (if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
        then -2 * a2 ^ p else 0) ≤
        Matrix.trace ((matrixBlock B block b) ^ (2 * p)) := by
    have hbImage : b ∈ imageBlocks := (Finset.mem_erase.mp hb).2
    obtain ⟨i, hi, hib⟩ := Finset.mem_image.mp hbImage
    have hiuniv : i ∈ (Finset.univ : Finset ι) := by simpa using hi
    subst b
    by_cases htwo : ((Finset.univ : Finset ι).filter fun j ↦
        block j = block i).card = 2
    · simp only [htwo, if_true]
      exact twoProjection_two_block_trace_even_power_lower P E Q block hD δ θ p
        hδ hθ i htwo
    · simp only [htwo, if_false]
      have hmem : i ∈ ((Finset.univ : Finset ι).filter fun j ↦
          block j = block i) := by simp
      have hpos : 0 < ((Finset.univ : Finset ι).filter fun j ↦
          block j = block i).card := Finset.card_pos.mpr ⟨i, hmem⟩
      have hle := hD.2.2.1 i
      have hone : ((Finset.univ : Finset ι).filter fun j ↦
          block j = block i).card = 1 := by omega
      exact twoProjection_singleton_block_trace_even_power_nonneg
        P E Q block δ θ p i hone
  have hsumLower :
      (∑ b ∈ imageBlocks.erase b₀,
        if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
          then -2 * a2 ^ p else 0) ≤
        ∑ b ∈ imageBlocks.erase b₀,
          Matrix.trace ((matrixBlock B block b) ^ (2 * p)) := by
    exact Finset.sum_le_sum hblock
  have hindicator :
      (∑ b ∈ imageBlocks.erase b₀,
        if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
          then -2 * a2 ^ p else 0) =
        (remainingTwoBlocks.card : ℝ) * (-2 * a2 ^ p) := by
    calc
      (∑ b ∈ imageBlocks.erase b₀,
        if ((Finset.univ : Finset ι).filter fun j ↦ block j = b).card = 2
          then -2 * a2 ^ p else 0) =
          ∑ b ∈ remainingTwoBlocks, (-2 * a2 ^ p) := by
            symm
            exact Finset.sum_filter _ _
      _ = (remainingTwoBlocks.card : ℝ) * (-2 * a2 ^ p) := by
        simp [nsmul_eq_mul]
  have hcardReal : (remainingTwoBlocks.card : ℝ) ≤ r := by
    exact_mod_cast hremaining
  have hpowNonneg : 0 ≤ a2 ^ p := pow_nonneg ha2 p
  have hremainingLower :
      -2 * r * a2 ^ p ≤
        ∑ b ∈ imageBlocks.erase b₀,
          Matrix.trace ((matrixBlock B block b) ^ (2 * p)) := by
    have hnumeric :
        -2 * r * a2 ^ p ≤
          (remainingTwoBlocks.card : ℝ) * (-2 * a2 ^ p) := by
      nlinarith
    exact hnumeric.trans (hindicator ▸ hsumLower)
  have hb₀Image : b₀ ∈ imageBlocks := by simpa [imageBlocks] using hb₀
  have htraceB : Matrix.trace (B ^ (2 * p)) + 2 * r * a2 ^ p >
      q ^ (2 * p) := by
    rw [trace_pow_eq_sum_matrixBlock B block
      (conjugated_centeredTwoProjectionProduct_off_block P E Q block hD δ θ)
      (2 * p)]
    have hsplit :
        (∑ b ∈ imageBlocks, Matrix.trace ((matrixBlock B block b) ^ (2 * p))) =
          Matrix.trace ((matrixBlock B block b₀) ^ (2 * p)) +
            ∑ b ∈ imageBlocks.erase b₀,
              Matrix.trace ((matrixBlock B block b) ^ (2 * p)) := by
      rw [← Finset.sum_erase_add imageBlocks
        (fun b ↦ Matrix.trace ((matrixBlock B block b) ^ (2 * p))) hb₀Image]
      ring
    rw [hsplit]
    change q ^ (2 * p) <
      Matrix.trace ((matrixBlock B block b₀) ^ (2 * p)) +
        (∑ b ∈ imageBlocks.erase b₀,
          Matrix.trace ((matrixBlock B block b) ^ (2 * p))) +
        2 * r * a2 ^ p
    nlinarith
  rw [trace_centeredTwoProjectionProduct_pow_eq_conjugated P E Q δ θ
    hD.1 hD.2.1 (2 * p)]
  simpa [B, a2] using htraceB

theorem exists_compressionEigenvalue_deviation_of_operatorNorm_gt
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η)
    (hbad : euclideanOperatorNorm
      (θ⁻¹ • (X.transpose * E * X) - 1) > η) :
    ∃ i : Fin r, |compressionEigenvalue X E hE i - θ| > θ * η := by
  classical
  let C := X.transpose * E * X
  let U := compressionEigenbasisMatrix X E hE
  let lam := compressionEigenvalue X E hE
  let M : Matrix (Fin r) (Fin r) ℝ := θ⁻¹ • C - 1
  let d : Fin r → ℝ := fun i ↦ θ⁻¹ * lam i - 1
  have hUU : U.transpose * U = 1 ∧ U * U.transpose = 1 :=
    compressionEigenbasis_orthogonal X E hE
  have hdiagC : U.transpose * C * U = Matrix.diagonal lam := by
    have h := compressionEigenbasis_diagonalizes X E hE
    change U.transpose * C * U = Matrix.diagonal lam at h
    exact h
  have hdiagM : U.transpose * M * U = Matrix.diagonal d := by
    simp only [M, d, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, hdiagC, hUU.1]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hUmem : U ∈ Matrix.unitaryGroup (Fin r) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hUU.2
  have hUtmem : U.transpose ∈ Matrix.unitaryGroup (Fin r) ℝ := by
    simpa only [Matrix.transpose_mem_unitaryGroup_iff] using hUmem
  have hnormM : ‖M‖ = ‖Matrix.diagonal d‖ := by
    calc
      ‖M‖ = ‖M * U‖ := (CStarRing.norm_mul_mem_unitary M hUmem).symm
      _ = ‖U.transpose * (M * U)‖ :=
        (CStarRing.norm_mem_unitary_mul (M * U) hUtmem).symm
      _ = ‖Matrix.diagonal d‖ := by
        rw [← Matrix.mul_assoc, hdiagM]
  by_contra hall
  push Not at hall
  have hd (i : Fin r) : |d i| ≤ η := by
    have hi := hall i
    have hθne : θ ≠ 0 := ne_of_gt hθ
    simp only [d]
    rw [show θ⁻¹ * lam i - 1 = (lam i - θ) / θ by
      field_simp [hθne]]
    rw [abs_div, abs_of_pos hθ]
    apply (div_le_iff₀ hθ).2
    simpa [mul_comm] using hi
  have hdnorm : ‖d‖ ≤ η := by
    rw [pi_norm_le_iff_of_nonneg hη.le]
    intro i
    simpa only [Real.norm_eq_abs] using hd i
  have hMle : euclideanOperatorNorm M ≤ η := by
    rw [euclideanOperatorNorm_eq_l2_opNorm, hnormM,
      Matrix.l2_opNorm_diagonal]
    exact hdnorm
  have hbadM : euclideanOperatorNorm M > η := by simpa [M, C] using hbad
  exact (not_lt_of_ge hMle hbadM)

theorem exists_twoProjection_bad_block_trace_gt
    {α : Type*} [Fintype α] [DecidableEq α] {r p : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (δ θ η : ℝ) (hp : 1 ≤ p)
    (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hθ : 0 < θ ∧ θ ≤ 1 / 2)
    (hη : 0 < η ∧ η < 1) (hsmall : δ ≤ θ * η ^ 2 / 64)
    (i : Fin r) (hbad : |compressionEigenvalue X E hE i - θ| > θ * η) :
    ∃ (Q : Matrix α α ℝ) (block : α → α) (b₀ : α),
      IsTwoProjectionBlockDecomposition (X * X.transpose) E Q block ∧
      ((Finset.univ : Finset α).filter (fun k ↦
        ((Finset.univ : Finset α).filter fun j ↦
          block j = block k).card = 2)).card / 2 ≤ r ∧
      b₀ ∈ (Finset.univ : Finset α).image block ∧
      Matrix.trace ((matrixBlock
        (centeredTwoProjectionProduct
          (orthogonalConjugate Q (X * X.transpose))
          (orthogonalConjugate Q E) δ θ) block b₀) ^ (2 * p)) >
        (θ * η / 2) ^ (2 * p) := by
  classical
  letI : Finite (interiorCompressionIndex X E hE) :=
    Finite.of_injective (fun k : interiorCompressionIndex X E hE ↦ k.1)
      Subtype.val_injective
  letI : Fintype (interiorCompressionIndex X E hE) := Fintype.ofFinite _
  letI : DecidableEq (interiorCompressionIndex X E hE) := Classical.decEq _
  let Q := twoProjectionChangeOfBasis X E hX hE
  let block := twoProjectionBlock X E hX hE
  let yi₀ : pairedProjectionAdaptedIndex X E hE := Sum.inl (Sum.inl i)
  let yi := pairedProjectionAdaptedIndexEquiv X E hX hE yi₀
  let b₀ := block yi
  let lam := compressionEigenvalue X E hE i
  have hlam : 0 ≤ lam ∧ lam ≤ 1 := by
    simpa [lam] using compressionEigenvalue_mem_unitInterval X E hX hE i
  have hedge := bad_spectral_edge_large_root lam δ θ η hlam hδ.1 hθ hη hsmall
    (by simpa [lam] using hbad)
  dsimp only at hedge
  have hD : IsTwoProjectionBlockDecomposition (X * X.transpose) E Q block := by
    simpa [Q, block] using
      twoProjectionBlock_isTwoProjectionBlockDecomposition X E hX hE
  have hcount : ((Finset.univ : Finset α).filter (fun k ↦
      ((Finset.univ : Finset α).filter fun j ↦
        block j = block k).card = 2)).card / 2 ≤ r := by
    simpa [block] using
      twoProjectionBlock_two_block_index_card_div_two_le_rank X E hX hE
  have hb₀ : b₀ ∈ (Finset.univ : Finset α).image block := by
    exact Finset.mem_image.mpr ⟨yi, Finset.mem_univ yi, rfl⟩
  have hPii : orthogonalConjugate Q (X * X.transpose) yi yi = 1 := by
    dsimp only [Q, yi, yi₀]
    rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
    have hmul : (X * X.transpose) * rangeEigenbasis X E hE =
        rangeEigenbasis X E hE := by
      simp only [rangeEigenbasis, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc X.transpose X, hX]
      simp
    have hyMul : Matrix.toEuclideanLin (X * X.transpose)
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i))) =
          pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i)) := by
      rw [pairedProjectionAdaptedBasis_inl_inl]
      ext a
      exact congrFun (congrFun hmul a) i
    rw [hyMul, pairedProjectionAdaptedBasis_inner]
    simp
  have hqpos : 0 < θ * η / 2 := div_pos (mul_pos hθ.1 hη.1) (by norm_num)
  have hqnonneg : 0 ≤ θ * η / 2 := hqpos.le
  refine ⟨Q, block, b₀, hD, hcount, hb₀, ?_⟩
  by_cases hint : 0 < lam ∧ lam < 1
  · let ii : interiorCompressionIndex X E hE := ⟨i, by simpa [lam] using hint⟩
    have hcard : ((Finset.univ : Finset α).filter fun j ↦
        block j = block yi).card = 2 := by
      change ((Finset.univ : Finset α).filter (fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE
            (pairedProjectionAdaptedIndexEquiv X E hX hE yi₀))).card = 2
      rw [twoProjectionBlock_fiber_card_equiv X E hX hE yi₀]
      simpa [yi₀, lam, hint] using
        pairedProjectionAdaptedBlock_y_fiber_card X E hE i
    have hEii : orthogonalConjugate Q E yi yi = lam := by
      dsimp only [Q, yi, yi₀]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      have hentry := pairedProjectionAdapted_secondProjection_entry_y_interior
        X E hX hE (Sum.inl (Sum.inl i)) ii
      simpa [ii, lam] using hentry
    have htrace :=
      twoProjection_two_block_trace_eq_canonical_of_primary_diagonal
        (X * X.transpose) E Q block hD δ θ lam (2 * p) yi hcard hPii hEii
    obtain ⟨z₁, z₂, hsum, hprod, hlarge⟩ := hedge.2.2.2 hint.1 hint.2
    rw [htrace]
    exact twoProjectionPairTransferMatrix_trace_even_power_gt_of_large_real_root
      lam δ θ (θ * η / 2) z₁ z₂ p hp hlam hqnonneg
      hsum hprod hlarge
  · have hend : lam = 0 ∨ lam = 1 := by
      simpa [lam] using compressionEigenvalue_endpoint_of_not_interior
        X E hX hE i (by simpa [lam] using hint)
    have hcard : ((Finset.univ : Finset α).filter fun j ↦
        block j = block yi).card = 1 := by
      change ((Finset.univ : Finset α).filter (fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE
            (pairedProjectionAdaptedIndexEquiv X E hX hE yi₀))).card = 1
      rw [twoProjectionBlock_fiber_card_equiv X E hX hE yi₀]
      simpa [yi₀, lam, hint] using
        pairedProjectionAdaptedBlock_y_fiber_card X E hE i
    have hEii : orthogonalConjugate Q E yi yi = lam := by
      dsimp only [Q, yi, yi₀]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      have hentry := pairedProjectionAdapted_secondProjection_entry_y_endpoint
        X E hX hE (Sum.inl (Sum.inl i)) i (by simpa [lam] using hend)
      simpa [lam] using hentry
    have htrace := twoProjection_singleton_block_trace_pow_eq
      (X * X.transpose) E Q block hD δ θ 1 lam (2 * p) yi hcard hPii hEii
    rw [htrace]
    rcases hend with hzero | hone
    · apply even_power_strict_mono_of_abs_gt ((1 - δ) * (lam - θ))
        (θ * η / 2) p hp hqnonneg
      have hpositive : 0 < (1 - δ) * θ := by
        exact hqpos.trans (hedge.2.1 hzero)
      rw [hzero]
      convert hedge.2.1 hzero using 1 <;>
        rw [show (1 - δ) * (0 - θ) = -((1 - δ) * θ) by ring,
          abs_neg, abs_of_pos hpositive]
    · apply even_power_strict_mono_of_abs_gt ((1 - δ) * (lam - θ))
        (θ * η / 2) p hp hqnonneg
      have hpositive : 0 < (1 - δ) * (1 - θ) := by
        exact hqpos.trans (hedge.2.2.1 hone)
      rw [hone, abs_of_pos hpositive]
      exact hedge.2.2.1 hone

theorem two_projection_spectral_transfer_proof
    {α : Type*} [Fintype α] [DecidableEq α] {r p : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (δ θ : ℝ) (hp : 1 ≤ p)
    (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hθ : 0 < θ ∧ θ ≤ 1 / 2) :
    let A := (X * X.transpose - δ • 1) * (E - θ • 1)
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    Matrix.trace (A ^ (2 * p)) ≥ -2 * r * a2 ^ p ∧
      ∀ η : ℝ, 0 < η → η < 1 → δ ≤ θ * η ^ 2 / 64 →
        (if euclideanOperatorNorm (θ⁻¹ • (X.transpose * E * X) - 1) > η
          then (θ * η / 2) ^ (2 * p) else 0) ≤
          Matrix.trace (A ^ (2 * p)) + 2 * r * a2 ^ p := by
  dsimp only
  have hδunit : 0 ≤ δ ∧ δ ≤ 1 :=
    ⟨hδ.1.le, hδ.2.trans (by norm_num)⟩
  have hθunit : 0 ≤ θ ∧ θ ≤ 1 :=
    ⟨hθ.1.le, hθ.2.trans (by norm_num)⟩
  obtain ⟨Q, block, hD, hcount⟩ :=
    twoProjectionBlockDecomposition_exists X E hX hE
  have hlower : Matrix.trace
      (((X * X.transpose - δ • 1) * (E - θ • 1)) ^ (2 * p)) ≥
      -2 * r * (δ * (1 - δ) * θ * (1 - θ)) ^ p := by
    simpa [centeredTwoProjectionProduct] using
      twoProjection_trace_even_power_lower_of_decomposition
        (X * X.transpose) E Q block hD hcount δ θ p hδunit hθunit
  refine ⟨hlower, ?_⟩
  intro η hη0 hη1 hsmall
  by_cases hnorm : euclideanOperatorNorm
      (θ⁻¹ • (X.transpose * E * X) - 1) > η
  · rw [if_pos hnorm]
    obtain ⟨i, hi⟩ := exists_compressionEigenvalue_deviation_of_operatorNorm_gt
      X E hE θ η hθ.1 hη0 hnorm
    obtain ⟨Qbad, blockBad, b₀, hDbad, hcountBad, hb₀, hbadBlock⟩ :=
      exists_twoProjection_bad_block_trace_gt X E hX hE δ θ η hp hδ hθ
        ⟨hη0, hη1⟩ hsmall i hi
    have hstrict := twoProjection_trace_plus_compensation_gt_of_bad_block
      (X * X.transpose) E Qbad blockBad hDbad hcountBad δ θ
        (θ * η / 2) p hδunit hθunit b₀ hb₀ hbadBlock
    exact le_of_lt (by simpa [centeredTwoProjectionProduct] using hstrict)
  · rw [if_neg hnorm]
    linarith

#print axioms exists_compressionEigenvalue_deviation_of_operatorNorm_gt
#print axioms exists_twoProjection_bad_block_trace_gt
#print axioms two_projection_spectral_transfer_proof

end Problem56
