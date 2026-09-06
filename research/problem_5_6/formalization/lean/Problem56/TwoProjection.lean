import Problem56.Definitions

/-!
Kernel-checked prefix for the finite-dimensional two-projection decomposition.
The constructions below start from the frame and the second projection; no
block decomposition or change-of-basis matrix is assumed.
-/

open scoped Matrix

namespace Problem56

private def frameProjection {α : Type*} [Fintype α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) : Matrix α α ℝ :=
  X * X.transpose

theorem frameProjection_isOrthogonalProjection
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X) :
    IsOrthogonalProjection (frameProjection X) := by
  constructor
  · simp only [frameProjection, Matrix.transpose_mul, Matrix.transpose_transpose]
  · simp only [frameProjection, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc X.transpose X X.transpose, hX]
    simp

private def frameCompression {α : Type*} [Fintype α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  X.transpose * E * X

theorem frameCompression_transpose
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    (frameCompression X E).transpose = frameCompression X E := by
  simp only [frameCompression, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hE.1]
  simp only [Matrix.mul_assoc]

theorem frameCompression_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    Matrix.IsHermitian (frameCompression X E) := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact frameCompression_transpose X E hE

noncomputable def compressionEigenbasisMatrix
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Matrix (Fin r) (Fin r) ℝ :=
  frameCompression_isHermitian X E hE |>.eigenvectorUnitary

noncomputable def compressionEigenvalue
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Fin r → ℝ :=
  frameCompression_isHermitian X E hE |>.eigenvalues

theorem compressionEigenbasis_orthogonal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    (compressionEigenbasisMatrix X E hE).transpose *
        compressionEigenbasisMatrix X E hE = 1 ∧
      compressionEigenbasisMatrix X E hE *
        (compressionEigenbasisMatrix X E hE).transpose = 1 := by
  let hC := frameCompression_isHermitian X E hE
  let Uunit := hC.eigenvectorUnitary
  have hleft := Unitary.coe_star_mul_self Uunit
  have hright := Unitary.coe_mul_star_self Uunit
  constructor
  · simpa [compressionEigenbasisMatrix, hC, Uunit,
      Matrix.star_eq_conjTranspose] using hleft
  · simpa [compressionEigenbasisMatrix, hC, Uunit,
      Matrix.star_eq_conjTranspose] using hright

theorem compressionEigenbasis_diagonalizes
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    (compressionEigenbasisMatrix X E hE).transpose *
        frameCompression X E * compressionEigenbasisMatrix X E hE =
      Matrix.diagonal (compressionEigenvalue X E hE) := by
  let hC := frameCompression_isHermitian X E hE
  have hdiag := hC.conjStarAlgAut_star_eigenvectorUnitary
  simpa [Unitary.conjStarAlgAut_star_apply, compressionEigenbasisMatrix,
    compressionEigenvalue, hC, Matrix.star_eq_conjTranspose] using hdiag

noncomputable def rangeEigenbasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Matrix α (Fin r) ℝ :=
  X * compressionEigenbasisMatrix X E hE

theorem rangeEigenbasis_orthonormal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    OrthonormalFrame (rangeEigenbasis X E hE) := by
  have hU := (compressionEigenbasis_orthogonal X E hE).1
  simp only [OrthonormalFrame, rangeEigenbasis, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc X.transpose X, hX]
  simpa using hU

theorem frameProjection_mul_rangeEigenbasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    frameProjection X * rangeEigenbasis X E hE = rangeEigenbasis X E hE := by
  simp only [frameProjection, rangeEigenbasis, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc X.transpose X, hX]
  simp

theorem rangeEigenbasis_mul_transpose
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    rangeEigenbasis X E hE * (rangeEigenbasis X E hE).transpose =
      frameProjection X := by
  have hUU := (compressionEigenbasis_orthogonal X E hE).2
  simp only [rangeEigenbasis, frameProjection, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (compressionEigenbasisMatrix X E hE)
    (compressionEigenbasisMatrix X E hE).transpose X.transpose, hUU]
  simp

theorem rangeEigenbasis_compresses_E_to_diagonal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    (rangeEigenbasis X E hE).transpose * E * rangeEigenbasis X E hE =
      Matrix.diagonal (compressionEigenvalue X E hE) := by
  simpa only [rangeEigenbasis, frameCompression, Matrix.transpose_mul,
    Matrix.mul_assoc] using compressionEigenbasis_diagonalizes X E hE

noncomputable def compressionDiagonal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (compressionEigenvalue X E hE)

theorem compressionEigenbasis_intertwines
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    frameCompression X E * compressionEigenbasisMatrix X E hE =
      compressionEigenbasisMatrix X E hE * compressionDiagonal X E hE := by
  let U := compressionEigenbasisMatrix X E hE
  let C := frameCompression X E
  let D := compressionDiagonal X E hE
  have hUU : U * U.transpose = 1 := (compressionEigenbasis_orthogonal X E hE).2
  have hdiag : U.transpose * C * U = D := by
    simpa only [U, C, D, compressionDiagonal] using
      compressionEigenbasis_diagonalizes X E hE
  change C * U = U * D
  calc
    C * U = 1 * (C * U) := by simp
    _ = (U * U.transpose) * (C * U) := by rw [hUU]
    _ = U * (U.transpose * C * U) := by simp only [Matrix.mul_assoc]
    _ = U * D := by rw [hdiag]

theorem frameProjection_mul_E_mul_rangeEigenbasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    frameProjection X * E * rangeEigenbasis X E hE =
      rangeEigenbasis X E hE * compressionDiagonal X E hE := by
  have hintertwine := compressionEigenbasis_intertwines X E hE
  simp only [frameProjection, rangeEigenbasis, frameCompression,
    Matrix.mul_assoc] at hintertwine ⊢
  exact congrArg (fun M ↦ X * M) hintertwine

noncomputable def pairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Matrix α (Fin r) ℝ :=
  E * rangeEigenbasis X E hE -
    rangeEigenbasis X E hE * compressionDiagonal X E hE

theorem frameProjection_annihilates_pairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    frameProjection X * pairingResidual X E hE = 0 := by
  rw [pairingResidual, Matrix.mul_sub]
  simp only [← Matrix.mul_assoc,
    frameProjection_mul_E_mul_rangeEigenbasis X E hX hE,
    frameProjection_mul_rangeEigenbasis X E hX hE, sub_self]

theorem rangeEigenbasis_orthogonal_to_pairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    (rangeEigenbasis X E hE).transpose * pairingResidual X E hE = 0 := by
  let Y := rangeEigenbasis X E hE
  let D := compressionDiagonal X E hE
  have hleft : Y.transpose * (E * Y) = D := by
    rw [← Matrix.mul_assoc]
    simpa only [Y, D, compressionDiagonal] using
      rangeEigenbasis_compresses_E_to_diagonal X E hE
  have hright : Y.transpose * (Y * D) = D := by
    rw [← Matrix.mul_assoc, show Y.transpose * Y = 1 by
      exact rangeEigenbasis_orthonormal X E hX hE]
    simp
  change Y.transpose * (E * Y - Y * D) = 0
  rw [Matrix.mul_sub, hleft, hright, sub_self]

theorem compressionDiagonal_transpose
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    (compressionDiagonal X E hE).transpose = compressionDiagonal X E hE := by
  simp [compressionDiagonal]

theorem pairingResidual_gram
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    (pairingResidual X E hE).transpose * pairingResidual X E hE =
      compressionDiagonal X E hE -
        compressionDiagonal X E hE * compressionDiagonal X E hE := by
  let Y := rangeEigenbasis X E hE
  let D := compressionDiagonal X E hE
  have hY : Y.transpose * Y = 1 := rangeEigenbasis_orthonormal X E hX hE
  have hYEY : Y.transpose * E * Y = D := by
    simpa only [Y, D, compressionDiagonal] using
      rangeEigenbasis_compresses_E_to_diagonal X E hE
  have hDt : D.transpose = D := by
    simpa only [D] using compressionDiagonal_transpose X E hE
  have htermOne : (Y.transpose * E) * (E * Y) = D := by
    calc
      (Y.transpose * E) * (E * Y) = Y.transpose * (E * E) * Y := by
        simp only [Matrix.mul_assoc]
      _ = Y.transpose * E * Y := by rw [hE.2]
      _ = D := hYEY
  have htermTwo : (Y.transpose * E) * (Y * D) = D * D := by
    calc
      (Y.transpose * E) * (Y * D) = (Y.transpose * E * Y) * D := by
        simp only [Matrix.mul_assoc]
      _ = D * D := by rw [hYEY]
  have htermThree : (D * Y.transpose) * (E * Y) = D * D := by
    calc
      (D * Y.transpose) * (E * Y) = D * (Y.transpose * E * Y) := by
        simp only [Matrix.mul_assoc]
      _ = D * D := by rw [hYEY]
  have htermFour : (D * Y.transpose) * (Y * D) = D * D := by
    calc
      (D * Y.transpose) * (Y * D) = D * (Y.transpose * Y) * D := by
        simp only [Matrix.mul_assoc]
      _ = D * 1 * D := by rw [hY]
      _ = D * D := by simp
  change (E * Y - Y * D).transpose * (E * Y - Y * D) = D - D * D
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hE.1, hDt]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    htermOne, htermTwo, htermThree, htermFour]
  abel

theorem pairingResidual_inner
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i j : Fin r) :
    ((pairingResidual X E hE).transpose * pairingResidual X E hE) i j =
      if i = j then
        compressionEigenvalue X E hE i *
          (1 - compressionEigenvalue X E hE i)
      else 0 := by
  rw [pairingResidual_gram X E hX hE]
  by_cases hij : i = j
  · subst j
    simp [compressionDiagonal]
    ring
  · simp [compressionDiagonal, hij]

theorem pairingResidual_column_eq_zero_of_eigenvalue_endpoint
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin r)
    (hi : compressionEigenvalue X E hE i = 0 ∨
      compressionEigenvalue X E hE i = 1) :
    ∀ a, pairingResidual X E hE a i = 0 := by
  let R := pairingResidual X E hE
  have hdiag := pairingResidual_inner X E hX hE i i
  simp only [if_pos] at hdiag
  have hzero : (R.transpose * R) i i = 0 := by
    rw [hdiag]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  have hdot : (fun a ↦ R a i) ⬝ᵥ (fun a ↦ R a i) = 0 := by
    simpa only [dotProduct, Matrix.mul_apply, Matrix.transpose_apply] using hzero
  have hfun : (fun a ↦ R a i) = 0 := dotProduct_self_eq_zero.mp hdot
  intro a
  exact congrFun hfun a

theorem compressionEigenvalue_mem_unitInterval
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin r) : compressionEigenvalue X E hE i ∈ Set.Icc (0 : ℝ) 1 := by
  let R := pairingResidual X E hE
  let lam := compressionEigenvalue X E hE i
  have hnonneg : 0 ≤ (R.transpose * R) i i := by
    rw [Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro a _
    simp only [Matrix.transpose_apply]
    exact mul_self_nonneg (R a i)
  have hdiag := pairingResidual_inner X E hX hE i i
  simp only [if_pos] at hdiag
  have hprod : 0 ≤ lam * (1 - lam) := by
    rw [← hdiag]
    exact hnonneg
  constructor <;> nlinarith

theorem compressionEigenvalue_endpoint_of_not_interior
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin r)
    (hi : ¬ (0 < compressionEigenvalue X E hE i ∧
      compressionEigenvalue X E hE i < 1)) :
    compressionEigenvalue X E hE i = 0 ∨
      compressionEigenvalue X E hE i = 1 := by
  have hmem := compressionEigenvalue_mem_unitInterval X E hX hE i
  rcases hmem with ⟨hlo, hhi⟩
  by_cases hz : compressionEigenvalue X E hE i = 0
  · exact Or.inl hz
  · right
    push_neg at hi
    have hpos : 0 < compressionEigenvalue X E hE i :=
      lt_of_le_of_ne hlo (Ne.symm hz)
    exact le_antisymm hhi (hi hpos)

noncomputable def interiorCompressionIndex
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :=
  {i : Fin r // 0 < compressionEigenvalue X E hE i ∧
    compressionEigenvalue X E hE i < 1}

noncomputable def normalizedPairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    Matrix α (interiorCompressionIndex X E hE) ℝ :=
  fun a i ↦ pairingResidual X E hE a i.1 /
    Real.sqrt (compressionEigenvalue X E hE i.1 *
      (1 - compressionEigenvalue X E hE i.1))

theorem normalizedPairingResidual_inner
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i j : interiorCompressionIndex X E hE) :
    ((normalizedPairingResidual X E hE).transpose *
        normalizedPairingResidual X E hE) i j =
      if i.1 = j.1 then 1 else 0 := by
  let R := pairingResidual X E hE
  let lam := compressionEigenvalue X E hE
  let s : interiorCompressionIndex X E hE → ℝ := fun i ↦
    Real.sqrt (lam i.1 * (1 - lam i.1))
  have hspos (i : interiorCompressionIndex X E hE) : 0 < s i := by
    apply Real.sqrt_pos.2
    exact mul_pos i.2.1 (sub_pos.2 i.2.2)
  have hgram := pairingResidual_inner X E hX hE i.1 j.1
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hgram ⊢
  change (∑ a, (R a i.1 / s i) * (R a j.1 / s j)) = _
  calc
    (∑ a, (R a i.1 / s i) * (R a j.1 / s j)) =
        (∑ a, R a i.1 * R a j.1) / (s i * s j) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (if i.1 = j.1 then lam i.1 * (1 - lam i.1) else 0) /
        (s i * s j) := by rw [hgram]
    _ = if i.1 = j.1 then 1 else 0 := by
      by_cases hval : i.1 = j.1
      · have hij : i = j := Subtype.ext hval
        subst j
        simp only [if_pos]
        have hsquare : s i * s i = lam i.1 * (1 - lam i.1) := by
          rw [show s i * s i = (s i) ^ 2 by ring]
          exact Real.sq_sqrt (le_of_lt (mul_pos i.2.1 (sub_pos.2 i.2.2)))
        rw [hsquare]
        exact div_self (ne_of_gt (mul_pos i.2.1 (sub_pos.2 i.2.2)))
      · simp [hval]

theorem normalizedPairingResidual_gram
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    (normalizedPairingResidual X E hE).transpose *
        normalizedPairingResidual X E hE =
      fun i j ↦ if i.1 = j.1 then 1 else 0 := by
  ext i j
  exact normalizedPairingResidual_inner X E hX hE i j

theorem rangeEigenbasis_orthogonal_to_normalizedPairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    (rangeEigenbasis X E hE).transpose * normalizedPairingResidual X E hE = 0 := by
  have hYR := rangeEigenbasis_orthogonal_to_pairingResidual X E hX hE
  ext i j
  have hzero :
      (∑ a, rangeEigenbasis X E hE a i * pairingResidual X E hE a j.1) = 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using
      congrFun (congrFun hYR i) j.1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    normalizedPairingResidual, div_eq_mul_inv]
  calc
    (∑ a, rangeEigenbasis X E hE a i *
        (pairingResidual X E hE a j.1 *
          (Real.sqrt (compressionEigenvalue X E hE j.1 *
            (1 - compressionEigenvalue X E hE j.1)))⁻¹)) =
        (∑ a, rangeEigenbasis X E hE a i * pairingResidual X E hE a j.1) *
          (Real.sqrt (compressionEigenvalue X E hE j.1 *
            (1 - compressionEigenvalue X E hE j.1)))⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [hzero]; simp

noncomputable def rangeEigenvector
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) (i : Fin r) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun a ↦ rangeEigenbasis X E hE a i)

noncomputable def normalizedPairingResidualVector
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    (i : interiorCompressionIndex X E hE) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun a ↦ normalizedPairingResidual X E hE a i)

noncomputable def pairedProjectionFamily
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    Fin r ⊕ interiorCompressionIndex X E hE → EuclideanSpace ℝ α
  | Sum.inl i => rangeEigenvector X E hE i
  | Sum.inr i => normalizedPairingResidualVector X E hE i

theorem pairedProjectionFamily_orthonormal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    Orthonormal ℝ (pairedProjectionFamily X E hE) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · have hYY := rangeEigenbasis_orthonormal X E hX hE
    have hij := congrFun (congrFun hYY i) j
    simpa [pairedProjectionFamily, rangeEigenvector, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, mul_comm] using hij
  · have hYZ := rangeEigenbasis_orthogonal_to_normalizedPairingResidual X E hX hE
    have hij := congrFun (congrFun hYZ i) j
    simpa [pairedProjectionFamily, rangeEigenvector,
      normalizedPairingResidualVector, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      mul_comm]
      using hij
  · have hYZ := rangeEigenbasis_orthogonal_to_normalizedPairingResidual X E hX hE
    have hji := congrFun (congrFun hYZ j) i
    simpa [pairedProjectionFamily, rangeEigenvector,
      normalizedPairingResidualVector, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      mul_comm] using hji
  · have hZZ := normalizedPairingResidual_inner X E hX hE i j
    by_cases hij : i = j
    · subst j
      simp only [pairedProjectionFamily, normalizedPairingResidualVector,
        PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Sum.inr.injEq,
        if_pos]
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, if_pos] using hZZ
    · have hval : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
      simp only [pairedProjectionFamily, normalizedPairingResidualVector,
        PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Sum.inr.injEq,
        if_neg hij]
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, if_neg hval,
        mul_comm] using hZZ

theorem secondProjection_mul_pairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    E * pairingResidual X E hE =
      rangeEigenbasis X E hE *
          (compressionDiagonal X E hE -
            compressionDiagonal X E hE * compressionDiagonal X E hE) +
        pairingResidual X E hE * (1 - compressionDiagonal X E hE) := by
  let Y := rangeEigenbasis X E hE
  let D := compressionDiagonal X E hE
  change E * (E * Y - Y * D) =
    Y * (D - D * D) + (E * Y - Y * D) * (1 - D)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc E E Y, hE.2]
  abel

theorem secondProjection_mul_rangeEigenbasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    E * rangeEigenbasis X E hE =
      pairingResidual X E hE +
        rangeEigenbasis X E hE * compressionDiagonal X E hE := by
  rw [pairingResidual]
  abel

theorem secondProjection_rangeEigenbasis_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) (a : α) (i : Fin r) :
    (E * rangeEigenbasis X E hE) a i =
      pairingResidual X E hE a i +
        compressionEigenvalue X E hE i * rangeEigenbasis X E hE a i := by
  rw [secondProjection_mul_rangeEigenbasis X E hE]
  simp [compressionDiagonal, Matrix.mul_diagonal]
  ring

theorem secondProjection_pairingResidual_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) (a : α) (i : Fin r) :
    (E * pairingResidual X E hE) a i =
      compressionEigenvalue X E hE i *
          (1 - compressionEigenvalue X E hE i) *
          rangeEigenbasis X E hE a i +
        (1 - compressionEigenvalue X E hE i) *
          pairingResidual X E hE a i := by
  have hdiagdiff :
      compressionDiagonal X E hE -
          compressionDiagonal X E hE * compressionDiagonal X E hE =
        Matrix.diagonal (fun i ↦ compressionEigenvalue X E hE i *
          (1 - compressionEigenvalue X E hE i)) := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp [compressionDiagonal]
      ring
    · simp [compressionDiagonal, huv]
  have honeminus :
      (1 : Matrix (Fin r) (Fin r) ℝ) - compressionDiagonal X E hE =
        Matrix.diagonal (fun i ↦ 1 - compressionEigenvalue X E hE i) := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp [compressionDiagonal]
    · simp [compressionDiagonal, huv]
  rw [secondProjection_mul_pairingResidual X E hE]
  rw [hdiagdiff, honeminus]
  simp [Matrix.mul_diagonal]
  ring

theorem frameProjection_mul_normalizedPairingResidual
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    frameProjection X * normalizedPairingResidual X E hE = 0 := by
  have hPR := frameProjection_annihilates_pairingResidual X E hX hE
  ext a i
  have hzero :
      (∑ b, frameProjection X a b * pairingResidual X E hE b i.1) = 0 := by
    simpa only [Matrix.mul_apply, Matrix.zero_apply] using
      congrFun (congrFun hPR a) i.1
  simp only [Matrix.mul_apply, Matrix.zero_apply, normalizedPairingResidual,
    div_eq_mul_inv]
  calc
    (∑ b, frameProjection X a b *
        (pairingResidual X E hE b i.1 *
          (Real.sqrt (compressionEigenvalue X E hE i.1 *
            (1 - compressionEigenvalue X E hE i.1)))⁻¹)) =
        (∑ b, frameProjection X a b * pairingResidual X E hE b i.1) *
          (Real.sqrt (compressionEigenvalue X E hE i.1 *
            (1 - compressionEigenvalue X E hE i.1)))⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = 0 := by rw [hzero]; simp

theorem secondProjection_rangeEigenbasis_endpoint_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin r)
    (hi : compressionEigenvalue X E hE i = 0 ∨
      compressionEigenvalue X E hE i = 1) (a : α) :
    (E * rangeEigenbasis X E hE) a i =
      compressionEigenvalue X E hE i * rangeEigenbasis X E hE a i := by
  rw [secondProjection_rangeEigenbasis_apply X E hE]
  rw [pairingResidual_column_eq_zero_of_eigenvalue_endpoint X E hX hE i hi a]
  ring

theorem secondProjection_rangeEigenbasis_interior_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    (i : interiorCompressionIndex X E hE) (a : α) :
    (E * rangeEigenbasis X E hE) a i.1 =
      compressionEigenvalue X E hE i.1 * rangeEigenbasis X E hE a i.1 +
        Real.sqrt (compressionEigenvalue X E hE i.1 *
          (1 - compressionEigenvalue X E hE i.1)) *
          normalizedPairingResidual X E hE a i := by
  have hspos : 0 < Real.sqrt (compressionEigenvalue X E hE i.1 *
      (1 - compressionEigenvalue X E hE i.1)) := by
    apply Real.sqrt_pos.2
    exact mul_pos i.2.1 (sub_pos.2 i.2.2)
  rw [secondProjection_rangeEigenbasis_apply X E hE]
  simp only [normalizedPairingResidual]
  field_simp [ne_of_gt hspos]
  <;> ring

theorem secondProjection_normalizedPairingResidual_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    (i : interiorCompressionIndex X E hE) (a : α) :
    (E * normalizedPairingResidual X E hE) a i =
      Real.sqrt (compressionEigenvalue X E hE i.1 *
          (1 - compressionEigenvalue X E hE i.1)) *
          rangeEigenbasis X E hE a i.1 +
        (1 - compressionEigenvalue X E hE i.1) *
          normalizedPairingResidual X E hE a i := by
  let lam := compressionEigenvalue X E hE i.1
  let s := Real.sqrt (lam * (1 - lam))
  have hspos : 0 < s := by
    apply Real.sqrt_pos.2
    exact mul_pos i.2.1 (sub_pos.2 i.2.2)
  have hsquare : s * s = lam * (1 - lam) := by
    rw [show s * s = s ^ 2 by ring]
    exact Real.sq_sqrt (le_of_lt (mul_pos i.2.1 (sub_pos.2 i.2.2)))
  have hER := secondProjection_pairingResidual_apply X E hE a i.1
  change (∑ b, E a b * (pairingResidual X E hE b i.1 / s)) =
    s * rangeEigenbasis X E hE a i.1 +
      (1 - lam) * (pairingResidual X E hE a i.1 / s)
  calc
    (∑ b, E a b * (pairingResidual X E hE b i.1 / s)) =
        (∑ b, E a b * pairingResidual X E hE b i.1) / s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = (lam * (1 - lam) * rangeEigenbasis X E hE a i.1 +
        (1 - lam) * pairingResidual X E hE a i.1) / s := by
      simpa only [Matrix.mul_apply, lam] using congrArg (fun z ↦ z / s) hER
    _ = s * rangeEigenbasis X E hE a i.1 +
        (1 - lam) * (pairingResidual X E hE a i.1 / s) := by
      field_simp [ne_of_gt hspos]
      rw [show s ^ 2 = lam * (1 - lam) by nlinarith [hsquare]]
      ring

theorem secondProjection_pairedProjectionFamily_mem_span
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin r ⊕ interiorCompressionIndex X E hE) :
    Matrix.toEuclideanLin E (pairedProjectionFamily X E hE i) ∈
      Submodule.span ℝ (Set.range (pairedProjectionFamily X E hE)) := by
  let S := Submodule.span ℝ (Set.range (pairedProjectionFamily X E hE))
  rcases i with i | i
  · by_cases hi : 0 < compressionEigenvalue X E hE i ∧
        compressionEigenvalue X E hE i < 1
    · let ii : interiorCompressionIndex X E hE := ⟨i, hi⟩
      have haction :
          Matrix.toEuclideanLin E (rangeEigenvector X E hE i) =
            compressionEigenvalue X E hE i • rangeEigenvector X E hE i +
              Real.sqrt (compressionEigenvalue X E hE i *
                (1 - compressionEigenvalue X E hE i)) •
                normalizedPairingResidualVector X E hE ii := by
        ext a
        exact secondProjection_rangeEigenbasis_interior_apply X E hE ii a
      rw [pairedProjectionFamily, haction]
      exact S.add_mem
        (S.smul_mem _ (Submodule.subset_span (Set.mem_range_self (Sum.inl i))))
        (S.smul_mem _ (Submodule.subset_span (Set.mem_range_self (Sum.inr ii))))
    · have hmem := compressionEigenvalue_mem_unitInterval X E hX hE i
      have hend : compressionEigenvalue X E hE i = 0 ∨
          compressionEigenvalue X E hE i = 1 := by
        rcases hmem with ⟨hlo, hhi⟩
        by_cases hz : compressionEigenvalue X E hE i = 0
        · exact Or.inl hz
        · right
          push_neg at hi
          have hpos : 0 < compressionEigenvalue X E hE i := lt_of_le_of_ne hlo (Ne.symm hz)
          exact le_antisymm hhi (hi hpos)
      have haction :
          Matrix.toEuclideanLin E (rangeEigenvector X E hE i) =
            compressionEigenvalue X E hE i • rangeEigenvector X E hE i := by
        ext a
        exact secondProjection_rangeEigenbasis_endpoint_apply X E hX hE i hend a
      rw [pairedProjectionFamily, haction]
      exact S.smul_mem _ (Submodule.subset_span (Set.mem_range_self (Sum.inl i)))
  · have haction :
        Matrix.toEuclideanLin E (normalizedPairingResidualVector X E hE i) =
          Real.sqrt (compressionEigenvalue X E hE i.1 *
              (1 - compressionEigenvalue X E hE i.1)) •
              rangeEigenvector X E hE i.1 +
            (1 - compressionEigenvalue X E hE i.1) •
              normalizedPairingResidualVector X E hE i := by
      ext a
      exact secondProjection_normalizedPairingResidual_apply X E hE i a
    rw [pairedProjectionFamily, haction]
    exact S.add_mem
      (S.smul_mem _ (Submodule.subset_span (Set.mem_range_self (Sum.inl i.1))))
      (S.smul_mem _ (Submodule.subset_span (Set.mem_range_self (Sum.inr i))))

theorem secondProjection_pairedSpan_invariant
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (x : EuclideanSpace ℝ α)
    (hx : x ∈ Submodule.span ℝ
      (Set.range (pairedProjectionFamily X E hE))) :
    Matrix.toEuclideanLin E x ∈ Submodule.span ℝ
      (Set.range (pairedProjectionFamily X E hE)) := by
  let S := Submodule.span ℝ (Set.range (pairedProjectionFamily X E hE))
  refine Submodule.span_induction (p := fun x _ ↦ Matrix.toEuclideanLin E x ∈ S)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact secondProjection_pairedProjectionFamily_mem_span X E hX hE i
  · simpa only [map_zero] using S.zero_mem
  · intro y z _ _ hy hz
    simpa only [map_add] using S.add_mem hy hz
  · intro c y _ hy
    simpa only [map_smul] using S.smul_mem c hy

theorem secondProjection_pairedSpan_orthogonal_invariant
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (x : EuclideanSpace ℝ α)
    (hx : x ∈ Submodule.orthogonal (Submodule.span ℝ
      (Set.range (pairedProjectionFamily X E hE)))) :
    Matrix.toEuclideanLin E x ∈ Submodule.orthogonal (Submodule.span ℝ
      (Set.range (pairedProjectionFamily X E hE))) := by
  let S := Submodule.span ℝ (Set.range (pairedProjectionFamily X E hE))
  have hEH : Matrix.IsHermitian E := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact hE.1
  have hsym : (Matrix.toEuclideanLin E).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hEH
  rw [S.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [hsym]
  exact hx _ (secondProjection_pairedSpan_invariant X E hX hE y hy)

abbrev pairedProjectionSpan
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Submodule ℝ (EuclideanSpace ℝ α) :=
  Submodule.span ℝ (Set.range (pairedProjectionFamily X E hE))

noncomputable abbrev pairedProjectionComplement
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) : Submodule ℝ (EuclideanSpace ℝ α) :=
  Submodule.orthogonal (pairedProjectionSpan X E hE)

noncomputable def pairedComplementProjection
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    pairedProjectionComplement X E hE →ₗ[ℝ]
      pairedProjectionComplement X E hE :=
  ((Matrix.toEuclideanLin E).domRestrict (pairedProjectionComplement X E hE)).codRestrict
    (pairedProjectionComplement X E hE) fun x ↦ by
      exact secondProjection_pairedSpan_orthogonal_invariant X E hX hE x x.2

theorem frameProjection_annihilates_pairedComplement
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    (x : pairedProjectionComplement X E hE) :
    Matrix.toEuclideanLin (frameProjection X) (x : EuclideanSpace ℝ α) = 0 := by
  let Y := rangeEigenbasis X E hE
  have hYtx : Y.transpose *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ α) = 0 := by
    funext i
    have hyS : rangeEigenvector X E hE i ∈ pairedProjectionSpan X E hE :=
      Submodule.subset_span (Set.mem_range_self (Sum.inl i))
    have hinner := Submodule.inner_right_of_mem_orthogonal hyS x.2
    simpa only [rangeEigenvector, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm,
      Y, Pi.zero_apply] using hinner
  ext a
  change (frameProjection X *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ α)) a = 0
  rw [← rangeEigenbasis_mul_transpose X E hE, ← Matrix.mulVec_mulVec, hYtx]
  simp

theorem pairedComplementProjection_isSymmetric
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    (pairedComplementProjection X E hX hE).IsSymmetric := by
  have hEH : Matrix.IsHermitian E := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact hE.1
  have hsym : (Matrix.toEuclideanLin E).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hEH
  intro x y
  exact hsym x y

theorem pairedComplementProjection_idempotent
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (x : pairedProjectionComplement X E hE) :
    pairedComplementProjection X E hX hE
        (pairedComplementProjection X E hX hE x) =
      pairedComplementProjection X E hX hE x := by
  apply Subtype.ext
  change Matrix.toEuclideanLin E (Matrix.toEuclideanLin E x) =
    Matrix.toEuclideanLin E x
  ext a
  change (E *ᵥ (E *ᵥ (WithLp.ofLp (x : EuclideanSpace ℝ α)))) a =
    (E *ᵥ (WithLp.ofLp (x : EuclideanSpace ℝ α))) a
  rw [Matrix.mulVec_mulVec, hE.2]

noncomputable def pairedComplementEigenbasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) ℝ
      (pairedProjectionComplement X E hE) :=
  (pairedComplementProjection_isSymmetric X E hX hE).eigenvectorBasis rfl

noncomputable def pairedComplementEigenvalue
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    Fin (Module.finrank ℝ (pairedProjectionComplement X E hE)) → ℝ :=
  (pairedComplementProjection_isSymmetric X E hX hE).eigenvalues rfl

theorem pairedComplementProjection_mul_eigenbasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    pairedComplementProjection X E hX hE
        (pairedComplementEigenbasis X E hX hE i) =
      pairedComplementEigenvalue X E hX hE i •
        pairedComplementEigenbasis X E hX hE i := by
  exact (pairedComplementProjection_isSymmetric X E hX hE).apply_eigenvectorBasis rfl i

theorem pairedComplementEigenvalue_endpoint
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (i : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    pairedComplementEigenvalue X E hX hE i = 0 ∨
      pairedComplementEigenvalue X E hX hE i = 1 := by
  let T := pairedComplementProjection X E hX hE
  let b := pairedComplementEigenbasis X E hX hE
  let mu := pairedComplementEigenvalue X E hX hE i
  have hact : T (b i) = mu • b i :=
    pairedComplementProjection_mul_eigenbasis X E hX hE i
  have hidem := pairedComplementProjection_idempotent X E hX hE (b i)
  change T (T (b i)) = T (b i) at hidem
  rw [hact, map_smul, hact] at hidem
  have hbne : b i ≠ 0 := b.orthonormal.ne_zero i
  have hscalar : mu * mu = mu := by
    apply smul_left_injective ℝ hbne
    simpa only [mul_smul] using hidem
  have hfactor : mu * (mu - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hone)

noncomputable def pairedProjectionSpanBasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    OrthonormalBasis (Fin r ⊕ interiorCompressionIndex X E hE) ℝ
      (pairedProjectionSpan X E hE) := by
  let v := pairedProjectionFamily X E hE
  let b₀ := OrthonormalBasis.span (pairedProjectionFamily_orthonormal X E hX hE)
    (Finset.univ : Finset (Fin r ⊕ interiorCompressionIndex X E hE))
  have hset : ((↑((Finset.univ :
      Finset (Fin r ⊕ interiorCompressionIndex X E hE)).image v)) :
      Set (EuclideanSpace ℝ α)) = Set.range v := by
    ext x
    simp
  have hspan : Submodule.span ℝ
      ((↑((Finset.univ :
        Finset (Fin r ⊕ interiorCompressionIndex X E hE)).image v)) :
        Set (EuclideanSpace ℝ α)) = pairedProjectionSpan X E hE := by
    rw [hset]
  let eUniv : (↑(Finset.univ :
      Finset (Fin r ⊕ interiorCompressionIndex X E hE))) ≃
      (Fin r ⊕ interiorCompressionIndex X E hE) :=
    { toFun := Subtype.val
      invFun := fun i ↦ ⟨i, Finset.mem_univ i⟩
      left_inv := fun i ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  exact (b₀.map (LinearIsometryEquiv.ofEq _ _ hspan)).reindex eUniv

theorem pairedProjectionSpanBasis_inl
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (i : Fin r) :
    ((pairedProjectionSpanBasis X E hX hE (Sum.inl i) :
      pairedProjectionSpan X E hE) : EuclideanSpace ℝ α) =
        rangeEigenvector X E hE i := by
  simp [pairedProjectionSpanBasis, pairedProjectionFamily]

theorem pairedProjectionSpanBasis_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : interiorCompressionIndex X E hE) :
    ((pairedProjectionSpanBasis X E hX hE (Sum.inr i) :
      pairedProjectionSpan X E hE) : EuclideanSpace ℝ α) =
        normalizedPairingResidualVector X E hE i := by
  simp [pairedProjectionSpanBasis, pairedProjectionFamily]

noncomputable def pairedProjectionAdaptedBasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    OrthonormalBasis
      ((Fin r ⊕ interiorCompressionIndex X E hE) ⊕
        Fin (Module.finrank ℝ (pairedProjectionComplement X E hE)))
      ℝ (EuclideanSpace ℝ α) :=
  ((pairedProjectionSpanBasis X E hX hE).prod
      (pairedComplementEigenbasis X E hX hE)).map
    (pairedProjectionSpan X E hE).orthogonalDecomposition.symm

theorem pairedProjectionAdaptedBasis_inl_inl
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (i : Fin r) :
    pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i)) =
      rangeEigenvector X E hE i := by
  rw [pairedProjectionAdaptedBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply]
  simp [
    Submodule.toLinearEquiv_orthogonalDecomposition_symm,
    Submodule.coe_prodEquivOfIsCompl', pairedProjectionSpanBasis_inl]

theorem pairedProjectionAdaptedBasis_inl_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : interiorCompressionIndex X E hE) :
    pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inr i)) =
      normalizedPairingResidualVector X E hE i := by
  rw [pairedProjectionAdaptedBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply]
  simp [
    Submodule.toLinearEquiv_orthogonalDecomposition_symm,
    Submodule.coe_prodEquivOfIsCompl', pairedProjectionSpanBasis_inr]

theorem pairedProjectionAdaptedBasis_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    pairedProjectionAdaptedBasis X E hX hE (Sum.inr i) =
      (pairedComplementEigenbasis X E hX hE i :
        pairedProjectionComplement X E hE) := by
  rw [pairedProjectionAdaptedBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply]
  simp [
    Submodule.toLinearEquiv_orthogonalDecomposition_symm,
    Submodule.coe_prodEquivOfIsCompl']

theorem frameProjection_mul_adaptedBasis_inl_inl
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (i : Fin r) :
    Matrix.toEuclideanLin (frameProjection X)
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i))) =
      pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i)) := by
  rw [pairedProjectionAdaptedBasis_inl_inl]
  ext a
  exact congrFun (congrFun
    (frameProjection_mul_rangeEigenbasis X E hX hE) a) i

theorem frameProjection_mul_adaptedBasis_inl_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : interiorCompressionIndex X E hE) :
    Matrix.toEuclideanLin (frameProjection X)
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inr i))) = 0 := by
  rw [pairedProjectionAdaptedBasis_inl_inr]
  ext a
  exact congrFun (congrFun
    (frameProjection_mul_normalizedPairingResidual X E hX hE) a) i

theorem frameProjection_mul_adaptedBasis_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    Matrix.toEuclideanLin (frameProjection X)
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inr i)) = 0 := by
  rw [pairedProjectionAdaptedBasis_inr]
  exact frameProjection_annihilates_pairedComplement X E hE
    (pairedComplementEigenbasis X E hX hE i)

theorem secondProjection_mul_adaptedBasis_inl_inl_interior
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : interiorCompressionIndex X E hE) :
    Matrix.toEuclideanLin E
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i.1))) =
      compressionEigenvalue X E hE i.1 •
          pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i.1)) +
        Real.sqrt (compressionEigenvalue X E hE i.1 *
          (1 - compressionEigenvalue X E hE i.1)) •
          pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inr i)) := by
  rw [pairedProjectionAdaptedBasis_inl_inl,
    pairedProjectionAdaptedBasis_inl_inr]
  ext a
  exact secondProjection_rangeEigenbasis_interior_apply X E hE i a

theorem secondProjection_mul_adaptedBasis_inl_inl_endpoint
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (i : Fin r)
    (hi : compressionEigenvalue X E hE i = 0 ∨
      compressionEigenvalue X E hE i = 1) :
    Matrix.toEuclideanLin E
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i))) =
      compressionEigenvalue X E hE i •
        pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i)) := by
  rw [pairedProjectionAdaptedBasis_inl_inl]
  ext a
  exact secondProjection_rangeEigenbasis_endpoint_apply X E hX hE i hi a

theorem secondProjection_mul_adaptedBasis_inl_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : interiorCompressionIndex X E hE) :
    Matrix.toEuclideanLin E
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inr i))) =
      Real.sqrt (compressionEigenvalue X E hE i.1 *
          (1 - compressionEigenvalue X E hE i.1)) •
          pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i.1)) +
        (1 - compressionEigenvalue X E hE i.1) •
          pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inr i)) := by
  rw [pairedProjectionAdaptedBasis_inl_inl,
    pairedProjectionAdaptedBasis_inl_inr]
  ext a
  exact secondProjection_normalizedPairingResidual_apply X E hE i a

theorem secondProjection_mul_adaptedBasis_inr
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    Matrix.toEuclideanLin E
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inr i)) =
      pairedComplementEigenvalue X E hX hE i •
        pairedProjectionAdaptedBasis X E hX hE (Sum.inr i) := by
  rw [pairedProjectionAdaptedBasis_inr]
  exact congrArg Subtype.val
    (pairedComplementProjection_mul_eigenbasis X E hX hE i)

abbrev pairedProjectionAdaptedIndex
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :=
  (Fin r ⊕ interiorCompressionIndex X E hE) ⊕
    Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))

noncomputable def pairedProjectionAdaptedIndexEquiv
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    pairedProjectionAdaptedIndex X E hE ≃ α := by
  apply Fintype.equivOfCardEq
  calc
    Fintype.card (pairedProjectionAdaptedIndex X E hE) =
        Module.finrank ℝ (EuclideanSpace ℝ α) :=
      (Module.finrank_eq_card_basis
        (pairedProjectionAdaptedBasis X E hX hE).toBasis).symm
    _ = Fintype.card α := by simp

noncomputable def pairedProjectionAmbientBasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    OrthonormalBasis α ℝ (EuclideanSpace ℝ α) :=
  (pairedProjectionAdaptedBasis X E hX hE).reindex
    (pairedProjectionAdaptedIndexEquiv X E hX hE)

noncomputable def twoProjectionChangeOfBasis
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] : Matrix α α ℝ :=
  (EuclideanSpace.basisFun α ℝ).toBasis.toMatrix
    (pairedProjectionAmbientBasis X E hX hE)

theorem twoProjectionChangeOfBasis_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (a i : α) :
    twoProjectionChangeOfBasis X E hX hE a i =
      pairedProjectionAmbientBasis X E hX hE i a := by
  rfl

theorem twoProjectionChangeOfBasis_orthogonal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    (twoProjectionChangeOfBasis X E hX hE).transpose *
          twoProjectionChangeOfBasis X E hX hE = 1 ∧
      twoProjectionChangeOfBasis X E hX hE *
          (twoProjectionChangeOfBasis X E hX hE).transpose = 1 := by
  constructor
  · simpa only [twoProjectionChangeOfBasis,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (EuclideanSpace.basisFun α ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self
        (pairedProjectionAmbientBasis X E hX hE)
  · simpa only [twoProjectionChangeOfBasis,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (EuclideanSpace.basisFun α ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose
        (pairedProjectionAmbientBasis X E hX hE)

def pairedProjectionAdaptedBlock
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E) :
    pairedProjectionAdaptedIndex X E hE →
      pairedProjectionAdaptedIndex X E hE
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
  | Sum.inl (Sum.inr i) => Sum.inl (Sum.inl i.1)
  | Sum.inr i => Sum.inr i

theorem pairedProjectionAdaptedBlock_fiber_card_le_two
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE) :
    ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
      (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
        pairedProjectionAdaptedBlock X E hE i)).card ≤ 2 := by
  classical
  rcases i with (i | i)
  · rcases i with i | i
    · by_cases hi : 0 < compressionEigenvalue X E hE i ∧
          compressionEigenvalue X E hE i < 1
      · let ii : interiorCompressionIndex X E hE := ⟨i, hi⟩
        calc
          ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
              (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
                pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inl i)))).card ≤
              ({Sum.inl (Sum.inl i), Sum.inl (Sum.inr ii)} :
                Finset (pairedProjectionAdaptedIndex X E hE)).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rcases j with (j | j)
            · rcases j with j | j
              · simpa [pairedProjectionAdaptedBlock] using hj
              · have hji : j.1 = i := by
                  simpa [pairedProjectionAdaptedBlock] using hj
                have hjii : j = ii := Subtype.ext hji
                subst j
                simp
            · simp [pairedProjectionAdaptedBlock] at hj
          _ ≤ 2 := Finset.card_le_two
      · calc
          ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
              (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
                pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inl i)))).card ≤
              ({Sum.inl (Sum.inl i)} :
                Finset (pairedProjectionAdaptedIndex X E hE)).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rcases j with (j | j)
            · rcases j with j | j
              · simpa [pairedProjectionAdaptedBlock] using hj
              · have hji : j.1 = i := by
                  simpa [pairedProjectionAdaptedBlock] using hj
                exfalso
                apply hi
                simpa [hji] using j.2
            · simp [pairedProjectionAdaptedBlock] at hj
          _ ≤ 2 := by simp
    · let yi : pairedProjectionAdaptedIndex X E hE := Sum.inl (Sum.inl i.1)
      calc
        ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
            (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
              pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inr i)))).card ≤
            ({yi, Sum.inl (Sum.inr i)} :
              Finset (pairedProjectionAdaptedIndex X E hE)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rcases j with (j | j)
          · rcases j with j | j
            · have hji : j = i.1 := by
                simpa [pairedProjectionAdaptedBlock] using hj
              subst j
              simp [yi]
            · have hji : j.1 = i.1 := by
                simpa [pairedProjectionAdaptedBlock] using hj
              have hjeq : j = i := Subtype.ext hji
              subst j
              simp
          · simp [pairedProjectionAdaptedBlock] at hj
        _ ≤ 2 := Finset.card_le_two
  · calc
      ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE (Sum.inr i))).card ≤
          ({Sum.inr i} : Finset (pairedProjectionAdaptedIndex X E hE)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rcases j with (j | j)
        · rcases j with j | j <;> simp [pairedProjectionAdaptedBlock] at hj
        · simpa [pairedProjectionAdaptedBlock] using hj
      _ ≤ 2 := by simp

theorem pairedProjectionAdaptedBlock_y_fiber_card
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (i : Fin r) :
    ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
      (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
        pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inl i)))).card =
      if 0 < compressionEigenvalue X E hE i ∧
          compressionEigenvalue X E hE i < 1 then 2 else 1 := by
  classical
  by_cases hi : 0 < compressionEigenvalue X E hE i ∧
      compressionEigenvalue X E hE i < 1
  · let ii : interiorCompressionIndex X E hE := ⟨i, hi⟩
    have hfiber :
        (Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inl i))) =
          {Sum.inl (Sum.inl i), Sum.inl (Sum.inr ii)} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      rcases j with (j | j)
      · rcases j with j | j
        · simp [pairedProjectionAdaptedBlock]
        · constructor
          · intro hji
            right
            apply congrArg Sum.inl
            apply congrArg Sum.inr
            apply Subtype.ext
            simpa [pairedProjectionAdaptedBlock] using hji
          · rintro (hbad | hji)
            · simp at hbad
            · have : j = ii := by simpa using Sum.inl.inj hji
              subst j
              simp [ii, pairedProjectionAdaptedBlock]
      · simp [pairedProjectionAdaptedBlock]
    rw [hfiber, if_pos hi]
    simp
  · have hfiber :
        (Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inl i))) =
          {Sum.inl (Sum.inl i)} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rcases j with (j | j)
      · rcases j with j | j
        · simp [pairedProjectionAdaptedBlock]
        · constructor
          · intro hji
            have hv : j.1 = i := by
              simpa [pairedProjectionAdaptedBlock] using hji
            exfalso
            apply hi
            simpa [hv] using j.2
          · simp
      · simp [pairedProjectionAdaptedBlock]
    rw [hfiber, if_neg hi]
    simp

theorem pairedProjectionAdaptedBlock_z_fiber_card
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : interiorCompressionIndex X E hE) :
    ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
      (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
        pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inr i)))).card = 2 := by
  rw [show pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inr i)) =
      pairedProjectionAdaptedBlock X E hE (Sum.inl (Sum.inl i.1)) by rfl]
  rw [pairedProjectionAdaptedBlock_y_fiber_card]
  simp [i.2.1, i.2.2]

theorem pairedProjectionAdaptedBlock_complement_fiber_card
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
      (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
        pairedProjectionAdaptedBlock X E hE (Sum.inr i))).card = 1 := by
  classical
  have hfiber :
      (Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
        (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
          pairedProjectionAdaptedBlock X E hE (Sum.inr i)) = {Sum.inr i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rcases j with (j | j)
    · rcases j with j | j <;> simp [pairedProjectionAdaptedBlock]
    · simp [pairedProjectionAdaptedBlock]
  rw [hfiber]
  simp

noncomputable def twoProjectionBlock
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] : α → α :=
  fun i ↦ pairedProjectionAdaptedIndexEquiv X E hX hE
    (pairedProjectionAdaptedBlock X E hE
      ((pairedProjectionAdaptedIndexEquiv X E hX hE).symm i))

theorem orthogonalConjugate_twoProjectionChangeOfBasis_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E A : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] (i j : α) :
    orthogonalConjugate (twoProjectionChangeOfBasis X E hX hE) A i j =
      inner ℝ (pairedProjectionAmbientBasis X E hX hE i)
        (Matrix.toEuclideanLin A (pairedProjectionAmbientBasis X E hX hE j)) := by
  let vi : α → ℝ := WithLp.ofLp (pairedProjectionAmbientBasis X E hX hE i)
  let vj : α → ℝ := WithLp.ofLp (pairedProjectionAmbientBasis X E hX hE j)
  simp only [orthogonalConjugate, Matrix.mul_apply, Matrix.transpose_apply,
    twoProjectionChangeOfBasis_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.toLpLin_apply]
  change (∑ x, (∑ y, vi y * A y x) * vj x) =
    ∑ x, (∑ y, A x y * vj y) * vi x
  calc
    (∑ x, (∑ y, vi y * A y x) * vj x) =
        ∑ x, ∑ y, (vi y * A y x) * vj x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ y, ∑ x, (vi y * A y x) * vj x := Finset.sum_comm
    _ = ∑ x, (∑ y, A x y * vj y) * vi x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem pairedProjectionAmbientBasis_equiv_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE) :
    pairedProjectionAmbientBasis X E hX hE
        (pairedProjectionAdaptedIndexEquiv X E hX hE i) =
      pairedProjectionAdaptedBasis X E hX hE i := by
  simp [pairedProjectionAmbientBasis]

theorem pairedProjectionAdaptedBasis_inner
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i j : pairedProjectionAdaptedIndex X E hE) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (pairedProjectionAdaptedBasis X E hX hE j) =
      if i = j then 1 else 0 := by
  have h := (pairedProjectionAdaptedBasis X E hX hE).orthonormal
  rw [orthonormal_iff_ite] at h
  exact h i j

theorem twoProjectionBlock_equiv_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE) :
    twoProjectionBlock X E hX hE
        (pairedProjectionAdaptedIndexEquiv X E hX hE i) =
      pairedProjectionAdaptedIndexEquiv X E hX hE
        (pairedProjectionAdaptedBlock X E hE i) := by
  simp [twoProjectionBlock]

theorem orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E A : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i j : pairedProjectionAdaptedIndex X E hE) :
    orthogonalConjugate (twoProjectionChangeOfBasis X E hX hE) A
        (pairedProjectionAdaptedIndexEquiv X E hX hE i)
        (pairedProjectionAdaptedIndexEquiv X E hX hE j) =
      inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin A
          (pairedProjectionAdaptedBasis X E hX hE j)) := by
  rw [orthogonalConjugate_twoProjectionChangeOfBasis_apply]
  simp only [pairedProjectionAmbientBasis_equiv_apply]

theorem pairedProjectionAdapted_frameProjection_entry_y
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE) (j : Fin r) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin (frameProjection X)
          (pairedProjectionAdaptedBasis X E hX hE
            (Sum.inl (Sum.inl j)))) =
      if i = Sum.inl (Sum.inl j) then 1 else 0 := by
  rw [frameProjection_mul_adaptedBasis_inl_inl]
  exact pairedProjectionAdaptedBasis_inner X E hX hE i _

theorem pairedProjectionAdapted_frameProjection_entry_z
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (j : interiorCompressionIndex X E hE) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin (frameProjection X)
          (pairedProjectionAdaptedBasis X E hX hE
            (Sum.inl (Sum.inr j)))) = 0 := by
  rw [frameProjection_mul_adaptedBasis_inl_inr]
  simp

theorem pairedProjectionAdapted_frameProjection_entry_complement
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (j : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin (frameProjection X)
          (pairedProjectionAdaptedBasis X E hX hE (Sum.inr j))) = 0 := by
  rw [frameProjection_mul_adaptedBasis_inr]
  simp

theorem pairedProjectionAdapted_secondProjection_entry_y_interior
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (j : interiorCompressionIndex X E hE) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin E
          (pairedProjectionAdaptedBasis X E hX hE
            (Sum.inl (Sum.inl j.1)))) =
      compressionEigenvalue X E hE j.1 *
          (if i = Sum.inl (Sum.inl j.1) then 1 else 0) +
        Real.sqrt (compressionEigenvalue X E hE j.1 *
          (1 - compressionEigenvalue X E hE j.1)) *
          (if i = Sum.inl (Sum.inr j) then 1 else 0) := by
  rw [secondProjection_mul_adaptedBasis_inl_inl_interior]
  simp only [inner_add_right, inner_smul_right, real_inner_comm]
  rw [pairedProjectionAdaptedBasis_inner,
    pairedProjectionAdaptedBasis_inner]

theorem pairedProjectionAdapted_secondProjection_entry_y_endpoint
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE) (j : Fin r)
    (hj : compressionEigenvalue X E hE j = 0 ∨
      compressionEigenvalue X E hE j = 1) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin E
          (pairedProjectionAdaptedBasis X E hX hE
            (Sum.inl (Sum.inl j)))) =
      compressionEigenvalue X E hE j *
        (if i = Sum.inl (Sum.inl j) then 1 else 0) := by
  rw [secondProjection_mul_adaptedBasis_inl_inl_endpoint X E hX hE j hj]
  simp only [inner_smul_right, real_inner_comm]
  rw [pairedProjectionAdaptedBasis_inner]

theorem pairedProjectionAdapted_secondProjection_entry_z
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (j : interiorCompressionIndex X E hE) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin E
          (pairedProjectionAdaptedBasis X E hX hE
            (Sum.inl (Sum.inr j)))) =
      Real.sqrt (compressionEigenvalue X E hE j.1 *
          (1 - compressionEigenvalue X E hE j.1)) *
          (if i = Sum.inl (Sum.inl j.1) then 1 else 0) +
        (1 - compressionEigenvalue X E hE j.1) *
          (if i = Sum.inl (Sum.inr j) then 1 else 0) := by
  rw [secondProjection_mul_adaptedBasis_inl_inr]
  simp only [inner_add_right, inner_smul_right, real_inner_comm]
  rw [pairedProjectionAdaptedBasis_inner,
    pairedProjectionAdaptedBasis_inner]

theorem pairedProjectionAdapted_secondProjection_entry_complement
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (j : Fin (Module.finrank ℝ (pairedProjectionComplement X E hE))) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin E
          (pairedProjectionAdaptedBasis X E hX hE (Sum.inr j))) =
      pairedComplementEigenvalue X E hX hE j *
        (if i = Sum.inr j then 1 else 0) := by
  rw [secondProjection_mul_adaptedBasis_inr]
  simp only [inner_smul_right, real_inner_comm]
  rw [pairedProjectionAdaptedBasis_inner]

theorem pairedProjectionAdapted_frameProjection_off_block
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i j : pairedProjectionAdaptedIndex X E hE)
    (hij : pairedProjectionAdaptedBlock X E hE i ≠
      pairedProjectionAdaptedBlock X E hE j) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin (frameProjection X)
          (pairedProjectionAdaptedBasis X E hX hE j)) = 0 := by
  rcases j with (j | j)
  · rcases j with j | j
    · rw [pairedProjectionAdapted_frameProjection_entry_y]
      have hiy : i ≠ Sum.inl (Sum.inl j) := by
        intro hEq
        apply hij
        subst i
        rfl
      simp [hiy]
    · exact pairedProjectionAdapted_frameProjection_entry_z X E hX hE i j
  · exact pairedProjectionAdapted_frameProjection_entry_complement X E hX hE i j

theorem pairedProjectionAdapted_secondProjection_off_block
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i j : pairedProjectionAdaptedIndex X E hE)
    (hij : pairedProjectionAdaptedBlock X E hE i ≠
      pairedProjectionAdaptedBlock X E hE j) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin E
          (pairedProjectionAdaptedBasis X E hX hE j)) = 0 := by
  rcases j with (j | j)
  · rcases j with j | j
    · by_cases hj : 0 < compressionEigenvalue X E hE j ∧
          compressionEigenvalue X E hE j < 1
      · let jj : interiorCompressionIndex X E hE := ⟨j, hj⟩
        rw [show j = jj.1 by rfl,
          pairedProjectionAdapted_secondProjection_entry_y_interior]
        have hiy : i ≠ Sum.inl (Sum.inl jj.1) := by
          intro hi
          apply hij
          subst i
          rfl
        have hiz : i ≠ Sum.inl (Sum.inr jj) := by
          intro hi
          apply hij
          subst i
          rfl
        simp [hiy, hiz]
      · have hend := compressionEigenvalue_endpoint_of_not_interior
          X E hX hE j hj
        rw [pairedProjectionAdapted_secondProjection_entry_y_endpoint
          X E hX hE i j hend]
        have hiy : i ≠ Sum.inl (Sum.inl j) := by
          intro hi
          apply hij
          subst i
          rfl
        simp [hiy]
    · rw [pairedProjectionAdapted_secondProjection_entry_z]
      have hiy : i ≠ Sum.inl (Sum.inl j.1) := by
        intro hi
        apply hij
        subst i
        rfl
      have hiz : i ≠ Sum.inl (Sum.inr j) := by
        intro hi
        apply hij
        subst i
        rfl
      simp [hiy, hiz]
  · rw [pairedProjectionAdapted_secondProjection_entry_complement]
    have hic : i ≠ Sum.inr j := by
      intro hi
      apply hij
      subst i
      rfl
    simp [hic]

theorem twoProjectionBlock_fiber_card_equiv
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE) :
    ((Finset.univ : Finset α).filter (fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE
            (pairedProjectionAdaptedIndexEquiv X E hX hE i))).card =
      ((Finset.univ : Finset (pairedProjectionAdaptedIndex X E hE)).filter
        (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
          pairedProjectionAdaptedBlock X E hE i)).card := by
  classical
  let e := pairedProjectionAdaptedIndexEquiv X E hX hE
  let S := (Finset.univ :
    Finset (pairedProjectionAdaptedIndex X E hE)).filter
      (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
        pairedProjectionAdaptedBlock X E hE i)
  let T := (Finset.univ : Finset α).filter (fun j ↦
    twoProjectionBlock X E hX hE j =
      twoProjectionBlock X E hX hE (e i))
  have hmap : S.map e.toEmbedding = T := by
    ext j
    simp [S, T, e, twoProjectionBlock]
  change T.card = S.card
  rw [← hmap, Finset.card_map]

theorem pairedProjectionAdapted_singleton_diagonal
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (hi : ((Finset.univ :
      Finset (pairedProjectionAdaptedIndex X E hE)).filter
        (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
          pairedProjectionAdaptedBlock X E hE i)).card = 1) :
    inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin (frameProjection X)
          (pairedProjectionAdaptedBasis X E hX hE i)) ∈
        ({0, 1} : Set ℝ) ∧
      inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
        (Matrix.toEuclideanLin E
          (pairedProjectionAdaptedBasis X E hX hE i)) ∈
        ({0, 1} : Set ℝ) := by
  rcases i with (i | i)
  · rcases i with i | i
    · have hcard := pairedProjectionAdaptedBlock_y_fiber_card X E hE i
      by_cases hint : 0 < compressionEigenvalue X E hE i ∧
          compressionEigenvalue X E hE i < 1
      · rw [if_pos hint] at hcard
        omega
      · have hend := compressionEigenvalue_endpoint_of_not_interior
          X E hX hE i hint
        constructor
        · rw [pairedProjectionAdapted_frameProjection_entry_y]
          simp
        · rw [pairedProjectionAdapted_secondProjection_entry_y_endpoint
            X E hX hE (Sum.inl (Sum.inl i)) i hend]
          simpa using hend
    · have hcard := pairedProjectionAdaptedBlock_z_fiber_card X E hE i
      omega
  · constructor
    · rw [pairedProjectionAdapted_frameProjection_entry_complement]
      simp
    · rw [pairedProjectionAdapted_secondProjection_entry_complement]
      simpa using pairedComplementEigenvalue_endpoint X E hX hE i

theorem pairedProjectionAdapted_two_block
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)]
    (i : pairedProjectionAdaptedIndex X E hE)
    (hi : ((Finset.univ :
      Finset (pairedProjectionAdaptedIndex X E hE)).filter
        (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
          pairedProjectionAdaptedBlock X E hE i)).card = 2) :
    ∃ j, j ≠ i ∧
      pairedProjectionAdaptedBlock X E hE j =
        pairedProjectionAdaptedBlock X E hE i ∧
      ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
        inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
          (Matrix.toEuclideanLin (frameProjection X)
            (pairedProjectionAdaptedBasis X E hX hE j)) = 0 ∧
        inner ℝ (pairedProjectionAdaptedBasis X E hX hE j)
          (Matrix.toEuclideanLin (frameProjection X)
            (pairedProjectionAdaptedBasis X E hX hE i)) = 0 ∧
        inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
          (Matrix.toEuclideanLin E
            (pairedProjectionAdaptedBasis X E hX hE j)) =
              Real.sqrt (lam * (1 - lam)) ∧
        inner ℝ (pairedProjectionAdaptedBasis X E hX hE j)
          (Matrix.toEuclideanLin E
            (pairedProjectionAdaptedBasis X E hX hE i)) =
              Real.sqrt (lam * (1 - lam)) ∧
        ((inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
              (Matrix.toEuclideanLin (frameProjection X)
                (pairedProjectionAdaptedBasis X E hX hE i)) = 1 ∧
            inner ℝ (pairedProjectionAdaptedBasis X E hX hE j)
              (Matrix.toEuclideanLin (frameProjection X)
                (pairedProjectionAdaptedBasis X E hX hE j)) = 0 ∧
            inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
              (Matrix.toEuclideanLin E
                (pairedProjectionAdaptedBasis X E hX hE i)) = lam ∧
            inner ℝ (pairedProjectionAdaptedBasis X E hX hE j)
              (Matrix.toEuclideanLin E
                (pairedProjectionAdaptedBasis X E hX hE j)) = 1 - lam) ∨
          (inner ℝ (pairedProjectionAdaptedBasis X E hX hE j)
              (Matrix.toEuclideanLin (frameProjection X)
                (pairedProjectionAdaptedBasis X E hX hE j)) = 1 ∧
            inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
              (Matrix.toEuclideanLin (frameProjection X)
                (pairedProjectionAdaptedBasis X E hX hE i)) = 0 ∧
            inner ℝ (pairedProjectionAdaptedBasis X E hX hE j)
              (Matrix.toEuclideanLin E
                (pairedProjectionAdaptedBasis X E hX hE j)) = lam ∧
            inner ℝ (pairedProjectionAdaptedBasis X E hX hE i)
              (Matrix.toEuclideanLin E
                (pairedProjectionAdaptedBasis X E hX hE i)) = 1 - lam)) := by
  rcases i with (i | i)
  · rcases i with i | i
    · have hint : 0 < compressionEigenvalue X E hE i ∧
          compressionEigenvalue X E hE i < 1 := by
        by_contra hn
        have hcard := pairedProjectionAdaptedBlock_y_fiber_card X E hE i
        rw [if_neg hn] at hcard
        omega
      let ii : interiorCompressionIndex X E hE := ⟨i, hint⟩
      refine ⟨Sum.inl (Sum.inr ii), by simp, rfl,
        compressionEigenvalue X E hE i, hint.1, hint.2, ?_, ?_, ?_, ?_, Or.inl ?_⟩
      · exact pairedProjectionAdapted_frameProjection_entry_z X E hX hE _ ii
      · rw [pairedProjectionAdapted_frameProjection_entry_y]
        simp
      · rw [pairedProjectionAdapted_secondProjection_entry_z]
        simp [ii]
      · rw [show i = ii.1 by rfl,
          pairedProjectionAdapted_secondProjection_entry_y_interior]
        simp
      · constructor
        · rw [pairedProjectionAdapted_frameProjection_entry_y]
          simp
        · constructor
          · exact pairedProjectionAdapted_frameProjection_entry_z X E hX hE _ ii
          · constructor
            · rw [show i = ii.1 by rfl,
                pairedProjectionAdapted_secondProjection_entry_y_interior]
              simp
            · rw [pairedProjectionAdapted_secondProjection_entry_z]
              simp [ii]
    · refine ⟨Sum.inl (Sum.inl i.1), by simp,
        rfl, compressionEigenvalue X E hE i.1, i.2.1, i.2.2,
        ?_, ?_, ?_, ?_, Or.inr ?_⟩
      · rw [pairedProjectionAdapted_frameProjection_entry_y]
        simp
      · exact pairedProjectionAdapted_frameProjection_entry_z X E hX hE _ i
      · rw [pairedProjectionAdapted_secondProjection_entry_y_interior
          X E hX hE (Sum.inl (Sum.inr i)) i]
        simp
      · rw [pairedProjectionAdapted_secondProjection_entry_z]
        simp
      · constructor
        · rw [pairedProjectionAdapted_frameProjection_entry_y]
          simp
        · constructor
          · exact pairedProjectionAdapted_frameProjection_entry_z X E hX hE _ i
          · constructor
            · rw [pairedProjectionAdapted_secondProjection_entry_y_interior
                X E hX hE (Sum.inl (Sum.inl i.1)) i]
              simp
            · rw [pairedProjectionAdapted_secondProjection_entry_z]
              simp
  · have hcard := pairedProjectionAdaptedBlock_complement_fiber_card X E hE i
    omega

theorem twoProjectionBlock_isTwoProjectionBlockDecomposition
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    IsTwoProjectionBlockDecomposition (X * X.transpose) E
      (twoProjectionChangeOfBasis X E hX hE)
      (twoProjectionBlock X E hX hE) := by
  classical
  let e := pairedProjectionAdaptedIndexEquiv X E hX hE
  have hQ := twoProjectionChangeOfBasis_orthogonal X E hX hE
  refine ⟨hQ.1, hQ.2, ?_, ?_, ?_, ?_⟩
  · intro i
    let ii := e.symm i
    have hcard := pairedProjectionAdaptedBlock_fiber_card_le_two X E hE ii
    have htransport := twoProjectionBlock_fiber_card_equiv X E hX hE ii
    have hii : pairedProjectionAdaptedIndexEquiv X E hX hE ii = i := by
      simp [ii, e]
    rw [← hii, htransport]
    exact hcard
  · intro i j hij
    let ii := e.symm i
    let jj := e.symm j
    have hab : pairedProjectionAdaptedBlock X E hE ii ≠
        pairedProjectionAdaptedBlock X E hE jj := by
      intro hab
      apply hij
      have heq := congrArg e hab
      simpa [e, ii, jj, twoProjectionBlock] using heq
    constructor
    · rw [show i = e ii by simp [ii], show j = e jj by simp [jj]]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      simpa only [frameProjection] using
        pairedProjectionAdapted_frameProjection_off_block X E hX hE ii jj hab
    · rw [show i = e ii by simp [ii], show j = e jj by simp [jj]]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      exact pairedProjectionAdapted_secondProjection_off_block X E hX hE ii jj hab
  · intro i hi
    let ii := e.symm i
    have htransport := twoProjectionBlock_fiber_card_equiv X E hX hE ii
    have hii : e ii = i := by simp [ii]
    have hi' : ((Finset.univ :
        Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE ii)).card = 1 := by
      rw [← htransport]
      simpa [e, ii] using hi
    have hadapt := pairedProjectionAdapted_singleton_diagonal X E hX hE ii hi'
    constructor
    · rw [show i = e ii by exact hii.symm]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      simpa only [frameProjection] using hadapt.1
    · rw [show i = e ii by exact hii.symm]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      exact hadapt.2
  · intro i hi
    let ii := e.symm i
    have htransport := twoProjectionBlock_fiber_card_equiv X E hX hE ii
    have hii : e ii = i := by simp [ii]
    have hi' : ((Finset.univ :
        Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE ii)).card = 2 := by
      rw [← htransport]
      simpa [e, ii] using hi
    obtain ⟨jj, hjjne, hblock, lam, hlam0, hlam1,
      hPij, hPji, hEij, hEji, hdiag⟩ :=
        pairedProjectionAdapted_two_block X E hX hE ii hi'
    refine ⟨e jj, ?_, ?_, lam, hlam0, hlam1, ?_, ?_, ?_, ?_, ?_⟩
    · intro hji
      apply hjjne
      apply e.injective
      simpa [hii] using hji
    · rw [twoProjectionBlock_equiv_apply, show i = e ii by exact hii.symm,
        twoProjectionBlock_equiv_apply, hblock]
    · rw [show i = e ii by exact hii.symm,
        orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      simpa only [frameProjection] using hPij
    · rw [show i = e ii by exact hii.symm,
        orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      simpa only [frameProjection] using hPji
    · rw [show i = e ii by exact hii.symm,
        orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      exact hEij
    · rw [show i = e ii by exact hii.symm,
        orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      exact hEji
    · rcases hdiag with hdiag | hdiag
      · left
        rcases hdiag with ⟨hPii, hPjj, hEii, hEjj⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [show i = e ii by exact hii.symm,
            orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          simpa only [frameProjection] using hPii
        · rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          simpa only [frameProjection] using hPjj
        · rw [show i = e ii by exact hii.symm,
            orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          exact hEii
        · rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          exact hEjj
      · right
        rcases hdiag with ⟨hPjj, hPii, hEjj, hEii⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          simpa only [frameProjection] using hPjj
        · rw [show i = e ii by exact hii.symm,
            orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          simpa only [frameProjection] using hPii
        · rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          exact hEjj
        · rw [show i = e ii by exact hii.symm,
            orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
          exact hEii

theorem pairedProjectionAdapted_two_block_index_card_le_twice_rank
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    ((Finset.univ :
      Finset (pairedProjectionAdaptedIndex X E hE)).filter (fun i ↦
        ((Finset.univ :
          Finset (pairedProjectionAdaptedIndex X E hE)).filter
            (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
              pairedProjectionAdaptedBlock X E hE i)).card = 2)).card ≤
      2 * r := by
  classical
  let S := (Finset.univ :
    Finset (pairedProjectionAdaptedIndex X E hE)).filter (fun i ↦
      ((Finset.univ :
        Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE i)).card = 2)
  have hno (k : Fin (Module.finrank ℝ
      (pairedProjectionComplement X E hE))) :
      (Sum.inr k : pairedProjectionAdaptedIndex X E hE) ∉ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    intro htwo
    have hone := pairedProjectionAdaptedBlock_complement_fiber_card X E hE k
    omega
  let f : S → Fin r ⊕ Fin r := fun x ↦ by
    rcases x with ⟨x, hx⟩
    rcases x with (x | x)
    · rcases x with x | x
      · exact Sum.inl x
      · exact Sum.inr x.1
    · exact (hno x hx).elim
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases a with (a | a)
    · rcases a with a | a
      · rcases b with (b | b)
        · rcases b with b | b
          · simpa [f] using hab
          · simp [f] at hab
        · exact (hno b hb).elim
      · rcases b with (b | b)
        · rcases b with b | b
          · simp [f] at hab
          · apply congrArg Sum.inl
            apply congrArg Sum.inr
            apply Subtype.ext
            simpa [f] using hab
        · exact (hno b hb).elim
    · exact (hno a ha).elim
  have hcard : Fintype.card S ≤ Fintype.card (Fin r ⊕ Fin r) :=
    Fintype.card_le_of_injective f hf
  change S.card ≤ 2 * r
  simpa [Nat.two_mul] using hcard

theorem twoProjectionBlock_two_block_index_card_equiv
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    ((Finset.univ : Finset α).filter (fun i ↦
        ((Finset.univ : Finset α).filter fun j ↦
          twoProjectionBlock X E hX hE j =
            twoProjectionBlock X E hX hE i).card = 2)).card =
      ((Finset.univ :
        Finset (pairedProjectionAdaptedIndex X E hE)).filter (fun i ↦
          ((Finset.univ :
            Finset (pairedProjectionAdaptedIndex X E hE)).filter
              (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
                pairedProjectionAdaptedBlock X E hE i)).card = 2)).card := by
  classical
  let e := pairedProjectionAdaptedIndexEquiv X E hX hE
  let S := (Finset.univ :
    Finset (pairedProjectionAdaptedIndex X E hE)).filter (fun i ↦
      ((Finset.univ :
        Finset (pairedProjectionAdaptedIndex X E hE)).filter
          (fun j ↦ pairedProjectionAdaptedBlock X E hE j =
            pairedProjectionAdaptedBlock X E hE i)).card = 2)
  let T := (Finset.univ : Finset α).filter (fun i ↦
    ((Finset.univ : Finset α).filter fun j ↦
      twoProjectionBlock X E hX hE j =
        twoProjectionBlock X E hX hE i).card = 2)
  have hmap : S.map e.toEmbedding = T := by
    ext j
    constructor
    · intro hj
      simp only [Finset.mem_map] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      change ((Finset.univ : Finset α).filter (fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE
            (pairedProjectionAdaptedIndexEquiv X E hX hE i))).card = 2
      rw [twoProjectionBlock_fiber_card_equiv]
      exact hi
    · intro hj
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      apply Finset.mem_map.mpr
      refine ⟨e.symm j, ?_, by simp⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← twoProjectionBlock_fiber_card_equiv X E hX hE (e.symm j)]
      simpa [e] using hj
  change T.card = S.card
  rw [← hmap, Finset.card_map]

theorem twoProjectionBlock_two_block_index_card_div_two_le_rank
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    [Fintype (interiorCompressionIndex X E hE)]
    [DecidableEq (interiorCompressionIndex X E hE)] :
    ((Finset.univ : Finset α).filter (fun i ↦
      ((Finset.univ : Finset α).filter fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE i).card = 2)).card / 2 ≤ r := by
  have htransport := twoProjectionBlock_two_block_index_card_equiv X E hX hE
  have hadapt := pairedProjectionAdapted_two_block_index_card_le_twice_rank
    X E hX hE
  have hle : ((Finset.univ : Finset α).filter (fun i ↦
      ((Finset.univ : Finset α).filter fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE i).card = 2)).card ≤ 2 * r := by
    rw [htransport]
    exact hadapt
  omega

theorem twoProjectionBlockDecomposition_exists
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    ∃ (Q : Matrix α α ℝ) (block : α → α),
      IsTwoProjectionBlockDecomposition (X * X.transpose) E Q block ∧
      ((Finset.univ : Finset α).filter (fun i ↦
        ((Finset.univ : Finset α).filter fun j ↦ block j = block i).card = 2)).card /
          2 ≤ r := by
  classical
  letI : Finite (interiorCompressionIndex X E hE) :=
    Finite.of_injective (fun i : interiorCompressionIndex X E hE ↦ i.1)
      Subtype.val_injective
  letI : Fintype (interiorCompressionIndex X E hE) := Fintype.ofFinite _
  letI : DecidableEq (interiorCompressionIndex X E hE) := Classical.decEq _
  exact ⟨twoProjectionChangeOfBasis X E hX hE,
    twoProjectionBlock X E hX hE,
    twoProjectionBlock_isTwoProjectionBlockDecomposition X E hX hE,
    twoProjectionBlock_two_block_index_card_div_two_le_rank X E hX hE⟩

theorem pairedProjectionFamily_exists_orthonormalBasis_extension
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    ∃ (u : Finset (EuclideanSpace ℝ α))
      (b : OrthonormalBasis u ℝ (EuclideanSpace ℝ α)),
      Set.range (pairedProjectionFamily X E hE) ⊆ u ∧
        ⇑b = ((↑) : u → EuclideanSpace ℝ α) := by
  have hv := pairedProjectionFamily_orthonormal X E hX hE
  have hrange : Orthonormal ℝ
      ((↑) : Set.range (pairedProjectionFamily X E hE) →
        EuclideanSpace ℝ α) := hv.toSubtypeRange
  exact hrange.exists_orthonormalBasis_extension

#print axioms frameProjection_isOrthogonalProjection
#print axioms frameCompression_isHermitian
#print axioms compressionEigenbasis_orthogonal
#print axioms compressionEigenbasis_diagonalizes
#print axioms rangeEigenbasis_orthonormal
#print axioms frameProjection_mul_rangeEigenbasis
#print axioms rangeEigenbasis_compresses_E_to_diagonal
#print axioms compressionEigenbasis_intertwines
#print axioms frameProjection_mul_E_mul_rangeEigenbasis
#print axioms frameProjection_annihilates_pairingResidual
#print axioms rangeEigenbasis_orthogonal_to_pairingResidual
#print axioms pairingResidual_gram
#print axioms pairingResidual_inner
#print axioms compressionEigenvalue_mem_unitInterval
#print axioms normalizedPairingResidual_inner
#print axioms secondProjection_mul_pairingResidual
#print axioms secondProjection_mul_rangeEigenbasis
#print axioms secondProjection_rangeEigenbasis_apply
#print axioms secondProjection_pairingResidual_apply
#print axioms twoProjectionBlock_isTwoProjectionBlockDecomposition
#print axioms pairedProjectionAdapted_two_block_index_card_le_twice_rank
#print axioms twoProjectionBlockDecomposition_exists

end Problem56
