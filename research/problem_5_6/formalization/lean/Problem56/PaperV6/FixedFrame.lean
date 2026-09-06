import Problem56.Statements
import Problem56.PaperV6.FixedFrameExpected

open scoped BigOperators Matrix

namespace Problem56.PaperV6

/-- Finite uniform probabilities, including an empty sample type, lie in [0,1]. -/
theorem uniformProbability_bounds {Ω : Type*} [Fintype Ω] (E : Ω → Prop) :
    0 ≤ uniformProbability E ∧ uniformProbability E ≤ 1 := by
  classical
  unfold uniformProbability
  constructor
  · positivity
  · by_cases h : Fintype.card Ω = 0
    · simp [h]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).2
      exact_mod_cast Finset.card_filter_le Finset.univ E

/-- A bounded supremum dominates the probability for each particular frame. -/
theorem frameFailureProbability_le_sup {m r k : ℕ} (ε : ℝ)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V) :
    frameFailureProbability (k := k) ε V ≤ spectralFailureSup m r k ε := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro z ⟨W, _, rfl⟩
    exact (uniformProbability_bounds _).2
  · exact ⟨V, hV, rfl⟩

theorem fixed_frame_ose : FixedFrameOSE := by
  obtain ⟨C, hCeq, hC, H⟩ := main_universal_ose
  refine ⟨C, hCeq, hC, ?_⟩
  intro m r ε hr hrn hε hε1
  obtain ⟨k, hrk, hkn, hku, hsup⟩ := H m r ε hr hrn hε hε1
  exact ⟨k, hrk, hkn, hku, fun V hV ↦
    (frameFailureProbability_le_sup ε V hV).trans hsup⟩

/-- The custom L2 norm and a rectangular Gram quadratic form agree exactly. -/
theorem gram_quadraticForm {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) (x : β → ℝ) :
    quadraticForm (A.transpose * A) x = euclideanNorm (A.mulVec x) ^ 2 := by
  classical
  rw [euclideanNorm_sq_eq_sum]
  unfold quadraticForm euclideanInner
  change x ⬝ᵥ (A.transpose * A).mulVec x = ∑ i, (A.mulVec x i) ^ 2
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  simp [dotProduct, pow_two]

theorem frame_isometry {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (V : Matrix α (Fin r) ℝ) (hV : OrthonormalFrame V) (x : Fin r → ℝ) :
    euclideanNorm (V.mulVec x) ^ 2 = euclideanNorm x ^ 2 := by
  rw [← gram_quadraticForm, hV, quadraticForm_one, euclideanNorm_sq_eq_sum]

theorem compressedGram_quadraticForm {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k)
    (x : Fin r → ℝ) :
    quadraticForm (compressedGram V d₁ d₂ J) x =
      euclideanNorm ((rerandomizedSRHT d₁ d₂ J).transpose.mulVec (V.mulVec x)) ^ 2 := by
  have hgram : compressedGram V d₁ d₂ J =
      ((rerandomizedSRHT d₁ d₂ J).transpose * V).transpose *
      ((rerandomizedSRHT d₁ d₂ J).transpose * V) := by
    simp [compressedGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hgram, gram_quadraticForm, ← Matrix.mulVec_mulVec]

theorem spectral_bound_implies_squared_edges {m r k : ℕ} (ε : ℝ)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k)
    (h : euclideanOperatorNorm (compressedGram V d₁ d₂ J - 1) ≤ ε) :
    SquaredNormEdges ε V d₁ d₂ J := by
  intro x
  have hb := sampling_abs_quadraticForm_le_operatorNorm_mul_sq
    (compressedGram V d₁ d₂ J - 1) x
  have hb' := hb.trans (mul_le_mul_of_nonneg_right h
    (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i))))
  rw [quadraticForm_sub, quadraticForm_one, compressedGram_quadraticForm,
    ← euclideanNorm_sq_eq_sum, ← frame_isometry V hV x] at hb'
  obtain ⟨hl, hu⟩ := abs_le.mp hb'
  constructor <;> nlinarith

theorem compressedGram_isHermitian {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    (compressedGram V d₁ d₂ J).IsHermitian := by
  let A := (rerandomizedSRHT d₁ d₂ J).transpose * V
  have h : compressedGram V d₁ d₂ J = A.transpose * A := by
    simp [A, compressedGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self A

theorem squared_edges_iff_spectral_bound {m r k : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    SquaredNormEdges ε V d₁ d₂ J ↔
      euclideanOperatorNorm (compressedGram V d₁ d₂ J - 1) ≤ ε := by
  constructor
  · intro h
    apply sampling_euclideanOperatorNorm_le_of_quadraticForm_abs_le _
      ((compressedGram_isHermitian V d₁ d₂ J).sub Matrix.isHermitian_one) ε hε
    intro x
    obtain ⟨hl, hu⟩ := h x
    rw [quadraticForm_sub, quadraticForm_one, compressedGram_quadraticForm,
      ← euclideanNorm_sq_eq_sum, ← frame_isometry V hV x]
    apply abs_le.mpr
    constructor <;> nlinarith
  · exact spectral_bound_implies_squared_edges ε V hV d₁ d₂ J

theorem fixedSubset_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (hk : k ≤ Fintype.card α) : Nonempty (FixedSubset α k) := by
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hk
  exact ⟨s, hs⟩

theorem uniformProbability_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProbability (fun _ : Ω ↦ True) = 1 := by
  classical
  simp [uniformProbability, Fintype.card_ne_zero]

theorem uniformProbability_complement {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProbability (fun ω ↦ ¬ E ω) = 1 - uniformProbability E := by
  classical
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformProbability, Finset.natCast_card_filter]
  have hs : (∑ ω : Ω, if ¬ E ω then (1 : ℝ) else 0) +
      (∑ ω : Ω, if E ω then (1 : ℝ) else 0) = Fintype.card Ω := by
    rw [← Finset.sum_add_distrib]
    have he : (∑ ω : Ω, ((if ¬ E ω then (1 : ℝ) else 0) +
        (if E ω then (1 : ℝ) else 0))) = ∑ _ : Ω, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : E ω <;> simp [h]
    rw [he]
    simp
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div]
  convert (congrArg (fun z : ℝ ↦ z / (Fintype.card Ω : ℝ)) hs).trans (div_self hn) using 1
  all_goals congr 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro ω _ <;>
    by_cases h : E ω <;> simp [h]


theorem fixed_frame_squared_norm_success :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
          k ≤ Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
          ∀ V : Matrix (WalshIndex m) (Fin r) ℝ, OrthonormalFrame V →
            99 / 100 ≤ uniformProbability
              (fun ω : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
                  FixedSubset (WalshIndex m) k ↦
                SquaredNormEdges ε V ω.1 ω.2.1 ω.2.2) := by
  obtain ⟨C, hCeq, hC, H⟩ := fixed_frame_ose
  refine ⟨C, hCeq, hC, ?_⟩
  intro m r ε hr hrn hε hε1
  obtain ⟨k, hrk, hkn, hku, Hk⟩ := H m r ε hr hrn hε hε1
  refine ⟨k, hrk, hkn, hku, ?_⟩
  intro V hV
  letI := fixedSubset_nonempty k hkn
  have hevent : (fun ω : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
      FixedSubset (WalshIndex m) k ↦ SquaredNormEdges ε V ω.1 ω.2.1 ω.2.2) =
      (fun ω ↦ ¬ euclideanOperatorNorm (compressedGram V ω.1 ω.2.1 ω.2.2 - 1) > ε) := by
    funext ω
    apply propext
    rw [squared_edges_iff_spectral_bound ε hε.le V hV, not_lt]
  rw [hevent, uniformProbability_complement]
  have hb := Hk V hV
  change frameFailureProbability (k := k) ε V ≤ 1 / 100 at hb
  unfold frameFailureProbability at hb
  linarith

end Problem56.PaperV6
