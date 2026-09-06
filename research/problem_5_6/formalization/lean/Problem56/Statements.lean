import Problem56.ProbabilityFrobenius
import Problem56.SpectralRoot
import Problem56.GraphEven
import Problem56.GraphRankEdgeSplit
import Problem56.GraphWeightLoops
import Problem56.GraphVertexSplit
import Problem56.GraphFiberSplit
import Problem56.GraphBridgelessConversion
import Problem56.RankCutStateFactorGeneral
import Problem56.EqualityBudget
import Problem56.LargeRankCutoff
import Problem56.SelectorQuotient
import Problem56.WalshSymmetry
import Problem56.XorKernel
import Problem56.PointwiseVanishing
import Problem56.TraceGeometric
import Problem56.EncodingCount
import Problem56.TwoProjection
import Problem56.SamplingArithmetic
import Problem56.CumulantMoment
import Problem56.ProjectionMean
import Problem56.BinomialTail
import Problem56.TwoProjectionTransfer
import Problem56.ProductCumulant
import Problem56.RademacherCumulant
import Problem56.RademacherFourthMoment
import Problem56.MixedCumulant
import Problem56.FinalWidth
import Problem56.OccurrenceGraph
import Problem56.JointEntryCumulant
import Problem56.FinitePopulationMoment
import Problem56.LargeBlockCount
import Problem56.DisjointPairCount
import Problem56.SmallRankSecondMoment
import Problem56.NestedCoupling
import Problem56.ThreeCategoryOrderCoupling
import Problem56.PairingParallelBound
import Problem56.EqualityDegreeFour
import Problem56.FixedSizeSamplingTransfer
import Problem56.LargeBlockSupportRank
import Problem56.BernoulliSamplingCorollary
import Problem56.AggregatePartitionCumulant
import Problem56.SignedTraceExpansion
import Problem56.ContractedCoreEncodingClosure

/-!
Source-bound theorem signatures for `solution.tex`, corrected and independently
re-audited during Gate 3.  All declarations are locally complete and their
transitive axiom closures contain only the allowed foundational axioms.
-/

open scoped BigOperators Matrix

namespace Problem56

private lemma sum_five_permute
    {U X A Y B : Type*} [Fintype U] [Fintype X] [Fintype A]
    [Fintype Y] [Fintype B] (f : U → X → A → Y → B → ℝ) :
    (∑ u, ∑ x, ∑ a, ∑ y, ∑ b, f u x a y b) =
      ∑ a, ∑ b, ∑ x, ∑ y, ∑ u, f u x a y b := by
  classical
  let e : U × (X × (A × (Y × B))) ≃ A × (B × (X × (Y × U))) :=
    { toFun := fun z ↦ (z.2.2.1, (z.2.2.2.2, (z.2.1, (z.2.2.2.1, z.1))))
      invFun := fun z ↦ (z.2.2.2.2, (z.2.2.1, (z.1, (z.2.2.2.1, z.2.1))))
      left_inv := by rintro ⟨u, x, a, y, b⟩; rfl
      right_inv := by rintro ⟨a, b, x, y, u⟩; rfl }
  calc
    _ = ∑ z : U × (X × (A × (Y × B))),
        f z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ z : A × (B × (X × (Y × U))),
        f z.2.2.2.2 z.2.2.1 z.1 z.2.2.2.1 z.2.1 := by
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]

private lemma walshCharacter_comm {m : ℕ} (a b : WalshIndex m) :
    walshCharacter a b = walshCharacter b a := by
  have hdot : walshDot a b = walshDot b a := by
    simp only [walshDot]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  simp only [walshCharacter, hdot]

private lemma sampleMatrix_mul_transpose
    {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (J : FixedSubset α k) :
    sampleMatrix J * (sampleMatrix J).transpose = coordinateProjection J := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [sampleMatrix, coordinateProjection, Matrix.mul_apply]
    calc
      (∑ q ∈ J.1.attach,
          if i = q.1 then if i = q.1 then (1 : ℝ) else 0 else 0) =
          ∑ q ∈ J.1.attach, if i = q.1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hiq : i = q.1 <;> simp [hiq]
      _ = ∑ x ∈ J.1, if i = x then (1 : ℝ) else 0 :=
        by simpa only using
          (Finset.sum_attach J.1 (fun x : α ↦ if i = x then (1 : ℝ) else 0))
      _ = if i ∈ J.1 then 1 else 0 := by simp
  · simp [sampleMatrix, coordinateProjection, Matrix.mul_apply, hij]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hjq : j = q.1
    · by_cases hiq : i = q.1
      · exact (hij (hiq.trans hjq.symm)).elim
      · simp [hjq, hiq]
    · simp [hjq]

private lemma signDiagonal_mul_self
    {α : Type*} [Fintype α] [DecidableEq α] (d : SignLayer α) :
    signDiagonal d * signDiagonal d = (1 : Matrix α α ℝ) := by
  simp only [signDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hdi : d i = true <;> simp [signValue, hdi]

private lemma zmod2_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

private lemma walshCharacter_add_right {m : ℕ}
    (c x y : WalshIndex m) :
    walshCharacter c (x + y) = walshCharacter c x * walshCharacter c y := by
  have hdot : walshDot c (x + y) = walshDot c x + walshDot c y := by
    simp [walshDot, mul_add, Finset.sum_add_distrib]
  rw [walshCharacter, walshCharacter, walshCharacter, hdot]
  by_cases hx : walshDot c x = 0
  · simp [hx]
  · have hx1 := zmod2_eq_one_of_ne_zero (walshDot c x) hx
    by_cases hy : walshDot c y = 0
    · simp [hx1, hy]
    · have hy1 := zmod2_eq_one_of_ne_zero (walshDot c y) hy
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [hx1, hy1, h11]

private lemma sum_walshCharacter {m : ℕ} (c : WalshIndex m) :
    (∑ x, walshCharacter c x) = if c = 0 then (walshCard m : ℝ) else 0 := by
  classical
  let ψ : AddChar (WalshIndex m) ℝ :=
    { toFun := walshCharacter c
      map_zero_eq_one' := by simp [walshCharacter, walshDot]
      map_add_eq_mul' := walshCharacter_add_right c }
  by_cases hc : c = 0
  · subst c
    simp [walshCharacter, walshDot, walshCard]
  · have hψ : ψ ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h
        apply hc
        funext i
        by_contra hi
        exact h ⟨i, hi⟩
      intro hzero
      have happ := DFunLike.congr_fun hzero (Pi.single i 1)
      have hdot : walshDot c (Pi.single i 1) = c i := by
        simp [walshDot, Pi.single_apply]
      change walshCharacter c (Pi.single i 1) = 1 at happ
      rw [walshCharacter, hdot, if_neg hi] at happ
      norm_num at happ
    have hsum : (∑ x, ψ x) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
    change (∑ x, walshCharacter c x) = 0 at hsum
    simpa only [hc, ↓reduceIte] using hsum

/-! ## Source-side theorem-strength interfaces -/

theorem I01_walsh_card (m : ℕ) : walshCard m = 2 ^ m := by
  simp [walshCard, WalshIndex]

theorem I01_walsh_symmetry (m : ℕ) :
    (normalizedWalsh m).transpose = normalizedWalsh m := by
  ext a b
  have hdot : walshDot b a = walshDot a b := by
    simp only [walshDot]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp only [Matrix.transpose_apply, normalizedWalsh, walshCharacter, hdot]

theorem I01_walsh_involution (m : ℕ) :
    normalizedWalsh m * normalizedWalsh m = 1 := by
  classical
  ext a b
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  have hab : a + b = 0 ↔ a = b := by
    have hneg : -b = b := by
      funext x
      exact ZMod.neg_eq_self_mod_two (b x)
    rw [add_eq_zero_iff_eq_neg]
    rw [hneg]
  simp only [Matrix.mul_apply, normalizedWalsh, Matrix.one_apply]
  calc
    (∑ x, walshCharacter a x / Real.sqrt (walshCard m : ℝ) *
        (walshCharacter x b / Real.sqrt (walshCard m : ℝ))) =
        (∑ x, walshCharacter (a + b) x) / (walshCard m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [walshCharacter_comm x b]
      field_simp
      rw [Real.sq_sqrt hcard.le]
      rw [walshCharacter_comm a x, walshCharacter_comm b x,
        ← walshCharacter_add_right, walshCharacter_comm x (a + b)]
      ring
    _ = if a = b then 1 else 0 := by
      rw [sum_walshCharacter, if_congr hab rfl rfl]
      split_ifs <;> simp [hcard.ne']

theorem I02_exact_gram_reduction {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    compressedGram V d₁ d₂ J =
      ((walshCard m : ℝ) / (k : ℝ)) •
        ((transformedFrame d₁ d₂ V).transpose * coordinateProjection J *
          transformedFrame d₁ d₂ V) := by
  classical
  simp only [compressedGram, rerandomizedSRHT, transformedFrame]
  simp only [Matrix.transpose_smul, Matrix.transpose_mul,
    signDiagonal, Matrix.diagonal_transpose,
    I01_walsh_symmetry]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hratio : 0 ≤ (walshCard m : ℝ) / (k : ℝ) := by positivity
  rw [show Real.sqrt ((walshCard m : ℝ) / (k : ℝ)) *
      Real.sqrt ((walshCard m : ℝ) / (k : ℝ)) =
        (walshCard m : ℝ) / (k : ℝ) by
    exact Real.mul_self_sqrt hratio]
  congr 1
  calc
    V.transpose *
          (Matrix.diagonal (signValue d₁) * normalizedWalsh m *
            Matrix.diagonal (signValue d₂) * normalizedWalsh m * sampleMatrix J) *
        ((sampleMatrix J).transpose *
          (normalizedWalsh m * (Matrix.diagonal (signValue d₂) *
            (normalizedWalsh m * Matrix.diagonal (signValue d₁))))) * V =
      V.transpose * Matrix.diagonal (signValue d₁) * normalizedWalsh m *
        Matrix.diagonal (signValue d₂) * normalizedWalsh m *
        (sampleMatrix J * (sampleMatrix J).transpose) * normalizedWalsh m *
        Matrix.diagonal (signValue d₂) * normalizedWalsh m *
        Matrix.diagonal (signValue d₁) * V := by
      simp only [Matrix.mul_assoc]
    _ = V.transpose * Matrix.diagonal (signValue d₁) * normalizedWalsh m *
        Matrix.diagonal (signValue d₂) * normalizedWalsh m *
        coordinateProjection J * normalizedWalsh m *
        Matrix.diagonal (signValue d₂) * normalizedWalsh m *
        Matrix.diagonal (signValue d₁) * V := by
      rw [sampleMatrix_mul_transpose]
    _ = V.transpose *
          (Matrix.diagonal (signValue d₁) *
            (normalizedWalsh m * (Matrix.diagonal (signValue d₂) * normalizedWalsh m))) *
        coordinateProjection J *
          (normalizedWalsh m * Matrix.diagonal (signValue d₂) * normalizedWalsh m *
            Matrix.diagonal (signValue d₁) * V) := by
      simp only [Matrix.mul_assoc]

theorem I03_full_sample_exact {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (d₁ d₂ : SignLayer (WalshIndex m))
    (J : FixedSubset (WalshIndex m) (walshCard m)) :
    compressedGram V d₁ d₂ J = 1 := by
  classical
  have hJ : J.1 = Finset.univ := by
    apply (Finset.card_eq_iff_eq_univ J.1).mp
    simpa [walshCard] using J.2
  have hP : coordinateProjection J =
      (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ) := by
    ext i j
    simp [coordinateProjection, Matrix.diagonal_apply, Matrix.one_apply, hJ]
  have hX : OrthonormalFrame (transformedFrame d₁ d₂ V) := by
    have hD₁ : Matrix.diagonal (signValue d₁) * Matrix.diagonal (signValue d₁) =
        (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ) :=
      signDiagonal_mul_self d₁
    have hD₂ : Matrix.diagonal (signValue d₂) * Matrix.diagonal (signValue d₂) =
        (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ) :=
      signDiagonal_mul_self d₂
    simp only [OrthonormalFrame, transformedFrame, Matrix.transpose_mul,
      signDiagonal, Matrix.diagonal_transpose, I01_walsh_symmetry]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (normalizedWalsh m) (normalizedWalsh m),
      I01_walsh_involution]
    simp only [Matrix.one_mul]
    rw [← Matrix.mul_assoc (Matrix.diagonal (signValue d₂)),
      hD₂]
    simp only [Matrix.one_mul]
    rw [← Matrix.mul_assoc (normalizedWalsh m), I01_walsh_involution]
    simp only [Matrix.one_mul]
    rw [← Matrix.mul_assoc (Matrix.diagonal (signValue d₁)),
      hD₁]
    simpa [OrthonormalFrame] using hV
  rw [I02_exact_gram_reduction V d₁ d₂ J, hP]
  have hcard : (walshCard m : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : walshCard m ≠ 0)
  rw [div_self hcard, one_smul, Matrix.mul_one]
  exact hX

theorem I04_mingo_speicher_graph_operator_specialization
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) :
    euclideanOperatorNorm (graphOperator dim src dst M input output) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  exact mingo_speicher_graph_operator_specialization dim src dst M
    input output hdag

theorem I05_mingo_speicher_bridgeless_conversion
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ)
    (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v))
    (hpositive : ∀ v, 0 < graphDegree src dst v)
    (hweight : ∀ v i, |w v i| ≤ 1)
    (u v : ι) (huv : u ≠ v) :
    ∃ (ι' ε' : Type) (_ : Fintype ι') (_ : Fintype ε')
      (_ : DecidableEq ι') (dim' : ι' → ℕ) (src' dst' : ε' → ι')
      (M' : ∀ e, Matrix (Fin (dim' (src' e))) (Fin (dim' (dst' e))) ℝ)
      (input output : ι'),
      input ≠ output ∧ MingoAdmissibleDAG src' dst' input output ∧
      dim' input = dim u ∧ dim' output = dim v ∧
      graphContraction dim src dst M w =
        ∑ a, ∑ b, graphOperator dim' src' dst' M' input output a b ∧
      (∏ e, euclideanOperatorNorm (M' e)) ≤
        ∏ e, euclideanOperatorNorm (M e) := by
  exact mingo_speicher_bridgeless_conversion dim src dst M w hconn heven
    hpositive hweight u v huv

theorem I06_connected_even_multigraph_has_no_bridge
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v)) :
    ∀ e₀ : ε, GraphConnected
      (fun e : {e // e ≠ e₀} ↦ src e.1)
      (fun e : {e // e ≠ e₀} ↦ dst e.1) := by
  exact connected_even_multigraph_has_no_bridge src dst hconn heven

theorem I07_rank_edge_factorization_bound
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v))
    (hpositive : ∀ v, 0 < graphDegree src dst v)
    (hnorm : ∀ e, euclideanOperatorNorm (M e) ≤ 1)
    (hweight : ∀ v i, |w v i| ≤ 1)
    (hrank : HasRankProjectionEdge dim src dst M r) :
    |graphContraction dim src dst M w| ≤ r := by
  classical
  letI : DecidableEq ε := Classical.decEq ε
  obtain ⟨e₀, L, R, hfactor, hL, hR⟩ :=
    hasRankProjectionEdge_factorization dim src dst M r hrank
  let sdim := rankEdgeSplitDim dim r
  let ssrc := rankEdgeSplitSrc src dst e₀
  let sdst := rankEdgeSplitDst src dst e₀
  let sM := rankEdgeSplitMatrix dim src dst M e₀ r L
    (1 : Matrix (Fin r) (Fin r) ℝ) R
  let sw := rankEdgeSplitWeight dim r w
  have hsconn : GraphConnected ssrc sdst := by
    exact graphConnected_rankEdgeSplit src dst e₀ hconn
  have hseven : ∀ z, Even (graphDegree ssrc sdst z) := by
    exact graphEven_rankEdgeSplit src dst e₀ heven
  have hspositive : ∀ z, 0 < graphDegree ssrc sdst z := by
    exact graphPositive_rankEdgeSplit src dst e₀ hpositive
  have hsweight : ∀ z i, |sw z i| ≤ 1 := by
    intro z i
    rcases z with v | k
    · exact hweight v i
    · simp [sw, rankEdgeSplitWeight]
  have huv : (Sum.inr (0 : Fin 2) : RankEdgeSplitVertex ι) ≠
      Sum.inr (Fin.succ 0) := by
    intro h
    have hk := Sum.inr.inj h
    norm_num at hk
  obtain ⟨ι', ε', fi', fe', deq', dim', src', dst', M', input, output,
      hio, hdag, hdin, hdout, hcontract, hprod⟩ :=
    I05_mingo_speicher_bridgeless_conversion sdim ssrc sdst sM sw
      hsconn hseven hspositive hsweight
      (Sum.inr (0 : Fin 2)) (Sum.inr (Fin.succ 0)) huv
  have hop := mingo_speicher_graph_operator_specialization
    dim' src' dst' M' input output hdag
  have hsM : ∀ e, euclideanOperatorNorm (sM e) ≤ 1 := by
    exact rankEdgeSplitMatrix_norm_le_one dim src dst M e₀ r L
      (1 : Matrix (Fin r) (Fin r) ℝ) R hnorm hL
      (euclideanOperatorNorm_one_le (α := Fin r)) hR
  have hsprod : (∏ e, euclideanOperatorNorm (sM e)) ≤ 1 := by
    exact Finset.prod_le_one
      (fun e _ => euclideanOperatorNorm_nonneg (sM e))
      (fun e _ => hsM e)
  calc
    |graphContraction dim src dst M w| =
        |graphContraction sdim ssrc sdst sM sw| := by
      rw [graphContraction_rankEdgeSplit dim src dst M w e₀ r L
        (1 : Matrix (Fin r) (Fin r) ℝ) R hfactor]
    _ = |∑ a, ∑ b,
        graphOperator dim' src' dst' M' input output a b| := by
      rw [hcontract]
    _ ≤ (r : ℝ) * euclideanOperatorNorm
        (graphOperator dim' src' dst' M' input output) := by
      exact abs_sum_all_entries_le_card_mul_operatorNorm_of_dim_eq
        (dim' input) (dim' output) r hdin hdout _
    _ ≤ (r : ℝ) * (∏ e, euclideanOperatorNorm (M' e)) := by
      exact mul_le_mul_of_nonneg_left hop (Nat.cast_nonneg r)
    _ ≤ (r : ℝ) * (∏ e, euclideanOperatorNorm (sM e)) := by
      exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg r)
    _ ≤ (r : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left hsprod (Nat.cast_nonneg r)
    _ = (r : ℝ) := by ring

theorem I08_moment_cumulant_inverse {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ}
    (Y : Fin q → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∏ j, Y j ω) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin q)),
        ∏ B ∈ P.parts, jointCumulantOn (fun j : B ↦ Y j.1) := by
  exact moment_cumulant_inverse_fin Y

theorem I09_product_cumulant_connected_partition_identity (b : ℕ) :
    (∑ j ∈ Finset.Icc 1 b,
      (Nat.stirlingSecond b j : ℤ) * (-1 : ℤ) ^ (j - 1) *
        (Nat.factorial (j - 1) : ℤ)) = (if b = 1 then 1 else 0) ∧
    ∀ {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
      (Y : ι → Ω → ℝ) (τ : Finpartition (Finset.univ : Finset ι)),
      jointCumulantOn (fun B : {B // B ∈ τ.parts} ↦
        fun ω ↦ ∏ j ∈ B.1, Y j ω) =
      connectedPartitionCumulantSum Y τ := by
  exact product_cumulant_connected_partition_identity b

theorem I10_independent_families_mixed_cumulant_vanish
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] [Nonempty Ω₁] [Nonempty Ω₂]
    {q : ℕ} (Y : Fin q → Ω₁ × Ω₂ → ℝ)
    (usesFirst usesSecond : Finset (Fin q))
    (hcover : usesFirst ∪ usesSecond = Finset.univ)
    (hdisjoint : Disjoint usesFirst usesSecond)
    (hfirst : ∀ j ∈ usesFirst, ∀ a b c, Y j (a, c) = Y j (b, c))
    (hsecond : ∀ j ∈ usesSecond, ∀ a b c, Y j (c, a) = Y j (c, b))
    (hnonempty₁ : usesFirst.Nonempty) (hnonempty₂ : usesSecond.Nonempty) :
    jointCumulant Y = 0 := by
  exact independent_families_mixed_cumulant_vanish Y usesFirst usesSecond
    hcover hdisjoint hfirst hsecond hnonempty₁ hnonempty₂

theorem I11_projection_entry_expansion {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (i j : WalshIndex m) :
    (walshCard m : ℝ) * randomProjection d₁ d₂ V i j =
      ∑ a, ∑ b, ∑ x, ∑ y,
        walshCharacter i a * walshCharacter j b * signValue d₂ a *
        signValue d₂ b * signValue d₁ x * signValue d₁ y *
        normalizedWalsh m a x * (V * V.transpose) x y *
        normalizedWalsh m y b := by
  classical
  simp [randomProjection, transformedFrame, Matrix.mul_apply, signDiagonal,
    normalizedWalsh, Matrix.diagonal_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [sum_five_permute]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [walshCharacter_comm b y]
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  field_simp
  rw [Real.sq_sqrt hcard.le]
  ring

theorem I12_occurrence_partitions_form_connected_even_graph
    {m r q : ℕ} (hq : 1 ≤ q) (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m)
    (hmiddle : ∀ B ∈ D.middle.parts, 0 < B.card ∧ Even B.card)
    (hinput : ∀ B ∈ D.input.parts, 0 < B.card ∧ Even B.card)
    (hjoin : ProductOccurrenceConnected D) :
    IsSurvivingOccurrencePartition D ∧
    GraphConnected (occurrenceSrc D) (occurrenceDst D) ∧
    (∀ v, 0 < graphDegree (occurrenceSrc D) (occurrenceDst D) v ∧
      Even (graphDegree (occurrenceSrc D) (occurrenceDst D) v)) ∧
    euclideanOperatorNorm (normalizedWalsh m) ≤ 1 ∧
    euclideanOperatorNorm (V * V.transpose) ≤ 1 ∧
    (∀ f B, |walshCharacter (i f) B| = 1 ∧ |walshCharacter (j f) B| = 1) ∧
    (∀ e, euclideanOperatorNorm (occurrenceEdgeMatrix D V e) ≤ 1) ∧
    (∀ v a, |occurrenceVertexWeight D i j v a| ≤ 1) ∧
    HasRankProjectionEdge (fun _ : OccurrenceVertex D ↦ walshCard m)
      (occurrenceSrc D) (occurrenceDst D) (occurrenceEdgeMatrix D V) r ∧
    occurrenceContraction D V i j =
      graphContraction (fun _ : OccurrenceVertex D ↦ walshCard m)
        (occurrenceSrc D) (occurrenceDst D) (occurrenceEdgeMatrix D V)
        (occurrenceVertexWeight D i j) := by
  exact occurrence_partitions_form_connected_even_graph
    hq D V hV i j hmiddle hinput hjoin

theorem I13_rademacher_cumulant_bound (b : ℕ) :
    |jointCumulant (Ω := Bool) (q := b)
      (fun _ ξ ↦ if ξ then (-1 : ℝ) else 1)| ≤ (b : ℝ) ^ (2 * b) ∧
    Fintype.card (EvenOccurrencePartition b × EvenOccurrencePartition b) ≤
      (2 * b) ^ (4 * b) ∧
    (∀ P : EvenOccurrencePartition b,
      |∏ B : {B // B ∈ P.1.parts}, rademacherCumulant B.1.card| ≤
        ((2 * b : ℕ) : ℝ) ^ (4 * b)) := by
  exact rademacher_cumulant_bound b

theorem I14_walsh_translation_modulation {m : ℕ} (s : WalshIndex m) :
    (∀ i a, walshCharacter (i + s) a =
      walshCharacter i a * walshCharacter s a) ∧
    walshModulation s * normalizedWalsh m =
      normalizedWalsh m * walshTranslation s ∧
    walshTranslation s * normalizedWalsh m =
      normalizedWalsh m * walshModulation s ∧
    (∀ F : SignLayer (WalshIndex m) → SignLayer (WalshIndex m) → ℝ,
      signPairExpectation (fun d₁ d₂ ↦
        F (modulateSign s d₁) (translateSign s d₂)) = signPairExpectation F) ∧
    (∀ r (V : Matrix (WalshIndex m) (Fin r) ℝ) d₁ d₂,
      randomProjection (modulateSign s d₁) (translateSign s d₂) V =
        walshModulation s * randomProjection d₁ d₂ V * walshModulation s) ∧
    (∀ x : WalshIndex m, x ≠ 0 →
      ∃ c : WalshIndex m, walshCharacter c x = -1) := by
  exact walsh_translation_modulation_package s

theorem I15_projection_mean_and_centering {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V) :
    (∀ i j, signPairExpectation (fun d₁ d₂ ↦ randomProjection d₁ d₂ V i j) =
      if i = j then (r : ℝ) / walshCard m else 0) ∧
    (∀ i j, signPairExpectation (fun d₁ d₂ ↦
      (randomProjection d₁ d₂ V - ((r : ℝ) / walshCard m) • 1) i j) = 0) ∧
    (∀ (q : ℕ), 2 ≤ q → ∀ i j : Fin q → WalshIndex m,
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦
          (randomProjection d.1 d.2 V - ((r : ℝ) / walshCard m) • 1)
            (i f) (j f)) =
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ randomProjection d.1 d.2 V (i f) (j f))) := by
  exact projection_mean_and_centering V hV

theorem I16_selector_quotient_degree_excess
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    s ≤ p - 1 ∧ s + t ≤ p ∧
    GraphConnected (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) ∧
    (∀ B : EqualityVertex Q.1,
      graphDegree (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
        (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) B =
          2 * B.1.card) ∧
    (∑ B ∈ Q.1.parts, (2 * B.card - 4) = 4 * s) := by
  exact ⟨(selector_quotient_parameter_bounds hp Q).1,
    (selector_quotient_parameter_bounds hp Q).2,
    selector_quotient_graph_connected hp Q,
    selector_quotient_degree hp Q,
    selector_quotient_total_excess hp Q⟩

theorem I17_centered_bernoulli_moment_bound
    (θ : ℝ) (b : ℕ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2) (hb : 2 ≤ b) :
    |θ * (1 - θ) ^ b + (1 - θ) * (-θ) ^ b| ≤ θ := by
  have hθ : 0 ≤ θ := hθ₀.le
  have hθle : θ ≤ 1 := by linarith
  have hone : 0 ≤ 1 - θ := by linarith
  have honele : 1 - θ ≤ 1 := by linarith
  have hpθ : θ ^ b ≤ θ ^ 2 := pow_le_pow_of_le_one hθ hθle hb
  have hpone : (1 - θ) ^ b ≤ (1 - θ) ^ 2 :=
    pow_le_pow_of_le_one hone honele hb
  calc
    |θ * (1 - θ) ^ b + (1 - θ) * (-θ) ^ b| ≤
        |θ * (1 - θ) ^ b| + |(1 - θ) * (-θ) ^ b| := abs_add_le _ _
    _ = θ * (1 - θ) ^ b + (1 - θ) * θ ^ b := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      simp only [abs_of_nonneg hθ, abs_of_nonneg hone, abs_neg]
    _ ≤ θ * (1 - θ) ^ 2 + (1 - θ) * θ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpone hθ)
        (mul_le_mul_of_nonneg_left hpθ hone)
    _ = θ * (1 - θ) := by ring
    _ ≤ θ := by nlinarith

theorem I18_exceptional_vertex_degree_budget
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (equalityExceptionalVertices Q.1).card ≤ t + 2 * s ∧
    equalityExceptionalDegree Q.1 ≤ 4 * t + 12 * s := by
  exact selector_exceptional_vertex_degree_budget hp Q

theorem I19_degree_four_classification_and_loop_bound
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (∀ B ∈ Q.1.parts, B ∉ equalityExceptionalVertices Q.1 →
      IsEqualityInternal Q.1 B ∨ IsEqualityLoopTerminal Q.1 B ∨
        IsEqualityFourEdgeTerminal Q.1 B) ∧
    (equalityExceptionalVertices Q.1 = ∅ →
      (∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B) ∨
      (∃ U ∈ Q.1.parts, ∃ V ∈ Q.1.parts, U ≠ V ∧
        IsEqualityLoopTerminal Q.1 U ∧ IsEqualityLoopTerminal Q.1 V ∧
        ∀ B ∈ Q.1.parts, B ≠ U → B ≠ V → IsEqualityInternal Q.1 B) ∨
      (Q.1.parts.card = 2 ∧
        ∀ B ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 B) ∨
      (Q.1.parts.card = 1 ∧ equalityLoopOccurrences Q.1 = 2)) ∧
    equalityLoopOccurrences Q.1 ≤ 4 * t + 12 * s + 2 := by
  exact degree_four_classification_and_loop_bound hp Q

theorem I20_contracted_core_encoding_bound (p s t : ℕ) (hp : 2 ≤ p) :
    Fintype.card (ContractedCoreCode p (s + t)) ≤
        (4 * p + 1) ^ (72 * (s + t)) ∧
    Nonempty (EqualityEncoding p s t) := by
  exact contracted_core_encoding_bound_closed p s t hp

theorem I21_euler_transition_count (p s t : ℕ) (hp : 2 ≤ p)
    (enc : EqualityEncoding p s t) :
      (∀ c : ContractedCoreCode p (s + t),
        Fintype.card (EulerTransitions c) ≤
          8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) ∧
      selectorEqualityCount p s t ≤
        (4 * p + 1) ^ (72 * (s + t)) *
          (8 * p * 3 ^ p * (4 * p + 1) ^ (2 * (s + t))) := by
  exact euler_transition_count p s t enc

theorem I22_xor_kernel_solution_count
    (m v h : ℕ) (A : Matrix (Fin h) (Fin v) (ZMod 2))
    (hrank : Matrix.rank A = h) :
    Fintype.card {x : Fin v → WalshIndex m //
      ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} =
      (2 ^ m) ^ (v - h) := by
  exact xor_kernel_solution_count m v h A hrank

theorem I23_pointwise_vanishing_pair_classification
    (m v : ℕ) (label : Fin v → WalshIndex m) (hinj : Function.Injective label) :
    (∀ u₁ v₁ u₂ v₂ : Fin v,
      label u₁ + label v₁ + label u₂ + label v₂ = 0 →
      (u₁ = v₁ ∧ u₂ = v₂) ∨
      ((u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂)) ∨
      (u₁ ≠ v₁ ∧ u₂ ≠ v₂ ∧
        Disjoint ({u₁, v₁} : Finset (Fin v)) ({u₂, v₂} : Finset (Fin v)))) ∧
    (∀ (p s t : ℕ) (D : EntryCumulantPartitionData p s t)
      (lab : EqualityVertex D.selector.1 → WalshIndex m), Function.Injective lab →
      (∀ B ∈ D.entry.parts, B.card = 2 →
        (∑ e ∈ B,
          (lab (equalityVertexAt D.selector.1 e) +
            lab (equalityVertexAt D.selector.1 (cyclicSucc e)))) = 0) →
      AdmissibleEntryPairBlocks D) := by
  exact ⟨walsh_label_vanishing_pair_classification m v label hinj,
    pointwise_vanishing_pair_blocks_admissible m⟩

theorem I24_large_block_and_support_rank_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (hd : d ≤ p - 1)
    (D : EntryCumulantPartitionData p s t)
    (hnonsingleton : ∀ B ∈ D.entry.parts, 2 ≤ B.card)
    (hadmissible : AdmissibleEntryPairBlocks D)
    (hblocks : D.entry.parts.card = p - d)
    (hrank : Matrix.rank (entryConstraintMatrix D) = h) :
    (largeBlockOccurrences D).card ≤ 6 * d ∧
    (largeTouchedVertices D).card ≤ 12 * d ∧
    oddIncidentVertexSet D ⊆
      largeTouchedVertices D ∪ disjointConstraintSupport D ∧
    Matrix.rank (disjointConstraintMatrix D) ≤ h ∧
    (disjointConstraintSupport D).card ≤ 4 * h ∧
    t ≤ 12 * d + 4 * h := by
  exact large_block_and_support_rank_bound hp hd D hnonsingleton hadmissible
    hblocks hrank

theorem I25_large_block_partition_constant_bound (p d : ℕ) :
    Fintype.card (LargeBlockPattern p d) ≤ (4 * p + 1) ^ (12 * d) ∧
    ∀ pattern : LargeBlockPattern p d,
      (4 * p) ^ (12 * pattern.1.1.card) ≤ (4 * p + 1) ^ (72 * d) := by
  exact large_block_partition_constant_bound p d

theorem I26_disjoint_pair_support_bound
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) (h : ℕ) :
    (∀ U : Finset (EqualityVertex Q.1), U.card ≤ 4 * h →
      (occurrenceWithinVertices Q U).card ≤ 8 * h + 2 * s) ∧
    Fintype.card (DisjointPairChoice Q h) ≤
      (4 * p + 1) ^ (12 * h + 2 * s) := by
  exact disjoint_pair_support_bound hp Q h

theorem I27_loop_parallel_pairing_bound (p s t ell : ℕ)
    (hp : 2 ≤ p) (hell : ell ≤ 4 * t + 12 * s + 2) (hellp : ell ≤ 2 * p) :
    Fintype.card (Pairing (Finset.univ : Finset (Fin ell))) ≤
        (4 * p + 1) ^ (2 * t + 6 * s + 1) ∧
    (∀ (g : ℕ), g ≤ p → ∀ a : Fin g → ℕ,
      (∀ e, 0 < a e ∧ Even (a e)) →
      (∑ e, (a e - 4)) ≤ 2 * s →
      (∏ e, 3 * (4 * p) ^ ((a e - 4) / 2)) ≤
        3 ^ p * (4 * p + 1) ^ s) := by
  exact loop_parallel_pairing_bound p s t ell hp hell hellp

theorem I28_aggregate_partition_cumulant_bound
    {p s t d h : ℕ} (hp : 2 ≤ p) (hd : d ≤ p - 1)
    (Q : SelectorEqualityData p s t) :
    aggregateEntryPartitionCumulantSum Q d h ≤
      (3 * K₂) ^ p *
        (4 * p + 1) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) := by
  exact aggregate_partition_cumulant_bound hp hd Q

theorem I29_exact_dimension_factor
    (n r p s d h : ℕ) (θ : ℝ) (hn : 0 < n) (hr : 0 < r) (hθ : 0 < θ)
    (hd : d ≤ p) (hsh : s + h ≤ p) :
    θ ^ (p - s) * (r : ℝ) ^ (p - d) * (n : ℝ) ^ (-(2 * p : ℤ)) *
      (n : ℝ) ^ (p - s - h) =
    (((r : ℝ) / n) * θ) ^ p * ((n : ℝ) * θ) ^ (-(s : ℤ)) *
      (r : ℝ) ^ (-(d : ℤ)) * (n : ℝ) ^ (-(h : ℤ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hs : s ≤ p := by omega
  have hh : h ≤ p - s := by omega
  have htwop : (2 : ℤ) * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by norm_num
  rw [pow_sub₀ θ hθ0 hs, pow_sub₀ (r : ℝ) hr0 hd]
  rw [pow_sub₀ (n : ℝ) hn0 hh, pow_sub₀ (n : ℝ) hn0 hs]
  rw [htwop]
  simp only [zpow_neg, zpow_natCast]
  field_simp
  simp only [mul_pow, div_pow]
  rw [show 2 * p = p + p by omega, pow_add]
  field_simp

theorem I30_trace_geometric_summation (p r : ℕ)
    (hp : 2 ≤ p) (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    let ρ : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r
    0 ≤ ρ ∧ ρ ≤ 1 / 2 ∧
    (∑' j : ℕ, ρ ^ j) ≤ 2 ∧
    (∑' j : ℕ, ρ ^ j) ^ 3 ≤ 8 ∧
    (∀ d h : ℕ,
      (∑ t ∈ Finset.range (12 * d + 4 * h + 1),
        (((4 * p + 1 : ℕ) : ℝ) ^ (76 * t))) ≤
          2 * ((4 * p + 1 : ℕ) : ℝ) ^ (912 * d + 304 * h)) ∧
    (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) ≤ 8 ∧
    128 * p * (4 * p + 1) ≤ 64 ^ p ∧
    64 * 9 * K₂ = K₀ := by
  exact trace_geometric_summation p r hp hr

theorem I31_two_projection_block_decomposition
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E) :
    ∃ (Q : Matrix α α ℝ) (block : α → α),
      IsTwoProjectionBlockDecomposition (X * X.transpose) E Q block ∧
      ((Finset.univ : Finset α).filter (fun i ↦
        ((Finset.univ : Finset α).filter fun j ↦ block j = block i).card = 2)).card /
          2 ≤ r := by
  exact twoProjectionBlockDecomposition_exists X E hX hE

theorem I32_quadratic_root_even_power_bound
    (a t : ℝ) (p : ℕ) (ha : 0 ≤ a) :
    ∀ z₁ z₂ : ℂ,
      z₁ + z₂ = t ∧ z₁ * z₂ = a ^ 2 →
      -2 * a ^ (2 * p) ≤ (z₁ ^ (2 * p) + z₂ ^ (2 * p)).re := by
  exact quadratic_root_even_power_bound a t p ha

theorem I33_bad_spectral_edge_large_root
    (lam δ θ η : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hδ : 0 < δ)
    (hθ : 0 < θ ∧ θ ≤ 1 / 2) (hη : 0 < η ∧ η < 1)
    (hsmall : δ ≤ θ * η ^ 2 / 64)
    (hbad : |lam - θ| > θ * η) :
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    let t := lam - δ - θ + 2 * δ * θ
    |t| > 63 * (θ * η) / 64 ∧
    (lam = 0 → (1 - δ) * θ > θ * η / 2) ∧
    (lam = 1 → (1 - δ) * (1 - θ) > θ * η / 2) ∧
    (0 < lam → lam < 1 →
      ∃ z₁ z₂ : ℝ, z₁ + z₂ = t ∧ z₁ * z₂ = a2 ∧
        max |z₁| |z₂| > θ * η / 2) := by
  exact bad_spectral_edge_large_root lam δ θ η hlam hδ hθ hη hsmall hbad

theorem I34_bernoulli_failure_arithmetic (p r : ℕ)
    (hp : Nat.ceil (Real.logb 2 (3000 * r : ℝ)) ≤ p) :
    (3 : ℝ) * r * 2 ^ (-(p : ℤ)) ≤ 1 / 1000 := by
  by_cases hr : r = 0
  · subst r
    norm_num
  have hrpos : 0 < (3000 : ℝ) * r := by positivity
  have hceil : Real.logb 2 (3000 * r : ℝ) ≤
      (Nat.ceil (Real.logb 2 (3000 * r : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hpc : (Nat.ceil (Real.logb 2 (3000 * r : ℝ)) : ℝ) ≤ p := by
    exact_mod_cast hp
  have hlog : Real.logb 2 (3000 * r : ℝ) ≤ (p : ℝ) := hceil.trans hpc
  have hpow : (3000 : ℝ) * r ≤ (2 : ℝ) ^ p := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (b := 2) (y := (p : ℝ))
      (by norm_num) hrpos).mp hlog
  have hpowpos : 0 < (2 : ℝ) ^ p := by positivity
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply (div_le_iff₀ hpowpos).2
  calc
    (3 : ℝ) * r = (1 / 1000) * (3000 * r) := by ring
    _ ≤ (1 / 1000) * 2 ^ p :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem I35_uniform_key_nested_coupling (n k : ℕ) (α : ℝ)
    (hk : k ≤ n) (hα : 0 < α ∧ α < 1)
    (htheta : (1 + α) * k / n ≤ 1) :
    ∃ coupling : FixedSubset (Fin n) k × SignLayer (Fin n) ×
        SignLayer (Fin n) → ℝ,
      (∀ sample, 0 ≤ coupling sample) ∧
      (∑ sample, coupling sample) = 1 ∧
      (∀ sample, coupling sample ≠ 0 →
        (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
        (((Finset.univ.filter fun i ↦ sample.2.1 i = true).card ≤ k ∧
            k ≤ (Finset.univ.filter fun i ↦ sample.2.2 i = true).card) →
          (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
          (∀ i, i ∈ sample.1.1 → sample.2.2 i = true))) ∧
      (∀ J, (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset (Fin n) k)) ∧
      (∀ bminus, (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
        bernoulliWeight ((1 - α) * k / n) bminus) ∧
      (∀ bplus, (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
        bernoulliWeight ((1 + α) * k / n) bplus) := by
  exact ThreeCategoryOrder.uniform_key_nested_coupling_via_three_category
    n k α hk hα htheta

theorem I36_sampling_sandwich_spectral_conversion
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k)
    (bminus bplus : SignLayer α) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hminus : ∀ i, bminus i = true → i ∈ J.1)
    (hplus : ∀ i, i ∈ J.1 → bplus i = true) :
    let α₀ := ε / 4
    let θminus := (1 - α₀) * k / Fintype.card α
    let θplus := (1 + α₀) * k / Fintype.card α
    (∀ x, (1 - α₀) * quadraticForm (bernoulliGram θminus X bminus) x ≤
        quadraticForm (fixedSampleGram X J) x ∧
      quadraticForm (fixedSampleGram X J) x ≤
        (1 + α₀) * quadraticForm (bernoulliGram θplus X bplus) x) ∧
    (euclideanOperatorNorm (bernoulliGram θminus X bminus - 1) ≤ α₀ →
      euclideanOperatorNorm (bernoulliGram θplus X bplus - 1) ≤ α₀ →
      euclideanOperatorNorm (fixedSampleGram X J - 1) ≤ ε) ∧
    1 - ε ≤ (1 - α₀) ^ 2 ∧ (1 + α₀) ^ 2 ≤ 1 + ε := by
  exact sampling_sandwich_spectral_conversion X J bminus bplus ε hε hk hminus hplus

theorem I37_binomial_tail_bounds
    (n : ℕ) (θ a : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ha : 0 ≤ a) :
    let μ := n * θ
    bernoulliProbability (α := Fin n) θ (fun e ↦
      a ≤ ((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ) ≤
        Real.exp (-(a ^ 2) / (2 * μ + 2 * a / 3)) ∧
    bernoulliProbability (α := Fin n) θ (fun e ↦
      a ≤ μ - ((Finset.univ.filter fun i ↦ e i).card : ℝ)) ≤
        Real.exp (-(a ^ 2) / (2 * μ)) := by
  exact binomial_tail_bounds n θ a hθ ha

theorem I38_finite_population_second_moment_identity
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X)
    (hn : 1 < Fintype.card α) (hk₁ : 1 ≤ k) (hkₙ : k ≤ Fintype.card α) :
    uniformExpectation (Ω := FixedSubset α k) (fun J ↦
      frobeniusNormSq (fixedSampleGram X J - 1)) =
      ((Fintype.card α - k : ℕ) : ℝ) /
        ((k : ℝ) * (Fintype.card α - 1 : ℕ)) *
        ((Fintype.card α : ℝ) * ∑ i, (∑ j, (X i j) ^ 2) ^ 2 - r) := by
  exact finite_population_second_moment_identity X hX hn hk₁ hkₙ

theorem I39_rademacher_vector_fourth_moment
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (U : Matrix α (Fin r) ℝ) (hU : OrthonormalFrame U) :
    uniformExpectation (Ω := SignLayer α) (fun ξ ↦
      (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) =
      ((r : ℝ) ^ 2 + 2 * r -
        2 * ∑ j, (∑ a, (U j a) ^ 2) ^ 2) ∧
    uniformExpectation (Ω := SignLayer α) (fun ξ ↦
      (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) ≤
      ((r : ℝ) ^ 2 + 2 * r) := by
  exact rademacher_vector_fourth_moment U hU

theorem I40_operator_norm_le_frobenius :
    (∀ (α : Type*) [Fintype α] (A : Matrix α α ℝ),
      euclideanOperatorNorm A ^ 2 ≤ frobeniusNormSq A) ∧
    (∀ (Ω α : Type*) [Fintype Ω] [Nonempty Ω] [Fintype α]
      (A : Ω → Matrix α α ℝ) (ε M : ℝ), 0 < ε →
      uniformExpectation (fun ω ↦ frobeniusNormSq (A ω)) ≤ M →
      uniformProbability (fun ω ↦ euclideanOperatorNorm (A ω) > ε) ≤
        M / ε ^ 2) := by
  constructor
  · intro α _ A
    exact euclideanOperatorNorm_sq_le_frobeniusNormSq A
  · intro Ω α _ _ _ A ε M hε hmean
    exact uniformProbability_operatorNorm_gt_le_frobeniusExpectation
      A ε M hε hmean

theorem I41_large_rank_cutoff_arithmetic (r : ℕ) (hr : R₀ ≤ r) :
    let p := Nat.ceil (Real.logb 2 (3000 * r : ℝ))
    2 * (4 * p + 1) ^ 1000 ≤ r := by
  exact large_rank_cutoff_arithmetic r hr

theorem I42_final_width_constant_assembly :
    explicitUniversalConstant = 200 * R₀ + 8196 * K₀ ∧
    ∀ (m r : ℕ) (ε : ℝ),
      1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
      ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
        k ≤ Nat.min (walshCard m)
          (Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2)) ∧
        ((r < R₀ ∧
            k = Nat.min (walshCard m)
              (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))) ∨
          (R₀ ≤ r ∧
            let k₀ := Nat.ceil ((2048 * K₀ : ℝ) * r / ε ^ 2)
            (walshCard m ≤ 4 * k₀ →
              k = walshCard m ∧
              k ≤ Nat.ceil ((8196 * K₀ : ℝ) * r / ε ^ 2)) ∧
            (4 * k₀ < walshCard m →
              k = k₀ ∧
              (1 + ε / 4) * k₀ / walshCard m ≤ 5 / 16 ∧
              (3 : ℝ) / 4 * k₀ ≥
                (1536 * K₀ : ℝ) * r / ε ^ 2 ∧
              2 / 1000 + 2 * Real.exp (-(ε ^ 2 * k₀ / 48)) < 1 / 100))) := by
  exact final_width_constant_assembly

/-! ## Nine named public results -/

theorem graph_rank_contraction
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (r : ℕ)
    (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v))
    (hpositive : ∀ v, 0 < graphDegree src dst v)
    (hnorm : ∀ e, euclideanOperatorNorm (M e) ≤ 1)
    (hweight : ∀ v i, |w v i| ≤ 1)
    (hrank : 1 ≤ r ∧ HasRankProjectionEdge dim src dst M r) :
    |graphContraction dim src dst M w| ≤ r := by
  exact I07_rank_edge_factorization_bound dim src dst M w r hrank.1 hconn heven
    hpositive hnorm hweight hrank.2

theorem joint_entry_cumulant_lemma {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m) (hq : 1 ≤ q) :
    |jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) * randomProjection d.1 d.2 V (i f) (j f))| ≤
        ((2 * q : ℕ) : ℝ) ^ (12 * q) * r ∧
    ((∑ f, (i f + j f)) ≠ 0 →
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ (walshCard m : ℝ) * randomProjection d.1 d.2 V (i f) (j f)) = 0) ∧
    (∀ a b, signPairExpectation (fun d₁ d₂ ↦ randomProjection d₁ d₂ V a b) =
      if a = b then (r : ℝ) / walshCard m else 0) := by
  apply joint_entry_cumulant_assembly _ V hV i j hq
  intro ι ε _ _ _ dim src dst M w r hconn heven hpositive hnorm hweight hrank
  exact graph_rank_contraction dim src dst M w r hconn heven hpositive hnorm
    hweight hrank

theorem selector_equality_graph_count (p s t : ℕ) (hp : 2 ≤ p) :
    (∀ Q : SelectorEqualityData p s t,
      equalityLoopOccurrences Q.1 ≤ 4 * t + 12 * s + 2) ∧
    selectorEqualityCount p s t ≤
      8 * p * 3 ^ p * (4 * p + 1) ^ (74 * (s + t)) := by
  constructor
  · intro Q
    exact (I19_degree_four_classification_and_loop_bound hp Q).2.2
  · let L := 4 * p + 1
    obtain ⟨enc⟩ := (I20_contracted_core_encoding_bound p s t hp).2
    have hcount := (I21_euler_transition_count p s t hp enc).2
    calc
      selectorEqualityCount p s t ≤
          L ^ (72 * (s + t)) *
            (8 * p * 3 ^ p * L ^ (2 * (s + t))) := hcount
      _ = 8 * p * 3 ^ p * L ^ (74 * (s + t)) := by
        rw [show 74 * (s + t) = 72 * (s + t) + 2 * (s + t) by omega,
          pow_add]
        ring

theorem signed_trace_proposition {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hp : 2 ≤ p) (hθ : 0 < θ ∧ θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace (((randomProjection d₁ d₂ V -
          ((r : ℝ) / walshCard m) • 1) *
        (bernoulliProjection e - θ • 1)) ^ (2 * p)))| ≤
      (K₀ : ℝ) ^ p * (((r : ℝ) / walshCard m) * θ) ^ p := by
  apply signedTrace_bound
  · intro ι ε _ _ _ dim src dst M w r hconn heven hpositive hnorm hweight hrank
    exact graph_rank_contraction dim src dst M w r hconn heven hpositive hnorm
      hweight hrank
  · intro p s t hp
    exact (selector_equality_graph_count p s t hp).2
  · exact hV
  · exact hp
  · exact hθ.1
  · exact hθ.2
  · exact hκ
  · exact hr

theorem two_projection_spectral_transfer
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
  exact two_projection_spectral_transfer_proof X E hX hE δ θ hp hδ hθ

theorem bernoulli_coordinate_sampling_corollary {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (p : ℕ) (hp : p = Nat.ceil (Real.logb 2 (3000 * r : ℝ)))
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r)
    (η θ : ℝ) (hη : 0 < η ∧ η < 1) (hθ : 0 < θ ∧ θ ≤ 1 / 2)
    (hκ : 64 * K₀ * r / η ^ 2 ≤ (walshCard m : ℝ) * θ) :
    signPairExpectation (fun d₁ d₂ ↦
      bernoulliProbability θ (fun e ↦
        euclideanOperatorNorm
          (bernoulliGram θ (transformedFrame d₁ d₂ V) e - 1) > η)) ≤
      1 / 1000 := by
  have hr2 : 2 ≤ r := by
    have hbasepos : 0 < (4 * p + 1) ^ 1000 :=
      pow_pos (by omega) 1000
    have hbase : 1 ≤ (4 * p + 1) ^ 1000 := hbasepos
    omega
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hlog : (2 : ℝ) ≤ Real.logb 2 (3000 * r : ℝ) := by
      apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).2
      rw [Real.rpow_two]
      norm_num
      exact_mod_cast (show 4 ≤ 3000 * r by omega)
    have hceil := hlog.trans (Nat.le_ceil (Real.logb 2 (3000 * r : ℝ)))
    exact_mod_cast hceil
  have hηsqpos : 0 < η ^ 2 := sq_pos_of_pos hη.1
  have hκ' : (64 : ℝ) * K₀ * r ≤
      ((walshCard m : ℝ) * θ) * η ^ 2 := by
    exact (div_le_iff₀ hηsqpos).mp (by simpa using hκ)
  have hηsqle : η ^ 2 ≤ 1 := by nlinarith [sq_nonneg η]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hK : (1 : ℝ) ≤ K₀ := by norm_num [K₀, K₂]
  have hκtrace : (r : ℝ) ≤ (walshCard m : ℝ) * θ := by
    have hfactor : (1 : ℝ) ≤ 64 * K₀ := by nlinarith
    have hscale : (r : ℝ) ≤ 64 * K₀ * r := by
      calc
        (r : ℝ) = 1 * r := by ring
        _ ≤ (64 * K₀) * r := mul_le_mul_of_nonneg_right hfactor hrpos.le
    have hnθ : 0 ≤ (walshCard m : ℝ) * θ :=
      mul_nonneg (Nat.cast_nonneg _) hθ.1.le
    calc
      (r : ℝ) ≤ 64 * K₀ * r := hscale
      _ ≤ ((walshCard m : ℝ) * θ) * η ^ 2 := hκ'
      _ ≤ (walshCard m : ℝ) * θ :=
        mul_le_of_le_one_right hnθ hηsqle
  apply bernoulli_coordinate_sampling_corollary_of_trace
    V hV p hp hr η θ hη hθ hκ
  exact signed_trace_proposition V hV θ hp2 hθ hκtrace hr

theorem fixed_size_sampling_transfer
    {Ω α : Type*} [Fintype Ω] [Nonempty Ω] [Fintype α] [DecidableEq α]
    {r k : ℕ} (X : Ω → Matrix α (Fin r) ℝ)
    (hX : ∀ ω, OrthonormalFrame (X ω))
    (ε γ : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hthetaMinus : (1 - ε / 4) * k / Fintype.card α ≤ 1)
    (hthetaPlus : (1 + ε / 4) * k / Fintype.card α ≤ 1)
    (hminus : uniformBernoulliFailureProbability
      ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ)
    (hplus : uniformBernoulliFailureProbability
      ((1 + ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ) :
    uniformFixedFailureProbability (k := k) ε X ≤
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48)) := by
  exact fixed_size_sampling_transfer_proof X hX ε γ hε hk
    hthetaMinus hthetaPlus hminus hplus

theorem small_rank_second_moment {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (hk : 1 ≤ k ∧ k ≤ walshCard m) :
    uniformExpectation
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k)
      (fun sample ↦ frobeniusNormSq
        (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) ≤
      (r : ℝ) * (r + 1) / k ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → 1 ≤ r → r ≤ walshCard m →
      let k₀ := Nat.min (walshCard m)
        (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))
      frameFailureProbability (k := k₀) ε V ≤ 1 / 100) := by
  apply small_rank_second_moment_of_gram_reduction V hV hk
  intro ε hε0 hε1 hr hrn d₁ d₂ J
  simpa only [fixedSampleGram, walshCard] using
    I02_exact_gram_reduction V d₁ d₂ J

private theorem uniformProbability_prod_assoc
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (event : A × (B × C) → Prop) :
    uniformProbability event =
      uniformProbability (fun z : (A × B) × C ↦ event (z.1.1, z.1.2, z.2)) := by
  classical
  unfold uniformProbability
  let e : (A × B) × C ≃ A × (B × C) := Equiv.prodAssoc A B C
  have hnum :
      (∑ z : A × (B × C), if event z then (1 : ℝ) else 0) =
        ∑ z : (A × B) × C,
          if event (z.1.1, z.1.2, z.2) then (1 : ℝ) else 0 := by
    symm
    exact Fintype.sum_equiv e _ _ (fun z ↦ rfl)
  simp only [Finset.natCast_card_filter, Finset.sum_filter,
    Finset.mem_univ, if_true] at *
  rw [hnum]
  congr 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

private theorem frameFailureProbability_eq_uniformFixed
    {m r k : ℕ} (ε : ℝ)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    frameFailureProbability (k := k) ε V =
      uniformFixedFailureProbability (k := k) ε
        (fun d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ↦
          transformedFrame d.1 d.2 V) := by
  unfold frameFailureProbability uniformFixedFailureProbability
  rw [uniformProbability_prod_assoc (A := SignLayer (WalshIndex m))
    (B := SignLayer (WalshIndex m)) (C := FixedSubset (WalshIndex m) k)]
  congr 1
  funext sample
  rw [I02_exact_gram_reduction]
  rfl

private theorem frameFailureProbability_full_sample
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (ε : ℝ) (hε : 0 < ε) :
    frameFailureProbability (k := walshCard m) ε V = 0 := by
  classical
  unfold frameFailureProbability uniformProbability
  have hpoint : ∀ sample : SignLayer (WalshIndex m) ×
      (SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) (walshCard m)),
      ¬ euclideanOperatorNorm
        (compressedGram V sample.1 sample.2.1 sample.2.2 - 1) > ε := by
    intro sample
    rw [I03_full_sample_exact V hV]
    simp only [sub_self]
    rw [euclideanOperatorNorm_eq_l2_opNorm]
    rw [Matrix.l2_opNorm_def]
    simpa using hε.le
  have hempty : (Finset.univ.filter fun sample : SignLayer (WalshIndex m) ×
      (SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) (walshCard m)) ↦
        euclideanOperatorNorm
          (compressedGram V sample.1 sample.2.1 sample.2.2 - 1) > ε) = ∅ := by
    ext sample
    simp [hpoint sample]
  rw [hempty]
  simp

theorem main_universal_ose :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
          k ≤ Nat.min (walshCard m)
            (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
          spectralFailureSup m r k ε ≤ 1 / 100 := by
  refine ⟨explicitUniversalConstant, rfl, ?_, ?_⟩
  · norm_num [explicitUniversalConstant, R₀, K₀, K₂]
  · intro m r ε hr hrn hε0 hε1
    obtain ⟨_, hwidth⟩ := I42_final_width_constant_assembly
    obtain ⟨k, hrk, hkn, hkupper, hkcase⟩ := hwidth m r ε hr hrn hε0 hε1
    refine ⟨k, hrk, hkn, hkupper, ?_⟩
    apply Real.sSup_le
    · intro z hz
      obtain ⟨V, hV, rfl⟩ := hz
      rcases hkcase with hsmall | hlarge
      · have hmoment := ((small_rank_second_moment V hV
          ⟨hr.trans hrk, hkn⟩).2 ε hε0 hε1 hr hrn)
        simpa [hsmall.2] using hmoment
      · dsimp only at hlarge
        by_cases hfull : walshCard m ≤ 4 * Nat.ceil
            ((2048 * K₀ : ℝ) * r / ε ^ 2)
        · have hkfull := (hlarge.2.1 hfull).1
          rw [hkfull, frameFailureProbability_full_sample V hV ε hε0]
          norm_num
        · have hnon : 4 * Nat.ceil
              ((2048 * K₀ : ℝ) * r / ε ^ 2) < walshCard m := by omega
          obtain ⟨hk0, hplus5, heffective, htail⟩ := hlarge.2.2 hnon
          subst k
          let k₀ : ℕ := Nat.ceil ((2048 * K₀ : ℝ) * r / ε ^ 2)
          let X : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) →
              Matrix (WalshIndex m) (Fin r) ℝ :=
            fun d ↦ transformedFrame d.1 d.2 V
          let θminus : ℝ := (1 - ε / 4) * k₀ / walshCard m
          let θplus : ℝ := (1 + ε / 4) * k₀ / walshCard m
          have hk₀eq : k₀ = Nat.ceil
              ((2048 * K₀ : ℝ) * r / ε ^ 2) := rfl
          have hk₀pos : 0 < k₀ := by
            rw [hk₀eq]
            omega
          have hnpos : (0 : ℝ) < walshCard m := by simp [walshCard]
          have hk₀posR : (0 : ℝ) < k₀ := by exact_mod_cast hk₀pos
          have hη : 0 < ε / 4 ∧ ε / 4 < 1 := by
            constructor
            · nlinarith only [hε0]
            · nlinarith only [hε1]
          have hminusFactor : 0 < 1 - ε / 4 := by
            nlinarith only [hε1]
          have hplusFactor : 0 < 1 + ε / 4 := by
            nlinarith only [hε0]
          have hθminus0 : 0 < θminus := by
            exact div_pos (mul_pos hminusFactor hk₀posR) hnpos
          have hθplus0 : 0 < θplus := by
            exact div_pos (mul_pos hplusFactor hk₀posR) hnpos
          have hθplus5 : θplus ≤ 5 / 16 := by
            simpa only [θplus, k₀] using hplus5
          have hθplusHalf : θplus ≤ 1 / 2 := hθplus5.trans (by norm_num)
          have hθorder : θminus ≤ θplus := by
            apply (div_le_div_iff_of_pos_right hnpos).2
            nlinarith only [hε0, hk₀posR]
          have hθminusHalf : θminus ≤ 1 / 2 := hθorder.trans hθplusHalf
          have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε0
          have hnθminus : (walshCard m : ℝ) * θminus =
              (1 - ε / 4) * k₀ := by
            dsimp only [θminus]
            field_simp
          have hthreequarter : (3 : ℝ) / 4 * k₀ ≤
              (walshCard m : ℝ) * θminus := by
            rw [hnθminus]
            nlinarith only [hε1, hk₀posR]
          have heffective' : (1536 * K₀ : ℝ) * r / ε ^ 2 ≤
              (3 : ℝ) / 4 * k₀ := by
            simpa only [k₀] using heffective
          have hwidthMinus : 64 * K₀ * r / (ε / 4) ^ 2 ≤
              (walshCard m : ℝ) * θminus := by
            calc
              64 * K₀ * r / (ε / 4) ^ 2 =
                  1024 * K₀ * r / ε ^ 2 := by ring
              _ ≤ 1536 * K₀ * r / ε ^ 2 := by
                apply (div_le_div_iff_of_pos_right hεsq).2
                have hnonneg : 0 ≤ (K₀ : ℝ) * r :=
                  mul_nonneg (Nat.cast_nonneg K₀) (Nat.cast_nonneg r)
                nlinarith only [hnonneg]
              _ ≤ (3 : ℝ) / 4 * k₀ := heffective'
              _ ≤ (walshCard m : ℝ) * θminus := hthreequarter
          have hwidthPlus : 64 * K₀ * r / (ε / 4) ^ 2 ≤
              (walshCard m : ℝ) * θplus := by
            exact hwidthMinus.trans
              (mul_le_mul_of_nonneg_left hθorder hnpos.le)
          let p₀ : ℕ := Nat.ceil (Real.logb 2 (3000 * r : ℝ))
          have hp₀rank : 2 * (4 * p₀ + 1) ^ 1000 ≤ r := by
            simpa only [p₀] using I41_large_rank_cutoff_arithmetic r hlarge.1
          have hminusFail : uniformBernoulliFailureProbability
              θminus (ε / 4) X ≤ 1 / 1000 := by
            simpa only [uniformBernoulliFailureProbability, signPairExpectation,
              X] using
              (bernoulli_coordinate_sampling_corollary V hV p₀ rfl hp₀rank
                (ε / 4) θminus hη ⟨hθminus0, hθminusHalf⟩ hwidthMinus)
          have hplusFail : uniformBernoulliFailureProbability
              θplus (ε / 4) X ≤ 1 / 1000 := by
            simpa only [uniformBernoulliFailureProbability, signPairExpectation,
              X] using
              (bernoulli_coordinate_sampling_corollary V hV p₀ rfl hp₀rank
                (ε / 4) θplus hη ⟨hθplus0, hθplusHalf⟩ hwidthPlus)
          have hX : ∀ d, OrthonormalFrame (X d) := by
            intro d
            exact transformedFrame_orthonormal V hV d.1 d.2
          rw [frameFailureProbability_eq_uniformFixed]
          have hfixed := fixed_size_sampling_transfer X hX ε (1 / 1000)
            ⟨hε0, hε1⟩ ⟨hr.trans hrk, hkn⟩
            (hθminusHalf.trans (by norm_num))
            (hθplusHalf.trans (by norm_num)) hminusFail hplusFail
          exact hfixed.trans (le_of_lt (by
            nlinarith only [htail]))
    · norm_num

end Problem56
