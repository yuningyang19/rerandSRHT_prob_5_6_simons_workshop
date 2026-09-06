import Problem56.FixedSizeSamplingTransfer
import Problem56.PaperV6.GeneralSamplingExpected

open scoped BigOperators Matrix

namespace Problem56.PaperV6

/- The following private helpers are byte-preserved proof text from B,
FixedSizeSamplingTransfer.lean lines15–470, in the separate PaperV6 namespace.
They were private in B; no B constant is shadowed or redefined. -/
private def transferTrueFinset {ι : Type*} [Fintype ι]
    (b : SignLayer ι) : Finset ι :=
  Finset.univ.filter fun i ↦ b i = true

private def signLayerEquiv
    {ι κ : Type*} (e : ι ≃ κ) : SignLayer ι ≃ SignLayer κ where
  toFun b := fun j ↦ b (e.symm j)
  invFun b := fun i ↦ b (e i)
  left_inv b := by funext i; simp
  right_inv b := by funext j; simp

@[simp]
private lemma signLayerEquiv_apply
    {ι κ : Type*} (e : ι ≃ κ) (b : SignLayer ι) (j : κ) :
    signLayerEquiv e b j = b (e.symm j) := rfl

private def fixedSubsetEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) : FixedSubset ι k ≃ FixedSubset κ k :=
  e.finsetCongr.subtypeEquiv fun J ↦ by simp

@[simp]
private lemma fixedSubsetEquiv_val
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) (J : FixedSubset ι k) :
    (fixedSubsetEquiv k e J).1 = J.1.map e.toEmbedding := rfl

private def couplingSpaceEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) :
    (FixedSubset ι k × SignLayer ι × SignLayer ι) ≃
      (FixedSubset κ k × SignLayer κ × SignLayer κ) :=
  (fixedSubsetEquiv k e).prodCongr
    ((signLayerEquiv e).prodCongr (signLayerEquiv e))

@[simp]
private lemma couplingSpaceEquiv_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) (J : FixedSubset ι k)
    (bminus bplus : SignLayer ι) :
    couplingSpaceEquiv k e (J, bminus, bplus) =
      (fixedSubsetEquiv k e J, signLayerEquiv e bminus,
        signLayerEquiv e bplus) := rfl

private lemma transferTrueFinset_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (b : SignLayer ι) :
    transferTrueFinset (signLayerEquiv e b) =
      (transferTrueFinset b).map e.toEmbedding := by
  ext j
  constructor
  · intro hj
    unfold transferTrueFinset at hj
    have hb : b (e.symm j) = true := (Finset.mem_filter.mp hj).2
    exact Finset.mem_map.mpr ⟨e.symm j,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    unfold transferTrueFinset at hi ⊢
    have hb : b i = true := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hb⟩

private lemma bernoulliWeight_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (θ : ℝ) (e : ι ≃ κ) (b : SignLayer ι) :
    bernoulliWeight θ (signLayerEquiv e b) = bernoulliWeight θ b := by
  classical
  unfold bernoulliWeight
  exact Equiv.prod_comp e.symm (fun i ↦ if b i then θ else 1 - θ)

private lemma sum_pair_equiv_transfer
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (eA : A ≃ B) (eC : C ≃ D) (F : B → D → ℝ) :
    (∑ a, ∑ c, F (eA a) (eC c)) = ∑ b, ∑ d, F b d := by
  calc
    _ = ∑ a, ∑ d, F (eA a) d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp eC (fun d ↦ F (eA a) d)
    _ = _ := Equiv.sum_comp eA (fun b ↦ ∑ d, F b d)

private lemma coupling_support_of_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ)
    (sample : FixedSubset ι k × SignLayer ι × SignLayer ι)
    (hsupport :
      (∀ j, (signLayerEquiv e sample.2.1) j = true →
        (signLayerEquiv e sample.2.2) j = true) ∧
      (((transferTrueFinset (signLayerEquiv e sample.2.1)).card ≤ k ∧
          k ≤ (transferTrueFinset (signLayerEquiv e sample.2.2)).card) →
        (∀ j, (signLayerEquiv e sample.2.1) j = true →
          j ∈ (fixedSubsetEquiv k e sample.1).1) ∧
        (∀ j, j ∈ (fixedSubsetEquiv k e sample.1).1 →
          (signLayerEquiv e sample.2.2) j = true))) :
    (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
      (((transferTrueFinset sample.2.1).card ≤ k ∧
          k ≤ (transferTrueFinset sample.2.2).card) →
        (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
        (∀ i, i ∈ sample.1.1 → sample.2.2 i = true)) := by
  constructor
  · intro i hi
    have hm : (signLayerEquiv e sample.2.1) (e i) = true := by simpa
    have hp := hsupport.1 (e i) hm
    simpa using hp
  · intro hbracket
    have hbracket' :
        (transferTrueFinset (signLayerEquiv e sample.2.1)).card ≤ k ∧
          k ≤ (transferTrueFinset (signLayerEquiv e sample.2.2)).card := by
      simp only [transferTrueFinset_equiv, Finset.card_map]
      exact hbracket
    obtain ⟨hm, hp⟩ := hsupport.2 hbracket'
    constructor
    · intro i hi
      have hmapped := hm (e i) (by simpa)
      simpa using hmapped
    · intro i hi
      have hmapped : e i ∈ (fixedSubsetEquiv k e sample.1).1 := by
        simp [hi]
      have hp' := hp (e i) hmapped
      simpa using hp'

private theorem uniform_key_nested_coupling_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (a : ℝ) (hk : k ≤ Fintype.card ι)
    (ha : 0 < a ∧ a < 1)
    (htheta : (1 + a) * k / Fintype.card ι ≤ 1) :
    ∃ coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ,
      (∀ sample, 0 ≤ coupling sample) ∧
      (∑ sample, coupling sample) = 1 ∧
      (∀ sample, coupling sample ≠ 0 →
        (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
        (((transferTrueFinset sample.2.1).card ≤ k ∧
            k ≤ (transferTrueFinset sample.2.2).card) →
          (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
          (∀ i, i ∈ sample.1.1 → sample.2.2 i = true))) ∧
      (∀ J, (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset ι k)) ∧
      (∀ bminus, (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
        bernoulliWeight ((1 - a) * k / Fintype.card ι) bminus) ∧
      (∀ bplus, (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
        bernoulliWeight ((1 + a) * k / Fintype.card ι) bplus) := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  obtain ⟨couplingFin, hnonneg, htotal, hsupport, hfixed, hminus, hplus⟩ :=
    uniform_key_nested_coupling n k a (by simpa [n] using hk) ha (by
      simpa [n] using htheta)
  let coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ :=
    fun sample ↦ couplingFin (couplingSpaceEquiv k e sample)
  refine ⟨coupling, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample
    exact hnonneg _
  · exact Equiv.sum_comp (couplingSpaceEquiv k e) couplingFin |>.trans htotal
  · intro sample hs
    rcases sample with ⟨J, bminus, bplus⟩
    apply coupling_support_of_equiv k e (J, bminus, bplus)
    have hsFin := hsupport (couplingSpaceEquiv k e (J, bminus, bplus)) hs
    simp only [couplingSpaceEquiv_apply] at hsFin
    refine ⟨hsFin.1, ?_⟩
    intro hbracket
    apply hsFin.2
    unfold transferTrueFinset at hbracket
    exact hbracket
  · intro J
    calc
      (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
          ∑ bminusFin, ∑ bplusFin,
            couplingFin (fixedSubsetEquiv k e J, bminusFin, bplusFin) := by
        exact sum_pair_equiv_transfer (signLayerEquiv e) (signLayerEquiv e)
          (fun bminusFin bplusFin ↦
            couplingFin (fixedSubsetEquiv k e J, bminusFin, bplusFin))
      _ = 1 / Fintype.card (FixedSubset (Fin n) k) := hfixed _
      _ = 1 / Fintype.card (FixedSubset ι k) := by
        congr 2
        exact Fintype.card_congr (fixedSubsetEquiv k e).symm
  · intro bminus
    calc
      (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
          ∑ JFin, ∑ bplusFin,
            couplingFin (JFin, signLayerEquiv e bminus, bplusFin) := by
        exact sum_pair_equiv_transfer (fixedSubsetEquiv k e) (signLayerEquiv e)
          (fun JFin bplusFin ↦
            couplingFin (JFin, signLayerEquiv e bminus, bplusFin))
      _ = bernoulliWeight ((1 - a) * k / n) (signLayerEquiv e bminus) :=
        hminus _
      _ = bernoulliWeight ((1 - a) * k / Fintype.card ι) bminus := by
        simpa [n] using bernoulliWeight_equiv
          ((1 - a) * (k : ℝ) / (n : ℝ)) e bminus
  · intro bplus
    calc
      (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
          ∑ JFin, ∑ bminusFin,
            couplingFin (JFin, bminusFin, signLayerEquiv e bplus) := by
        exact sum_pair_equiv_transfer (fixedSubsetEquiv k e) (signLayerEquiv e)
          (fun JFin bminusFin ↦
            couplingFin (JFin, bminusFin, signLayerEquiv e bplus))
      _ = bernoulliWeight ((1 + a) * k / n) (signLayerEquiv e bplus) :=
        hplus _
      _ = bernoulliWeight ((1 + a) * k / Fintype.card ι) bplus := by
        simpa [n] using bernoulliWeight_equiv
          ((1 + a) * (k : ℝ) / (n : ℝ)) e bplus

private lemma weighted_fixed_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ)
    (hfixed : ∀ J, (∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset ι k))
    (f : FixedSubset ι k → ℝ) :
    (∑ J, ∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus) * f J) =
      ∑ J, (1 / Fintype.card (FixedSubset ι k)) * f J := by
  apply Finset.sum_congr rfl
  intro J _
  calc
    _ = (∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus)) * f J := by
      simp_rw [Finset.sum_mul]
    _ = _ := by rw [hfixed J]

private lemma weighted_minus_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (θ : ℝ)
    (coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ)
    (hminus : ∀ bminus, (∑ J, ∑ bplus,
      coupling (J, bminus, bplus)) = bernoulliWeight θ bminus)
    (f : SignLayer ι → ℝ) :
    (∑ J, ∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus) * f bminus) =
      ∑ bminus, bernoulliWeight θ bminus * f bminus := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bminus _
  calc
    _ = (∑ J, ∑ bplus,
        coupling (J, bminus, bplus)) * f bminus := by
      simp_rw [Finset.sum_mul]
    _ = _ := by rw [hminus bminus]

private lemma weighted_plus_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (θ : ℝ)
    (coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ)
    (hplus : ∀ bplus, (∑ J, ∑ bminus,
      coupling (J, bminus, bplus)) = bernoulliWeight θ bplus)
    (f : SignLayer ι → ℝ) :
    (∑ J, ∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus) * f bplus) =
      ∑ bplus, bernoulliWeight θ bplus * f bplus := by
  calc
    _ = ∑ J, ∑ bplus, ∑ bminus,
        coupling (J, bminus, bplus) * f bplus := by
      apply Finset.sum_congr rfl
      intro J _
      rw [Finset.sum_comm]
    _ = ∑ bplus, ∑ J, ∑ bminus,
        coupling (J, bminus, bplus) * f bplus := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro bplus _
      calc
        _ = (∑ J, ∑ bminus,
            coupling (J, bminus, bplus)) * f bplus := by
          simp_rw [Finset.sum_mul]
        _ = _ := by rw [hplus bplus]

private lemma bernoulliProbability_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (θ : ℝ) (event : SignLayer κ → Prop) :
    bernoulliProbability θ (fun b ↦ event (signLayerEquiv e b)) =
      bernoulliProbability θ event := by
  classical
  unfold bernoulliProbability
  calc
    (∑ b, if event (signLayerEquiv e b)
        then bernoulliWeight θ b else 0) =
        ∑ b, if event (signLayerEquiv e b)
          then bernoulliWeight θ (signLayerEquiv e b) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [bernoulliWeight_equiv θ e b]
    _ = _ := Equiv.sum_comp (signLayerEquiv e)
      (fun b ↦ if event b then bernoulliWeight θ b else 0)

private theorem binomial_tail_bounds_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ a : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ha : 0 ≤ a) :
    let μ := Fintype.card ι * θ
    bernoulliProbability θ (fun b : SignLayer ι ↦
      a ≤ ((transferTrueFinset b).card : ℝ) - μ) ≤
        Real.exp (-(a ^ 2) / (2 * μ + 2 * a / 3)) ∧
    bernoulliProbability θ (fun b : SignLayer ι ↦
      a ≤ μ - ((transferTrueFinset b).card : ℝ)) ≤
        Real.exp (-(a ^ 2) / (2 * μ)) := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  have htail := binomial_tail_bounds n θ a hθ ha
  dsimp only at htail ⊢
  constructor
  · calc
      bernoulliProbability θ (fun b : SignLayer ι ↦
          a ≤ ((transferTrueFinset b).card : ℝ) -
            (Fintype.card ι : ℝ) * θ) =
          bernoulliProbability θ (fun b : SignLayer (Fin n) ↦
            a ≤ ((transferTrueFinset b).card : ℝ) - (n : ℝ) * θ) := by
        rw [← bernoulliProbability_equiv e θ]
        congr 1
        funext b
        rw [transferTrueFinset_equiv, Finset.card_map]
      _ ≤ _ := htail.1
  · calc
      bernoulliProbability θ (fun b : SignLayer ι ↦
          a ≤ (Fintype.card ι : ℝ) * θ -
            ((transferTrueFinset b).card : ℝ)) =
          bernoulliProbability θ (fun b : SignLayer (Fin n) ↦
            a ≤ (n : ℝ) * θ - ((transferTrueFinset b).card : ℝ)) := by
        rw [← bernoulliProbability_equiv e θ]
        congr 1
        funext b
        rw [transferTrueFinset_equiv, Finset.card_map]
      _ ≤ _ := htail.2

private lemma bernoulliProbability_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (p q : SignLayer ι → Prop) (hpq : ∀ b, p b → q b) :
    bernoulliProbability θ p ≤ bernoulliProbability θ q := by
  classical
  unfold bernoulliProbability
  apply Finset.sum_le_sum
  intro b _
  by_cases hp : p b
  · simp [hp, hpq b hp]
  · by_cases hq : q b
    · simp [hp, hq, bernoulliWeight_nonneg θ hθ b]
    · simp [hp, hq]

private theorem fixed_size_count_tail_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card ι)
    (hthetaMinus : (1 - ε / 4) * k / Fintype.card ι ≤ 1)
    (hthetaPlus : (1 + ε / 4) * k / Fintype.card ι ≤ 1) :
    bernoulliProbability ((1 - ε / 4) * k / Fintype.card ι)
        (fun b : SignLayer ι ↦ k < (transferTrueFinset b).card) ≤
          Real.exp (-(ε ^ 2 * k / 48)) ∧
    bernoulliProbability ((1 + ε / 4) * k / Fintype.card ι)
        (fun b : SignLayer ι ↦ (transferTrueFinset b).card < k) ≤
          Real.exp (-(ε ^ 2 * k / 48)) := by
  classical
  let θminus : ℝ := (1 - ε / 4) * (k : ℝ) /
    (Fintype.card ι : ℝ)
  let θplus : ℝ := (1 + ε / 4) * (k : ℝ) /
    (Fintype.card ι : ℝ)
  let a : ℝ := (ε / 4) * (k : ℝ)
  let μminus : ℝ := (Fintype.card ι : ℝ) * θminus
  let μplus : ℝ := (Fintype.card ι : ℝ) * θplus
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk.1
  have hcardNat : 0 < Fintype.card ι := lt_of_lt_of_le hk.1 hk.2
  have hcardReal : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  have hθminus : 0 ≤ θminus ∧ θminus ≤ 1 := by
    constructor
    · dsimp [θminus]
      exact div_nonneg
        (mul_nonneg (by linarith [hε.2]) (Nat.cast_nonneg k))
        hcardReal.le
    · simpa [θminus] using hthetaMinus
  have hθplus : 0 ≤ θplus ∧ θplus ≤ 1 := by
    constructor
    · dsimp [θplus]
      exact div_nonneg
        (mul_nonneg (by linarith [hε.1]) (Nat.cast_nonneg k))
        hcardReal.le
    · simpa [θplus] using hthetaPlus
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by linarith [hε.1]) (Nat.cast_nonneg k)
  have hμminus : μminus = (1 - ε / 4) * (k : ℝ) := by
    dsimp [μminus, θminus]
    field_simp
  have hμplus : μplus = (1 + ε / 4) * (k : ℝ) := by
    dsimp [μplus, θplus]
    field_simp
  have htailMinus := binomial_tail_bounds_fintype
    (ι := ι) θminus a hθminus ha
  have htailPlus := binomial_tail_bounds_fintype
    (ι := ι) θplus a hθplus ha
  dsimp only at htailMinus htailPlus
  constructor
  · calc
      bernoulliProbability θminus
          (fun b : SignLayer ι ↦ k < (transferTrueFinset b).card) ≤
          bernoulliProbability θminus (fun b : SignLayer ι ↦
            a ≤ ((transferTrueFinset b).card : ℝ) - μminus) := by
        apply bernoulliProbability_mono θminus hθminus
        intro b hb
        have hbReal : (k : ℝ) < ((transferTrueFinset b).card : ℝ) := by
          exact_mod_cast hb
        dsimp [a]
        rw [hμminus]
        linarith
      _ ≤ Real.exp (-(a ^ 2) /
          (2 * μminus + 2 * a / 3)) := htailMinus.1
      _ ≤ Real.exp (-(ε ^ 2 * k / 48)) := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < 2 * μminus + 2 * a / 3 := by
          rw [hμminus]
          dsimp [a]
          have hfac : 0 < 1 - ε / 4 := by linarith
          have haPos : 0 < ε / 4 * (k : ℝ) :=
            mul_pos (by linarith) hkReal
          positivity
        have hratio : ε ^ 2 * (k : ℝ) / 48 ≤
            a ^ 2 / (2 * μminus + 2 * a / 3) := by
          rw [le_div_iff₀ hden]
          rw [hμminus]
          dsimp [a]
          field_simp
          nlinarith [sq_pos_of_pos hε.1, sq_pos_of_pos hkReal]
        simpa only [neg_div] using neg_le_neg hratio
  · calc
      bernoulliProbability θplus
          (fun b : SignLayer ι ↦ (transferTrueFinset b).card < k) ≤
          bernoulliProbability θplus (fun b : SignLayer ι ↦
            a ≤ μplus - ((transferTrueFinset b).card : ℝ)) := by
        apply bernoulliProbability_mono θplus hθplus
        intro b hb
        have hbReal : ((transferTrueFinset b).card : ℝ) < (k : ℝ) := by
          exact_mod_cast hb
        dsimp [a]
        rw [hμplus]
        linarith
      _ ≤ Real.exp (-(a ^ 2) / (2 * μplus)) := htailPlus.2
      _ ≤ Real.exp (-(ε ^ 2 * k / 48)) := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < 2 * μplus := by
          rw [hμplus]
          have hfac : 0 < 1 + ε / 4 := by linarith
          positivity
        have hratio : ε ^ 2 * (k : ℝ) / 48 ≤
            a ^ 2 / (2 * μplus) := by
          rw [le_div_iff₀ hden]
          rw [hμplus]
          dsimp [a]
          field_simp
          nlinarith [sq_pos_of_pos hε.1, sq_pos_of_pos hkReal]
        simpa only [neg_div] using neg_le_neg hratio


/-- The old finite coupling proof yields a pointwise inequality with the two
marginal errors kept separate. Ω has no finiteness assumption. -/
theorem sampling_pointwise {Ω α : Type*} [Fintype α] [DecidableEq α]
    {r k : ℕ} (X : Ω → Matrix α (Fin r) ℝ)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hthetaMinus : (1 - ε / 4) * k / Fintype.card α ≤ 1)
    (hthetaPlus : (1 + ε / 4) * k / Fintype.card α ≤ 1) :
    ∀ ω, uniformProbability (fun J : FixedSubset α k ↦
        euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε) ≤
      bernoulliProbability ((1 - ε / 4) * k / Fintype.card α)
        (fun e ↦ euclideanOperatorNorm
          (bernoulliGram ((1 - ε / 4) * k / Fintype.card α) (X ω) e - 1) > ε / 4) +
      bernoulliProbability ((1 + ε / 4) * k / Fintype.card α)
        (fun e ↦ euclideanOperatorNorm
          (bernoulliGram ((1 + ε / 4) * k / Fintype.card α) (X ω) e - 1) > ε / 4) +
      2 * Real.exp (-(ε ^ 2 * k / 48)) := by
  classical
  let θminus : ℝ := (1 - ε / 4) * (k : ℝ) /
    (Fintype.card α : ℝ)
  let θplus : ℝ := (1 + ε / 4) * (k : ℝ) /
    (Fintype.card α : ℝ)
  let fixedBad : Ω → FixedSubset α k → Prop := fun ω J ↦
    euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε
  let minusBad : Ω → SignLayer α → Prop := fun ω b ↦
    euclideanOperatorNorm (bernoulliGram θminus (X ω) b - 1) > ε / 4
  let plusBad : Ω → SignLayer α → Prop := fun ω b ↦
    euclideanOperatorNorm (bernoulliGram θplus (X ω) b - 1) > ε / 4
  let minusCountBad : SignLayer α → Prop := fun b ↦
    k < (transferTrueFinset b).card
  let plusCountBad : SignLayer α → Prop := fun b ↦
    (transferTrueFinset b).card < k
  let fixedIndicator : Ω → FixedSubset α k → ℝ := fun ω J ↦
    if fixedBad ω J then 1 else 0
  let minusIndicator : Ω → SignLayer α → ℝ := fun ω b ↦
    if minusBad ω b then 1 else 0
  let plusIndicator : Ω → SignLayer α → ℝ := fun ω b ↦
    if plusBad ω b then 1 else 0
  let minusCountIndicator : SignLayer α → ℝ := fun b ↦
    if minusCountBad b then 1 else 0
  let plusCountIndicator : SignLayer α → ℝ := fun b ↦
    if plusCountBad b then 1 else 0
  obtain ⟨coupling, hcouplingNonneg, _hcouplingTotal, hcouplingSupport,
      hfixedMarginal, hminusMarginal, hplusMarginal⟩ :=
    uniform_key_nested_coupling_fintype k (ε / 4) hk.2
      (by constructor <;> linarith [hε.1, hε.2]) (by
        simpa using hthetaPlus)
  have hsample (ω : Ω) (J : FixedSubset α k)
      (bminus bplus : SignLayer α) :
      coupling (J, bminus, bplus) * fixedIndicator ω J ≤
        coupling (J, bminus, bplus) *
          (minusIndicator ω bminus + plusIndicator ω bplus +
            minusCountIndicator bminus + plusCountIndicator bplus) := by
    by_cases hc : coupling (J, bminus, bplus) = 0
    · simp [hc]
    have hs := hcouplingSupport (J, bminus, bplus) hc
    have hindicator : fixedIndicator ω J ≤
        minusIndicator ω bminus + plusIndicator ω bplus +
          minusCountIndicator bminus + plusCountIndicator bplus := by
      by_cases hfixedBad : fixedBad ω J
      · by_cases hminusBad : minusBad ω bminus
        · simp [fixedIndicator, minusIndicator, plusIndicator,
            minusCountIndicator, plusCountIndicator, hfixedBad, hminusBad]
          split_ifs <;> norm_num
        · by_cases hplusBad : plusBad ω bplus
          · simp [fixedIndicator, minusIndicator, plusIndicator,
              minusCountIndicator, plusCountIndicator, hfixedBad,
              hminusBad, hplusBad]
            split_ifs <;> norm_num
          · by_cases hminusCount : minusCountBad bminus
            · simp [fixedIndicator, minusIndicator, plusIndicator,
                minusCountIndicator, plusCountIndicator, hfixedBad,
                hminusBad, hplusBad, hminusCount]
              split_ifs <;> norm_num
            · by_cases hplusCount : plusCountBad bplus
              · simp [fixedIndicator, minusIndicator, plusIndicator,
                  minusCountIndicator, plusCountIndicator, hfixedBad,
                  hminusBad, hplusBad, hminusCount, hplusCount]
              · have hbracket :
                    (transferTrueFinset bminus).card ≤ k ∧
                      k ≤ (transferTrueFinset bplus).card :=
                  ⟨Nat.le_of_not_gt hminusCount,
                    Nat.le_of_not_gt hplusCount⟩
                obtain ⟨hminusInclusion, hplusInclusion⟩ := hs.2 hbracket
                have hfixedGood := sampling_sandwich_operatorNorm_conversion
                  (X ω) J bminus bplus ε hε hk
                  hminusInclusion hplusInclusion
                  (le_of_not_gt hminusBad) (le_of_not_gt hplusBad)
                exact False.elim ((not_lt_of_ge hfixedGood) hfixedBad)
      · simp [fixedIndicator, minusIndicator, plusIndicator,
          minusCountIndicator, plusCountIndicator, hfixedBad]
        split_ifs <;> norm_num
    exact mul_le_mul_of_nonneg_left hindicator
      (hcouplingNonneg (J, bminus, bplus))
  have hpoint (ω : Ω) :
      (∑ J, fixedIndicator ω J) /
          Fintype.card (FixedSubset α k) ≤
        bernoulliProbability θminus (minusBad ω) +
          bernoulliProbability θplus (plusBad ω) +
          bernoulliProbability θminus minusCountBad +
          bernoulliProbability θplus plusCountBad := by
    let Wfixed : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * fixedIndicator ω J
    let Wminus : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * minusIndicator ω bminus
    let Wplus : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * plusIndicator ω bplus
    let WminusCount : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * minusCountIndicator bminus
    let WplusCount : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * plusCountIndicator bplus
    have hfixedWeight :
        (∑ J, fixedIndicator ω J) /
            Fintype.card (FixedSubset α k) = Wfixed := by
      calc
        _ = ∑ J, (1 / Fintype.card (FixedSubset α k)) *
            fixedIndicator ω J := by
          simp_rw [div_eq_mul_inv, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro J _
          ring
        _ = Wfixed := by
          exact (weighted_fixed_marginal k coupling hfixedMarginal
            (fixedIndicator ω)).symm
    have hweighted : Wfixed ≤
        Wminus + Wplus + WminusCount + WplusCount := by
      calc
        Wfixed ≤ ∑ J, ∑ bminus, ∑ bplus,
            coupling (J, bminus, bplus) *
              (minusIndicator ω bminus + plusIndicator ω bplus +
                minusCountIndicator bminus +
                plusCountIndicator bplus) := by
          dsimp only [Wfixed]
          apply Finset.sum_le_sum
          intro J _
          apply Finset.sum_le_sum
          intro bminus _
          apply Finset.sum_le_sum
          intro bplus _
          exact hsample ω J bminus bplus
        _ = Wminus + Wplus + WminusCount + WplusCount := by
          dsimp only [Wminus, Wplus, WminusCount, WplusCount]
          simp_rw [mul_add, Finset.sum_add_distrib]
    have hWminus : Wminus =
        bernoulliProbability θminus (minusBad ω) := by
      dsimp only [Wminus]
      simpa [minusIndicator, bernoulliProbability] using
        weighted_minus_marginal k θminus coupling hminusMarginal
          (minusIndicator ω)
    have hWplus : Wplus =
        bernoulliProbability θplus (plusBad ω) := by
      dsimp only [Wplus]
      simpa [plusIndicator, bernoulliProbability] using
        weighted_plus_marginal k θplus coupling hplusMarginal
          (plusIndicator ω)
    have hWminusCount : WminusCount =
        bernoulliProbability θminus minusCountBad := by
      dsimp only [WminusCount]
      calc
        _ = ∑ bminus, bernoulliWeight θminus bminus *
            minusCountIndicator bminus :=
          weighted_minus_marginal k θminus coupling hminusMarginal
            minusCountIndicator
        _ = _ := by
          unfold bernoulliProbability
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : minusCountBad b <;>
            simp [minusCountIndicator, hb]
    have hWplusCount : WplusCount =
        bernoulliProbability θplus plusCountBad := by
      dsimp only [WplusCount]
      calc
        _ = ∑ bplus, bernoulliWeight θplus bplus *
            plusCountIndicator bplus :=
          weighted_plus_marginal k θplus coupling hplusMarginal
            plusCountIndicator
        _ = _ := by
          unfold bernoulliProbability
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : plusCountBad b <;>
            simp [plusCountIndicator, hb]
    calc
      _ = Wfixed := hfixedWeight
      _ ≤ Wminus + Wplus + WminusCount + WplusCount := hweighted
      _ = _ := by rw [hWminus, hWplus, hWminusCount, hWplusCount]
  have htail := fixed_size_count_tail_bounds k ε hε hk
    hthetaMinus hthetaPlus
  intro ω
  have hb := hpoint ω
  have hf : uniformProbability (fixedBad ω) =
      (∑ J, fixedIndicator ω J) / Fintype.card (FixedSubset α k) := by
    unfold uniformProbability
    rw [← Finset.sum_boole]
  rw [← hf] at hb
  have hm : bernoulliProbability θminus minusCountBad ≤
      Real.exp (-(ε ^ 2 * k / 48)) := htail.1
  have hp : bernoulliProbability θplus plusCountBad ≤
      Real.exp (-(ε ^ 2 * k / 48)) := htail.2
  change uniformProbability (fixedBad ω) ≤
    bernoulliProbability θminus (minusBad ω) +
    bernoulliProbability θplus (plusBad ω) + 2 * Real.exp (-(ε ^ 2 * k / 48))
  linarith

end Problem56.PaperV6
