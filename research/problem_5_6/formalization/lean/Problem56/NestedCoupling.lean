import Problem56.Definitions

/-!
An explicit finite coupling for the uniform fixed-size sample and the two
nested Bernoulli layers.  We first build a deterministic-selection coupling
with the correct Bernoulli marginals, then average it over all coordinate
permutations to make the fixed-size marginal uniform.
-/

open scoped BigOperators

namespace Problem56

private def trueFinset {ι : Type*} [Fintype ι]
    (b : SignLayer ι) : Finset ι :=
  Finset.univ.filter fun i ↦ b i = true

private def nestedSigns {ι : Type*} (bminus bplus : SignLayer ι) : Prop :=
  ∀ i, bminus i = true → bplus i = true

private def nestedCoordinateWeight
    (θminus θplus : ℝ) (bminus bplus : Bool) : ℝ :=
  if bminus then
    if bplus then θminus else 0
  else if bplus then θplus - θminus else 1 - θplus

private noncomputable def nestedSignWeight
    {ι : Type*} [Fintype ι]
    (θminus θplus : ℝ) (bminus bplus : SignLayer ι) : ℝ :=
  ∏ i, nestedCoordinateWeight θminus θplus (bminus i) (bplus i)

private lemma nestedCoordinateWeight_nonneg
    (θminus θplus : ℝ)
    (hminus : 0 ≤ θminus) (hle : θminus ≤ θplus) (hplus : θplus ≤ 1)
    (bminus bplus : Bool) :
    0 ≤ nestedCoordinateWeight θminus θplus bminus bplus := by
  cases bminus <;> cases bplus <;>
    simp [nestedCoordinateWeight] <;> linarith

private lemma nestedSignWeight_nonneg
    {ι : Type*} [Fintype ι]
    (θminus θplus : ℝ)
    (hminus : 0 ≤ θminus) (hle : θminus ≤ θplus) (hplus : θplus ≤ 1)
    (bminus bplus : SignLayer ι) :
    0 ≤ nestedSignWeight θminus θplus bminus bplus := by
  classical
  exact Finset.prod_nonneg fun i _ ↦
    nestedCoordinateWeight_nonneg θminus θplus hminus hle hplus _ _

private lemma nestedSignWeight_support
    {ι : Type*} [Fintype ι]
    (θminus θplus : ℝ) (bminus bplus : SignLayer ι)
    (hweight : nestedSignWeight θminus θplus bminus bplus ≠ 0) :
    nestedSigns bminus bplus := by
  classical
  intro i hi
  by_contra hp
  have hpfalse : bplus i = false := by
    cases h : bplus i <;> simp_all
  apply hweight
  rw [nestedSignWeight]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    simp [nestedCoordinateWeight, hi, hpfalse])

private lemma sum_nestedSignWeight_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θminus θplus : ℝ) (bminus : SignLayer ι) :
    (∑ bplus : SignLayer ι,
      nestedSignWeight θminus θplus bminus bplus) =
      bernoulliWeight θminus bminus := by
  classical
  unfold nestedSignWeight bernoulliWeight
  calc
    (∑ bplus : SignLayer ι,
        ∏ i, nestedCoordinateWeight θminus θplus (bminus i) (bplus i)) =
        ∏ i : ι, ∑ bplus : Bool,
          nestedCoordinateWeight θminus θplus (bminus i) bplus :=
      (Fintype.prod_sum fun i : ι ↦ fun bplus : Bool ↦
        nestedCoordinateWeight θminus θplus (bminus i) bplus).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      cases bminus i <;> simp [nestedCoordinateWeight]

private lemma sum_nestedSignWeight_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θminus θplus : ℝ) (bplus : SignLayer ι) :
    (∑ bminus : SignLayer ι,
      nestedSignWeight θminus θplus bminus bplus) =
      bernoulliWeight θplus bplus := by
  classical
  unfold nestedSignWeight bernoulliWeight
  calc
    (∑ bminus : SignLayer ι,
        ∏ i, nestedCoordinateWeight θminus θplus (bminus i) (bplus i)) =
        ∏ i : ι, ∑ bminus : Bool,
          nestedCoordinateWeight θminus θplus bminus (bplus i) :=
      (Fintype.prod_sum fun i : ι ↦ fun bminus : Bool ↦
        nestedCoordinateWeight θminus θplus bminus (bplus i)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      cases bplus i <;> simp [nestedCoordinateWeight]

private lemma sum_bernoulliWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ℝ) :
    (∑ b : SignLayer ι, bernoulliWeight θ b) = 1 := by
  classical
  unfold bernoulliWeight
  calc
    (∑ b : SignLayer ι, ∏ i, if b i then θ else 1 - θ) =
        ∏ _i : ι, ∑ b : Bool, if b then θ else 1 - θ :=
      (Fintype.prod_sum fun _i : ι ↦ fun b : Bool ↦
        if b then θ else 1 - θ).symm
    _ = 1 := by simp

private lemma trueFinset_subset_of_nested
    {ι : Type*} [Fintype ι]
    {bminus bplus : SignLayer ι} (h : nestedSigns bminus bplus) :
    trueFinset bminus ⊆ trueFinset bplus := by
  intro i hi
  simp only [trueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

private lemma exists_selectedSubset
    (n k : ℕ) (hk : k ≤ n)
    (bminus bplus : SignLayer (Fin n)) :
    ∃ J : FixedSubset (Fin n) k,
      nestedSigns bminus bplus →
      (trueFinset bminus).card ≤ k →
      k ≤ (trueFinset bplus).card →
      trueFinset bminus ⊆ J.1 ∧ J.1 ⊆ trueFinset bplus := by
  classical
  by_cases hnest : nestedSigns bminus bplus
  · by_cases hbracket :
        (trueFinset bminus).card ≤ k ∧ k ≤ (trueFinset bplus).card
    · obtain ⟨J, hmJ, hJp, hJcard⟩ :=
        Finset.exists_subsuperset_card_eq
          (trueFinset_subset_of_nested hnest) hbracket.1 hbracket.2
      exact ⟨⟨J, hJcard⟩, fun _ _ _ ↦ ⟨hmJ, hJp⟩⟩
    · obtain ⟨J, hJuniv, hJcard⟩ :=
        Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
          (by simpa using hk)
      exact ⟨⟨J, hJcard⟩, by aesop⟩
  · obtain ⟨J, hJuniv, hJcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
        (by simpa using hk)
    exact ⟨⟨J, hJcard⟩, by aesop⟩

private noncomputable def selectedSubset
    (n k : ℕ) (hk : k ≤ n)
    (bminus bplus : SignLayer (Fin n)) : FixedSubset (Fin n) k :=
  Classical.choose (exists_selectedSubset n k hk bminus bplus)

private lemma selectedSubset_spec
    (n k : ℕ) (hk : k ≤ n)
    (bminus bplus : SignLayer (Fin n))
    (hnest : nestedSigns bminus bplus)
    (hminus : (trueFinset bminus).card ≤ k)
    (hplus : k ≤ (trueFinset bplus).card) :
    trueFinset bminus ⊆ (selectedSubset n k hk bminus bplus).1 ∧
      (selectedSubset n k hk bminus bplus).1 ⊆ trueFinset bplus :=
  Classical.choose_spec (exists_selectedSubset n k hk bminus bplus)
    hnest hminus hplus

private noncomputable def baseCoupling
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ)
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)) : ℝ :=
  if sample.1 = selectedSubset n k hk sample.2.1 sample.2.2 then
    nestedSignWeight θminus θplus sample.2.1 sample.2.2
  else 0

private lemma sum_baseCoupling_fixedSubset
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ)
    (bminus bplus : SignLayer (Fin n)) :
    (∑ J : FixedSubset (Fin n) k,
      baseCoupling n k hk θminus θplus (J, bminus, bplus)) =
      nestedSignWeight θminus θplus bminus bplus := by
  classical
  rw [Fintype.sum_eq_single (selectedSubset n k hk bminus bplus)]
  · simp [baseCoupling]
  · intro J hJ
    simp [baseCoupling, hJ]

private lemma baseCoupling_nonneg
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ)
    (hminus : 0 ≤ θminus) (hle : θminus ≤ θplus) (hplus : θplus ≤ 1)
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)) :
    0 ≤ baseCoupling n k hk θminus θplus sample := by
  classical
  simp only [baseCoupling]
  split_ifs
  · exact nestedSignWeight_nonneg θminus θplus hminus hle hplus _ _
  · exact le_rfl

private lemma baseCoupling_support
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ)
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n))
    (hweight : baseCoupling n k hk θminus θplus sample ≠ 0) :
    nestedSigns sample.2.1 sample.2.2 ∧
      (((trueFinset sample.2.1).card ≤ k ∧
          k ≤ (trueFinset sample.2.2).card) →
        trueFinset sample.2.1 ⊆ sample.1.1 ∧
          sample.1.1 ⊆ trueFinset sample.2.2) := by
  classical
  have hJ : sample.1 = selectedSubset n k hk sample.2.1 sample.2.2 := by
    by_contra hne
    simp [baseCoupling, hne] at hweight
  have hnestedWeight :
      nestedSignWeight θminus θplus sample.2.1 sample.2.2 ≠ 0 := by
    simpa [baseCoupling, hJ] using hweight
  have hnest := nestedSignWeight_support θminus θplus
    sample.2.1 sample.2.2 hnestedWeight
  refine ⟨hnest, ?_⟩
  rintro ⟨hminus, hplus⟩
  have hs := selectedSubset_spec n k hk sample.2.1 sample.2.2
    hnest hminus hplus
  simpa [hJ] using hs

private lemma baseCoupling_total
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ) :
    (∑ sample : FixedSubset (Fin n) k × SignLayer (Fin n) ×
        SignLayer (Fin n),
      baseCoupling n k hk θminus θplus sample) = 1 := by
  classical
  simp only [Fintype.sum_prod_type]
  calc
    (∑ J : FixedSubset (Fin n) k,
      ∑ bminus : SignLayer (Fin n), ∑ bplus : SignLayer (Fin n),
        baseCoupling n k hk θminus θplus (J, bminus, bplus)) =
        ∑ bminus : SignLayer (Fin n), ∑ bplus : SignLayer (Fin n),
          ∑ J : FixedSubset (Fin n) k,
          baseCoupling n k hk θminus θplus (J, bminus, bplus) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro bminus _
      rw [Finset.sum_comm]
    _ = ∑ bminus : SignLayer (Fin n), ∑ bplus : SignLayer (Fin n),
        nestedSignWeight θminus θplus bminus bplus := by
      simp_rw [sum_baseCoupling_fixedSubset]
    _ = 1 := by
      simp_rw [sum_nestedSignWeight_right]
      exact sum_bernoulliWeight θminus

private lemma baseCoupling_minus_marginal
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ)
    (bminus : SignLayer (Fin n)) :
    (∑ J, ∑ bplus,
      baseCoupling n k hk θminus θplus (J, bminus, bplus)) =
      bernoulliWeight θminus bminus := by
  classical
  calc
    (∑ J : FixedSubset (Fin n) k, ∑ bplus : SignLayer (Fin n),
        baseCoupling n k hk θminus θplus (J, bminus, bplus)) =
        ∑ bplus : SignLayer (Fin n), ∑ J : FixedSubset (Fin n) k,
          baseCoupling n k hk θminus θplus (J, bminus, bplus) := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [sum_baseCoupling_fixedSubset]
      exact sum_nestedSignWeight_right θminus θplus bminus

private lemma baseCoupling_plus_marginal
    (n k : ℕ) (hk : k ≤ n) (θminus θplus : ℝ)
    (bplus : SignLayer (Fin n)) :
    (∑ J, ∑ bminus,
      baseCoupling n k hk θminus θplus (J, bminus, bplus)) =
      bernoulliWeight θplus bplus := by
  classical
  calc
    (∑ J : FixedSubset (Fin n) k, ∑ bminus : SignLayer (Fin n),
        baseCoupling n k hk θminus θplus (J, bminus, bplus)) =
        ∑ bminus : SignLayer (Fin n), ∑ J : FixedSubset (Fin n) k,
          baseCoupling n k hk θminus θplus (J, bminus, bplus) := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [sum_baseCoupling_fixedSubset]
      exact sum_nestedSignWeight_left θminus θplus bplus

private def signPermEquiv {ι : Type*} (σ : Equiv.Perm ι) :
    SignLayer ι ≃ SignLayer ι where
  toFun b := fun i ↦ b (σ.symm i)
  invFun b := fun i ↦ b (σ i)
  left_inv b := by
    funext i
    simp
  right_inv b := by
    funext i
    simp

@[simp]
private lemma signPermEquiv_apply
    {ι : Type*} (σ : Equiv.Perm ι) (b : SignLayer ι) (i : ι) :
    signPermEquiv σ b i = b (σ.symm i) := rfl

private def fixedSubsetPermEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (σ : Equiv.Perm ι) :
    FixedSubset ι k ≃ FixedSubset ι k :=
  σ.finsetCongr.subtypeEquiv fun J ↦ by simp

@[simp]
private lemma fixedSubsetPermEquiv_val
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (σ : Equiv.Perm ι) (J : FixedSubset ι k) :
    (fixedSubsetPermEquiv k σ J).1 = J.1.map σ.toEmbedding := rfl

private def couplingSamplePermEquiv
    (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    (FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)) ≃
      (FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)) :=
  (fixedSubsetPermEquiv k σ).prodCongr
    ((signPermEquiv σ).prodCongr (signPermEquiv σ))

@[simp]
private lemma couplingSamplePermEquiv_apply
    (n k : ℕ) (σ : Equiv.Perm (Fin n))
    (J : FixedSubset (Fin n) k)
    (bminus bplus : SignLayer (Fin n)) :
    couplingSamplePermEquiv n k σ (J, bminus, bplus) =
      (fixedSubsetPermEquiv k σ J,
        signPermEquiv σ bminus, signPermEquiv σ bplus) := rfl

private lemma signPermEquiv_mul
    {ι : Type*} (σ τ : Equiv.Perm ι) (b : SignLayer ι) :
    signPermEquiv σ (signPermEquiv τ b) = signPermEquiv (σ * τ) b := by
  funext i
  simp only [signPermEquiv_apply]
  rw [← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def,
    mul_inv_rev, Equiv.Perm.mul_apply]

private lemma fixedSubsetPermEquiv_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (σ τ : Equiv.Perm ι) (J : FixedSubset ι k) :
    fixedSubsetPermEquiv k σ (fixedSubsetPermEquiv k τ J) =
      fixedSubsetPermEquiv k (σ * τ) J := by
  apply Subtype.ext
  apply Finset.ext
  intro i
  simp
  rw [← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def,
    mul_inv_rev, Equiv.Perm.mul_apply]

private lemma couplingSamplePermEquiv_mul
    (n k : ℕ) (σ τ : Equiv.Perm (Fin n))
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)) :
    couplingSamplePermEquiv n k σ (couplingSamplePermEquiv n k τ sample) =
      couplingSamplePermEquiv n k (σ * τ) sample := by
  rcases sample with ⟨J, bminus, bplus⟩
  simp only [couplingSamplePermEquiv_apply, fixedSubsetPermEquiv_mul,
    signPermEquiv_mul]

private lemma nestedSignWeight_permute
    {ι : Type*} [Fintype ι]
    (θminus θplus : ℝ) (σ : Equiv.Perm ι)
    (bminus bplus : SignLayer ι) :
    nestedSignWeight θminus θplus
        (signPermEquiv σ bminus) (signPermEquiv σ bplus) =
      nestedSignWeight θminus θplus bminus bplus := by
  classical
  unfold nestedSignWeight
  exact Equiv.prod_comp σ.symm
    (fun i ↦ nestedCoordinateWeight θminus θplus (bminus i) (bplus i))

private lemma bernoulliWeight_permute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ℝ) (σ : Equiv.Perm ι) (b : SignLayer ι) :
    bernoulliWeight θ (signPermEquiv σ b) = bernoulliWeight θ b := by
  classical
  unfold bernoulliWeight
  exact Equiv.prod_comp σ.symm (fun i ↦ if b i then θ else 1 - θ)

private lemma trueFinset_permute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (b : SignLayer ι) :
    trueFinset (signPermEquiv σ b) =
      (trueFinset b).map σ.toEmbedding := by
  ext i
  constructor
  · intro hi
    unfold trueFinset at hi
    have hb : b (σ.symm i) = true := (Finset.mem_filter.mp hi).2
    exact Finset.mem_map.mpr ⟨σ.symm i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    unfold trueFinset at hj ⊢
    have hb : b j = true := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hb⟩

private lemma nestedSigns_permute_iff
    {ι : Type*} (σ : Equiv.Perm ι) (bminus bplus : SignLayer ι) :
    nestedSigns (signPermEquiv σ bminus) (signPermEquiv σ bplus) ↔
      nestedSigns bminus bplus := by
  constructor
  · intro h i hi
    have hm : signPermEquiv σ bminus (σ i) = true := by simpa
    have hp := h (σ i) hm
    simpa using hp
  · intro h i hi
    exact h (σ.symm i) hi

private lemma fixedSubset_mem_permute_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (σ : Equiv.Perm ι) (J : FixedSubset ι k) (i : ι) :
    i ∈ (fixedSubsetPermEquiv k σ J).1 ↔ σ.symm i ∈ J.1 := by
  simp

private lemma supportProperty_permute_iff
    (n k : ℕ) (σ : Equiv.Perm (Fin n))
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)) :
    (nestedSigns
        (couplingSamplePermEquiv n k σ sample).2.1
        (couplingSamplePermEquiv n k σ sample).2.2 ∧
      (((trueFinset (couplingSamplePermEquiv n k σ sample).2.1).card ≤ k ∧
          k ≤ (trueFinset (couplingSamplePermEquiv n k σ sample).2.2).card) →
        trueFinset (couplingSamplePermEquiv n k σ sample).2.1 ⊆
            (couplingSamplePermEquiv n k σ sample).1.1 ∧
          (couplingSamplePermEquiv n k σ sample).1.1 ⊆
            trueFinset (couplingSamplePermEquiv n k σ sample).2.2)) ↔
    (nestedSigns sample.2.1 sample.2.2 ∧
      (((trueFinset sample.2.1).card ≤ k ∧
          k ≤ (trueFinset sample.2.2).card) →
        trueFinset sample.2.1 ⊆ sample.1.1 ∧
          sample.1.1 ⊆ trueFinset sample.2.2)) := by
  rcases sample with ⟨J, bminus, bplus⟩
  simp only [couplingSamplePermEquiv_apply]
  rw [nestedSigns_permute_iff]
  simp_rw [trueFinset_permute]
  simp only [Finset.card_map]
  constructor
  · rintro ⟨hnest, hsupport⟩
    refine ⟨hnest, fun hbracket ↦ ?_⟩
    obtain ⟨hm, hp⟩ := hsupport hbracket
    constructor
    · intro i hi
      have himage : σ i ∈ (trueFinset bminus).map σ.toEmbedding := by simp [hi]
      have hJimage := hm himage
      simpa using hJimage
    · intro i hi
      have hJimage : σ i ∈ (J.1.map σ.toEmbedding) := by simp [hi]
      have hpimage := hp hJimage
      simpa using hpimage
  · rintro ⟨hnest, hsupport⟩
    refine ⟨hnest, fun hbracket ↦ ?_⟩
    obtain ⟨hm, hp⟩ := hsupport hbracket
    constructor
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_map.mpr ⟨j, hm hj, rfl⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_map.mpr ⟨j, hp hj, rfl⟩

private noncomputable def symmetrizedCoupling
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), base (couplingSamplePermEquiv n k σ sample)) /
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

private lemma perm_card_pos (n : ℕ) :
    0 < Fintype.card (Equiv.Perm (Fin n)) :=
  Fintype.card_pos

private lemma fintype_sum_div
    {A : Type*} [Fintype A] (f : A → ℝ) (d : ℝ) :
    (∑ a, f a / d) = (∑ a, f a) / d :=
  (Finset.sum_div Finset.univ f d).symm

private lemma symmetrizedCoupling_nonneg
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (hbase : ∀ sample, 0 ≤ base sample)
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n)) :
    0 ≤ symmetrizedCoupling n k base sample := by
  unfold symmetrizedCoupling
  exact div_nonneg (Finset.sum_nonneg fun σ _ ↦ hbase _) (by positivity)

private lemma symmetrizedCoupling_support
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (hbase : ∀ sample, base sample ≠ 0 →
      nestedSigns sample.2.1 sample.2.2 ∧
        (((trueFinset sample.2.1).card ≤ k ∧
            k ≤ (trueFinset sample.2.2).card) →
          trueFinset sample.2.1 ⊆ sample.1.1 ∧
            sample.1.1 ⊆ trueFinset sample.2.2))
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n))
    (hweight : symmetrizedCoupling n k base sample ≠ 0) :
    nestedSigns sample.2.1 sample.2.2 ∧
      (((trueFinset sample.2.1).card ≤ k ∧
          k ≤ (trueFinset sample.2.2).card) →
        trueFinset sample.2.1 ⊆ sample.1.1 ∧
          sample.1.1 ⊆ trueFinset sample.2.2) := by
  classical
  have hexists : ∃ σ : Equiv.Perm (Fin n),
      base (couplingSamplePermEquiv n k σ sample) ≠ 0 := by
    by_contra h
    push Not at h
    apply hweight
    simp [symmetrizedCoupling, h]
  obtain ⟨σ, hσ⟩ := hexists
  exact (supportProperty_permute_iff n k σ sample).mp (hbase _ hσ)

private lemma symmetrizedCoupling_total
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (hbase : (∑ sample, base sample) = 1) :
    (∑ sample, symmetrizedCoupling n k base sample) = 1 := by
  classical
  let G : ℕ := Fintype.card (Equiv.Perm (Fin n))
  have hG : (G : ℝ) ≠ 0 := by
    exact_mod_cast (perm_card_pos n).ne'
  unfold symmetrizedCoupling
  change (∑ sample,
    (∑ σ, base (couplingSamplePermEquiv n k σ sample)) / (G : ℝ)) = 1
  rw [fintype_sum_div, Finset.sum_comm]
  have heach : ∀ σ : Equiv.Perm (Fin n),
      (∑ sample,
        base (couplingSamplePermEquiv n k σ sample)) = 1 := by
    intro σ
    calc
      _ = ∑ sample, base sample :=
        Equiv.sum_comp (couplingSamplePermEquiv n k σ) base
      _ = 1 := hbase
  simp_rw [heach]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  change ((G : ℝ) * 1) / (G : ℝ) = 1
  field_simp

private lemma symmetrizedCoupling_permute
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (τ : Equiv.Perm (Fin n))
    (sample : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n)) :
    symmetrizedCoupling n k base (couplingSamplePermEquiv n k τ sample) =
      symmetrizedCoupling n k base sample := by
  classical
  unfold symmetrizedCoupling
  congr 1
  calc
    (∑ σ : Equiv.Perm (Fin n),
        base (couplingSamplePermEquiv n k σ
          (couplingSamplePermEquiv n k τ sample))) =
        ∑ σ : Equiv.Perm (Fin n),
          base (couplingSamplePermEquiv n k (σ * τ) sample) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [couplingSamplePermEquiv_mul]
    _ = ∑ σ : Equiv.Perm (Fin n),
        base (couplingSamplePermEquiv n k σ sample) := by
      exact Equiv.sum_comp (Equiv.mulRight τ)
        (fun σ ↦ base (couplingSamplePermEquiv n k σ sample))

private lemma sum_pair_equiv
    {A B : Type*} [Fintype A] [Fintype B]
    (eA : A ≃ A) (eB : B ≃ B) (F : A → B → ℝ) :
    (∑ a, ∑ b, F (eA a) (eB b)) = ∑ a, ∑ b, F a b := by
  calc
    _ = ∑ a, ∑ b, F (eA a) b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp eB (fun b ↦ F (eA a) b)
    _ = _ := Equiv.sum_comp eA (fun a ↦ ∑ b, F a b)

private lemma sum_three_rotate
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, F a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private lemma symmetrizedCoupling_minus_marginal
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (θminus : ℝ)
    (hbase : ∀ bminus, (∑ J, ∑ bplus, base (J, bminus, bplus)) =
      bernoulliWeight θminus bminus)
    (bminus : SignLayer (Fin n)) :
    (∑ J, ∑ bplus, symmetrizedCoupling n k base (J, bminus, bplus)) =
      bernoulliWeight θminus bminus := by
  classical
  let G : ℕ := Fintype.card (Equiv.Perm (Fin n))
  have hG : (G : ℝ) ≠ 0 := by
    exact_mod_cast (perm_card_pos n).ne'
  unfold symmetrizedCoupling
  simp_rw [fintype_sum_div]
  rw [sum_three_rotate]
  have heach : ∀ σ : Equiv.Perm (Fin n),
      (∑ J, ∑ bplus,
        base (fixedSubsetPermEquiv k σ J,
          signPermEquiv σ bminus, signPermEquiv σ bplus)) =
        bernoulliWeight θminus bminus := by
    intro σ
    calc
      _ = ∑ J, ∑ bplus,
          base (J, signPermEquiv σ bminus, bplus) := by
        exact sum_pair_equiv (fixedSubsetPermEquiv k σ) (signPermEquiv σ)
          (fun J bplus ↦ base (J, signPermEquiv σ bminus, bplus))
      _ = bernoulliWeight θminus (signPermEquiv σ bminus) :=
        hbase _
      _ = _ := bernoulliWeight_permute θminus σ bminus
  simp_rw [couplingSamplePermEquiv_apply, heach]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  change ((G : ℝ) * bernoulliWeight θminus bminus) / (G : ℝ) = _
  field_simp

private lemma symmetrizedCoupling_plus_marginal
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (θplus : ℝ)
    (hbase : ∀ bplus, (∑ J, ∑ bminus, base (J, bminus, bplus)) =
      bernoulliWeight θplus bplus)
    (bplus : SignLayer (Fin n)) :
    (∑ J, ∑ bminus, symmetrizedCoupling n k base (J, bminus, bplus)) =
      bernoulliWeight θplus bplus := by
  classical
  let G : ℕ := Fintype.card (Equiv.Perm (Fin n))
  have hG : (G : ℝ) ≠ 0 := by
    exact_mod_cast (perm_card_pos n).ne'
  unfold symmetrizedCoupling
  simp_rw [fintype_sum_div]
  rw [sum_three_rotate]
  have heach : ∀ σ : Equiv.Perm (Fin n),
      (∑ J, ∑ bminus,
        base (fixedSubsetPermEquiv k σ J,
          signPermEquiv σ bminus, signPermEquiv σ bplus)) =
        bernoulliWeight θplus bplus := by
    intro σ
    calc
      _ = ∑ J, ∑ bminus,
          base (J, bminus, signPermEquiv σ bplus) := by
        exact sum_pair_equiv (fixedSubsetPermEquiv k σ) (signPermEquiv σ)
          (fun J bminus ↦ base (J, bminus, signPermEquiv σ bplus))
      _ = bernoulliWeight θplus (signPermEquiv σ bplus) :=
        hbase _
      _ = _ := bernoulliWeight_permute θplus σ bplus
  simp_rw [couplingSamplePermEquiv_apply, heach]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  change ((G : ℝ) * bernoulliWeight θplus bplus) / (G : ℝ) = _
  field_simp

private noncomputable def fixedSubsetMarginal
    (n k : ℕ)
    (coupling : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (J : FixedSubset (Fin n) k) : ℝ :=
  ∑ bminus, ∑ bplus, coupling (J, bminus, bplus)

private lemma fixedSubsetMarginal_permute
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (σ : Equiv.Perm (Fin n)) (J : FixedSubset (Fin n) k) :
    fixedSubsetMarginal n k (symmetrizedCoupling n k base)
        (fixedSubsetPermEquiv k σ J) =
      fixedSubsetMarginal n k (symmetrizedCoupling n k base) J := by
  classical
  unfold fixedSubsetMarginal
  calc
    (∑ bminus, ∑ bplus,
        symmetrizedCoupling n k base
          (fixedSubsetPermEquiv k σ J, bminus, bplus)) =
        ∑ bminus, ∑ bplus,
          symmetrizedCoupling n k base
            (fixedSubsetPermEquiv k σ J,
              signPermEquiv σ bminus, signPermEquiv σ bplus) := by
      exact (sum_pair_equiv (signPermEquiv σ) (signPermEquiv σ)
        (fun bminus bplus ↦ symmetrizedCoupling n k base
          (fixedSubsetPermEquiv k σ J, bminus, bplus))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro bminus _
      apply Finset.sum_congr rfl
      intro bplus _
      simpa only [couplingSamplePermEquiv_apply] using
        symmetrizedCoupling_permute n k base σ (J, bminus, bplus)

private lemma fixedSubsetPermEquiv_transitive
    (n k : ℕ) (J K : FixedSubset (Fin n) k) :
    ∃ σ : Equiv.Perm (Fin n), fixedSubsetPermEquiv k σ J = K := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq J.1 K.1 (by rw [J.2, K.2])
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  exact hσ

private lemma fixedSubsetMarginal_constant
    (n k : ℕ)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (J K : FixedSubset (Fin n) k) :
    fixedSubsetMarginal n k (symmetrizedCoupling n k base) J =
      fixedSubsetMarginal n k (symmetrizedCoupling n k base) K := by
  obtain ⟨σ, hσ⟩ := fixedSubsetPermEquiv_transitive n k J K
  have h := fixedSubsetMarginal_permute n k base σ J
  rw [hσ] at h
  exact h.symm

private lemma sum_fixedSubsetMarginal
    (n k : ℕ)
    (coupling : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ) :
    (∑ J, fixedSubsetMarginal n k coupling J) =
      ∑ sample, coupling sample := by
  simp only [fixedSubsetMarginal, Fintype.sum_prod_type]

private lemma symmetrizedCoupling_fixedSubset_marginal
    (n k : ℕ) (hk : k ≤ n)
    (base : FixedSubset (Fin n) k × SignLayer (Fin n) ×
      SignLayer (Fin n) → ℝ)
    (hbase : (∑ sample, base sample) = 1)
    (J : FixedSubset (Fin n) k) :
    (∑ bminus, ∑ bplus,
      symmetrizedCoupling n k base (J, bminus, bplus)) =
      1 / Fintype.card (FixedSubset (Fin n) k) := by
  classical
  let J₀ : FixedSubset (Fin n) k :=
    selectedSubset n k hk (fun _ ↦ false) (fun _ ↦ false)
  let C : ℕ := Fintype.card (FixedSubset (Fin n) k)
  have hCnat : 0 < C := Fintype.card_pos_iff.mpr ⟨J₀⟩
  have hC : (C : ℝ) ≠ 0 := by exact_mod_cast hCnat.ne'
  have htotal :
      (∑ K, fixedSubsetMarginal n k (symmetrizedCoupling n k base) K) = 1 := by
    rw [sum_fixedSubsetMarginal]
    exact symmetrizedCoupling_total n k base hbase
  have hconstant :
      (∑ K, fixedSubsetMarginal n k (symmetrizedCoupling n k base) K) =
        (C : ℝ) * fixedSubsetMarginal n k (symmetrizedCoupling n k base) J := by
    calc
      _ = ∑ _K : FixedSubset (Fin n) k,
          fixedSubsetMarginal n k (symmetrizedCoupling n k base) J := by
        apply Finset.sum_congr rfl
        intro K _
        exact fixedSubsetMarginal_constant n k base K J
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hmul :
      (C : ℝ) * fixedSubsetMarginal n k
        (symmetrizedCoupling n k base) J = 1 := hconstant.symm.trans htotal
  change (∑ bminus, ∑ bplus,
      symmetrizedCoupling n k base (J, bminus, bplus)) = 1 / (C : ℝ)
  apply (eq_div_iff hC).2
  rw [mul_comm]
  exact hmul

theorem uniform_key_nested_coupling (n k : ℕ) (α : ℝ)
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
  classical
  let θminus : ℝ := (1 - α) * (k : ℝ) / (n : ℝ)
  let θplus : ℝ := (1 + α) * (k : ℝ) / (n : ℝ)
  have hθminus : 0 ≤ θminus := by
    dsimp [θminus]
    exact div_nonneg
      (mul_nonneg (by linarith [hα.2]) (Nat.cast_nonneg k))
      (Nat.cast_nonneg n)
  have hθle : θminus ≤ θplus := by
    dsimp [θminus, θplus]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith [hα.1]) (Nat.cast_nonneg k)
  have hθplus : θplus ≤ 1 := by
    simpa [θplus] using htheta
  let base := baseCoupling n k hk θminus θplus
  let coupling := symmetrizedCoupling n k base
  have hbaseNonneg : ∀ sample, 0 ≤ base sample := by
    intro sample
    exact baseCoupling_nonneg n k hk θminus θplus
      hθminus hθle hθplus sample
  have hbaseSupport : ∀ sample, base sample ≠ 0 →
      nestedSigns sample.2.1 sample.2.2 ∧
        (((trueFinset sample.2.1).card ≤ k ∧
            k ≤ (trueFinset sample.2.2).card) →
          trueFinset sample.2.1 ⊆ sample.1.1 ∧
            sample.1.1 ⊆ trueFinset sample.2.2) := by
    intro sample hs
    exact baseCoupling_support n k hk θminus θplus sample hs
  have hbaseTotal : (∑ sample, base sample) = 1 :=
    baseCoupling_total n k hk θminus θplus
  refine ⟨coupling, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample
    exact symmetrizedCoupling_nonneg n k base hbaseNonneg sample
  · exact symmetrizedCoupling_total n k base hbaseTotal
  · intro sample hs
    have hsupport := symmetrizedCoupling_support n k base hbaseSupport sample hs
    refine ⟨hsupport.1, ?_⟩
    intro hbracket
    have hbracket' :
        (trueFinset sample.2.1).card ≤ k ∧
          k ≤ (trueFinset sample.2.2).card := by
      simpa only [trueFinset] using hbracket
    obtain ⟨hminus, hplus⟩ := hsupport.2 hbracket'
    constructor
    · intro i hi
      apply hminus
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hplus hi)).2
  · intro J
    exact symmetrizedCoupling_fixedSubset_marginal n k hk base hbaseTotal J
  · intro bminus
    have hbaseMinus : ∀ bminus,
        (∑ J, ∑ bplus, base (J, bminus, bplus)) =
          bernoulliWeight θminus bminus := by
      intro b
      exact baseCoupling_minus_marginal n k hk θminus θplus b
    exact symmetrizedCoupling_minus_marginal n k base θminus hbaseMinus bminus
  · intro bplus
    have hbasePlus : ∀ bplus,
        (∑ J, ∑ bminus, base (J, bminus, bplus)) =
          bernoulliWeight θplus bplus := by
      intro b
      exact baseCoupling_plus_marginal n k hk θminus θplus b
    exact symmetrizedCoupling_plus_marginal n k base θplus hbasePlus bplus

end Problem56
