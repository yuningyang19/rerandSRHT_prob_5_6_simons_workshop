import Problem56.Definitions

/-!
Finite-population second-moment arithmetic for the fixed-size sampling law.
-/

open scoped BigOperators Matrix

namespace Problem56

lemma fixedSubset_card
    {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card (FixedSubset α k) = (Fintype.card α).choose k := by
  classical
  change Fintype.card {J : Finset α // J.card = k} = _
  let e : {J : Finset α // J.card = k} ≃
      {J // J ∈ Finset.univ.powersetCard k} :=
    { toFun := fun J ↦ ⟨J.1,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, J.2⟩⟩
      invFun := fun J ↦ ⟨J.1, (Finset.mem_powersetCard.mp J.2).2⟩
      left_inv := fun J ↦ by cases J; rfl
      right_inv := fun J ↦ by cases J; rfl }
  have hc : Fintype.card {J : Finset α // J.card = k} =
      Fintype.card {J // J ∈ Finset.univ.powersetCard k} :=
    Fintype.card_congr e
  calc
    _ = Fintype.card {J // J ∈ Finset.univ.powersetCard k} := hc
    _ = (Finset.univ.powersetCard k : Finset (Finset α)).card := by
      exact Fintype.card_coe _
    _ = _ := by rw [Finset.card_powersetCard, Finset.card_univ]

lemma sum_fixedSubset_eq_powersetCard
    {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (k : ℕ) (F : Finset α → M) :
    (∑ J : FixedSubset α k, F J.1) =
      ∑ J ∈ Finset.univ.powersetCard k, F J := by
  classical
  symm
  apply Finset.sum_subtype
  intro J
  simp

lemma sum_fixedSubset_indicator_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (i : α) (c : ℝ) (hk : 1 ≤ k) :
    (∑ J : FixedSubset α k, if i ∈ J.1 then c else 0) =
      ((Fintype.card α - 1).choose (k - 1) : ℕ) * c := by
  classical
  calc
    _ = ∑ J ∈ Finset.univ.powersetCard k,
        if i ∈ J then c else 0 :=
      sum_fixedSubset_eq_powersetCard k (fun J ↦ if i ∈ J then c else 0)
    _ = ∑ J ∈ (Finset.univ.powersetCard k).filter (fun J ↦ i ∈ J), c := by
      rw [Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      norm_cast
      simpa only [Finset.card_singleton, Finset.card_univ,
        Finset.singleton_subset_iff] using Finset.card_filter_powersetCard_subset
        ({i} : Finset α) Finset.univ k (by simp) (by simpa using hk)

lemma sum_fixedSubset_indicator_mem_pair
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (i j : α) (c : ℝ) (hij : i ≠ j) (hk : 2 ≤ k) :
    (∑ J : FixedSubset α k,
        if i ∈ J.1 ∧ j ∈ J.1 then c else 0) =
      ((Fintype.card α - 2).choose (k - 2) : ℕ) * c := by
  classical
  calc
    _ = ∑ J ∈ Finset.univ.powersetCard k,
        if i ∈ J ∧ j ∈ J then c else 0 :=
      sum_fixedSubset_eq_powersetCard k
        (fun J ↦ if i ∈ J ∧ j ∈ J then c else 0)
    _ = ∑ J ∈ (Finset.univ.powersetCard k).filter
        (fun J ↦ i ∈ J ∧ j ∈ J), c := by
      rw [Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      norm_cast
      have hcard : ({i, j} : Finset α).card = 2 := by simp [hij]
      simpa only [Finset.card_univ, Finset.insert_subset_iff,
        Finset.singleton_subset_iff, hcard] using
        Finset.card_filter_powersetCard_subset
          ({i, j} : Finset α) Finset.univ k (by simp) (by simpa [hcard] using hk)

lemma card_mul_choose_pred
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    N * (N - 1).choose (k - 1) = N.choose k * k := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := N)
    (by omega)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k)
    (by omega)
  simpa [Nat.succ_eq_add_one] using Nat.add_one_mul_choose_eq N' k'

lemma card_mul_pred_mul_choose_pred_pred
    (N k : ℕ) (hN : 2 ≤ N) (hk : 2 ≤ k) :
    N * (N - 1) * (N - 2).choose (k - 2) =
      N.choose k * k * (k - 1) := by
  have hfirst := card_mul_choose_pred N k (by omega) (by omega)
  have hsecond := card_mul_choose_pred (N - 1) (k - 1) (by omega) (by omega)
  have hsecond' :
      (N - 1) * (N - 2).choose (k - 2) =
        (N - 1).choose (k - 1) * (k - 1) := by
    have hNsub : N - 1 - 1 = N - 2 := by omega
    have hksub : k - 1 - 1 = k - 2 := by omega
    simpa only [hNsub, hksub] using hsecond
  calc
    N * (N - 1) * (N - 2).choose (k - 2) =
        N * ((N - 1) * (N - 2).choose (k - 2)) := by ring
    _ = N * ((N - 1).choose (k - 1) * (k - 1)) := by rw [hsecond']
    _ = (N * (N - 1).choose (k - 1)) * (k - 1) := by ring
    _ = (N.choose k * k) * (k - 1) := by rw [hfirst]

lemma fixedSampleGram_apply_sum
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k) (p q : Fin r) :
    fixedSampleGram X J p q =
      ((Fintype.card α : ℝ) / (k : ℝ)) *
        ∑ i ∈ J.1, X i p * X i q := by
  classical
  have hPX : ∀ i,
      (coordinateProjection J * X) i q =
        if i ∈ J.1 then X i q else 0 := by
    intro i
    simp [coordinateProjection]
  rw [fixedSampleGram]
  change ((Fintype.card α : ℝ) / (k : ℝ)) *
      (X.transpose * coordinateProjection J * X) p q = _
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, hPX]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  congr 3
  ext i
  simp

lemma fixedSubset_sum_sq_expand
    {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (J : FixedSubset α k) (f : α → ℝ) :
    (∑ i ∈ J.1, f i) ^ 2 =
      ∑ i, ∑ j, if i ∈ J.1 ∧ j ∈ J.1 then f i * f j else 0 := by
  classical
  have hsum : (∑ i ∈ J.1, f i) =
      ∑ i, if i ∈ J.1 then f i else 0 := by
    rw [← Finset.sum_filter]
    congr 2
    ext i
    simp
  rw [hsum, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ∈ J.1 <;> by_cases hj : j ∈ J.1 <;>
    simp [hi, hj]

lemma sum_fixedSubset_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (f : α → ℝ) (hk : 1 ≤ k) :
    (∑ J : FixedSubset α k, ∑ i ∈ J.1, f i) =
      ((Fintype.card α - 1).choose (k - 1) : ℕ) * ∑ i, f i := by
  classical
  calc
    _ = ∑ J : FixedSubset α k, ∑ i,
        if i ∈ J.1 then f i else 0 := by
      apply Finset.sum_congr rfl
      intro J _
      rw [← Finset.sum_filter]
      congr 2
      ext i
      simp
    _ = ∑ i, ∑ J : FixedSubset α k,
        if i ∈ J.1 then f i else 0 := by rw [Finset.sum_comm]
    _ = ∑ i, ((Fintype.card α - 1).choose (k - 1) : ℕ) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_fixedSubset_indicator_mem k i (f i) hk
    _ = _ := by rw [Finset.mul_sum]

lemma sum_affine_sub_sq
    {Ω : Type*} [Fintype Ω] (A S : ℝ) (Y : Ω → ℝ) :
    (∑ ω, (A * Y ω - S) ^ 2) =
      A ^ 2 * ∑ ω, (Y ω) ^ 2 -
        2 * A * S * ∑ ω, Y ω + (Fintype.card Ω : ℝ) * S ^ 2 := by
  calc
    _ = ∑ ω, (A ^ 2 * (Y ω) ^ 2 -
        (2 * A * S) * Y ω + S ^ 2) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ]

lemma sum_fixedSubset_sum_sq_of_two_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (f : α → ℝ) (hk : 2 ≤ k) :
    (∑ J : FixedSubset α k, (∑ i ∈ J.1, f i) ^ 2) =
      ((Fintype.card α - 1).choose (k - 1) : ℕ) * ∑ i, (f i) ^ 2 +
      ((Fintype.card α - 2).choose (k - 2) : ℕ) *
        ((∑ i, f i) ^ 2 - ∑ i, (f i) ^ 2) := by
  classical
  let c1 : ℝ := ((Fintype.card α - 1).choose (k - 1) : ℕ)
  let c2 : ℝ := ((Fintype.card α - 2).choose (k - 2) : ℕ)
  calc
    _ = ∑ J : FixedSubset α k, ∑ i, ∑ j,
        if i ∈ J.1 ∧ j ∈ J.1 then f i * f j else 0 := by
      apply Finset.sum_congr rfl
      intro J _
      exact fixedSubset_sum_sq_expand J f
    _ = ∑ i, ∑ j, ∑ J : FixedSubset α k,
        if i ∈ J.1 ∧ j ∈ J.1 then f i * f j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, if i = j then c1 * (f i * f j)
        else c2 * (f i * f j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simpa [c1] using
          sum_fixedSubset_indicator_mem k i (f i * f i) (by omega)
      · simpa [c2, hij] using
          sum_fixedSubset_indicator_mem_pair k i j (f i * f j) hij hk
    _ = c1 * ∑ i, (f i) ^ 2 +
        c2 * ((∑ i, f i) ^ 2 - ∑ i, (f i) ^ 2) := by
      have hpoint (i j : α) :
          (if i = j then c1 * (f i * f j) else c2 * (f i * f j)) =
            c2 * (f i * f j) +
              if i = j then (c1 - c2) * (f i * f j) else 0 := by
        by_cases hij : i = j
        · simp [hij]
          ring
        · simp [hij]
      simp_rw [hpoint, Finset.sum_add_distrib]
      simp_rw [Fintype.sum_ite_eq]
      have hcross :
          (∑ i, ∑ j, c2 * (f i * f j)) =
            c2 * (∑ i, f i) * (∑ j, f j) := by
        calc
          _ = ∑ i, (c2 * f i) * (∑ j, f j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ i, c2 * f i) * (∑ j, f j) := by
            rw [Finset.sum_mul]
          _ = _ := by
            congr 1
            simpa using (Finset.mul_sum Finset.univ f c2).symm
      have hdiag :
          (∑ i, (c1 - c2) * (f i * f i)) =
            (c1 - c2) * ∑ i, (f i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hcross, hdiag]
      ring
    _ = _ := by rfl

lemma sum_fixedSubset_indicator_mem_pair_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) (c : ℝ) (hij : i ≠ j) :
    (∑ J : FixedSubset α 1,
        if i ∈ J.1 ∧ j ∈ J.1 then c else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro J _
  have hnot : ¬(i ∈ J.1 ∧ j ∈ J.1) := by
    intro h
    have hsub : ({i, j} : Finset α) ⊆ J.1 := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using h
    have hcard := Finset.card_le_card hsub
    have hp : ({i, j} : Finset α).card = 2 := by simp [hij]
    rw [hp, J.2] at hcard
    omega
  simp [hnot]

lemma sum_fixedSubset_sum_sq_one
    {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) :
    (∑ J : FixedSubset α 1, (∑ i ∈ J.1, f i) ^ 2) =
      ∑ i, (f i) ^ 2 := by
  classical
  calc
    _ = ∑ J : FixedSubset α 1, ∑ i, ∑ j,
        if i ∈ J.1 ∧ j ∈ J.1 then f i * f j else 0 := by
      apply Finset.sum_congr rfl
      intro J _
      exact fixedSubset_sum_sq_expand J f
    _ = ∑ i, ∑ j, ∑ J : FixedSubset α 1,
        if i ∈ J.1 ∧ j ∈ J.1 then f i * f j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, if i = j then f i * f j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simpa using sum_fixedSubset_indicator_mem 1 i (f i * f i) (by simp)
      · simpa [hij] using sum_fixedSubset_indicator_mem_pair_one i j (f i * f j) hij
    _ = _ := by
      simp_rw [Fintype.sum_ite_eq]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma fixedSubset_scalar_second_moment
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (f : α → ℝ)
    (hn : 1 < Fintype.card α) (hk₁ : 1 ≤ k)
    (hkₙ : k ≤ Fintype.card α) :
    uniformExpectation (Ω := FixedSubset α k) (fun J ↦
      (((Fintype.card α : ℝ) / (k : ℝ)) *
        (∑ i ∈ J.1, f i) - ∑ i, f i) ^ 2) =
      ((Fintype.card α - k : ℕ) : ℝ) /
        ((k : ℝ) * (Fintype.card α - 1 : ℕ)) *
        ((Fintype.card α : ℝ) * ∑ i, (f i) ^ 2 - (∑ i, f i) ^ 2) := by
  classical
  let N := Fintype.card α
  let C := N.choose k
  let c1 := (N - 1).choose (k - 1)
  let S : ℝ := ∑ i, f i
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hNmpos : 0 < ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < N - 1)
  have hCpos : 0 < (C : ℝ) := by
    exact_mod_cast Nat.choose_pos hkₙ
  have hNmkcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
    apply Nat.cast_sub
    simpa [N] using hkₙ
  have hNmcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hkmcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk₁]
    norm_num
  have hNsubpos : 0 < (N : ℝ) - 1 := by rwa [← hNmcast]
  have hNm1ne : -1 + (N : ℝ) ≠ 0 := by linarith
  rw [uniformExpectation]
  rw [sum_affine_sub_sq]
  rw [sum_fixedSubset_sum k f hk₁, fixedSubset_card]
  change
    (((N : ℝ) / (k : ℝ)) ^ 2 *
          (∑ J : FixedSubset α k, (∑ i ∈ J.1, f i) ^ 2) -
        2 * ((N : ℝ) / (k : ℝ)) * S * ((c1 : ℝ) * S) +
        (C : ℝ) * S ^ 2) /
      (C : ℝ) = _
  rw [show (Fintype.card α : ℝ) = (N : ℝ) by rfl,
    show ((Fintype.card α - k : ℕ) : ℝ) = ((N - k : ℕ) : ℝ) by rfl,
    show ((Fintype.card α - 1 : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) by rfl,
    hNmkcast, hNmcast]
  by_cases hkone : k = 1
  · subst k
    rw [sum_fixedSubset_sum_sq_one]
    dsimp [N, C, c1, S]
    have hcardm1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by
      simpa [N] using hNsubpos.ne'
    rw [Nat.choose_zero_right]
    simp only [Nat.choose_one_right, Nat.cast_one]
    field_simp [hNmpos.ne', hNsubpos.ne', hNm1ne, hNpos.ne']
    ring
  · have hk2 : 2 ≤ k := by omega
    rw [sum_fixedSubset_sum_sq_of_two_le k f hk2]
    let c2 := (N - 2).choose (k - 2)
    have hc1nat := card_mul_choose_pred N k (by omega) hk₁
    have hc2nat := card_mul_pred_mul_choose_pred_pred N k (by omega) hk2
    have hc1 : (c1 : ℝ) = (C : ℝ) * (k : ℝ) / (N : ℝ) := by
      rw [eq_div_iff hNpos.ne']
      calc
        (c1 : ℝ) * (N : ℝ) = (N : ℝ) * (c1 : ℝ) := by ring
        _ = (C : ℝ) * (k : ℝ) := by exact_mod_cast hc1nat
    have hc2 : (c2 : ℝ) =
        (C : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) /
          ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) := by
      rw [eq_div_iff (mul_pos hNpos hNmpos).ne']
      calc
        (c2 : ℝ) * ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) =
            (N : ℝ) * ((N - 1 : ℕ) : ℝ) * (c2 : ℝ) := by ring
        _ = (C : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
          exact_mod_cast hc2nat
    change
      (((N : ℝ) / (k : ℝ)) ^ 2 *
            ((c1 : ℝ) * ∑ i, (f i) ^ 2 +
              (c2 : ℝ) * (S ^ 2 - ∑ i, (f i) ^ 2)) -
          2 * ((N : ℝ) / (k : ℝ)) * S * ((c1 : ℝ) * S) +
          (C : ℝ) * S ^ 2) /
        (C : ℝ) = _
    rw [hc1, hc2]
    rw [hNmcast, hkmcast]
    dsimp [N, C, S] at *
    field_simp [hCpos.ne', hkpos.ne', hNpos.ne', hNmpos.ne', hNsubpos.ne']
    ring

lemma orthonormalFrame_sum_mul
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X) (p q : Fin r) :
    (∑ i, X i p * X i q) = if p = q then 1 else 0 := by
  have hpq := congrFun (congrFun hX p) q
  simpa [OrthonormalFrame, Matrix.mul_apply, Matrix.one_apply] using hpq

private lemma finitePopulation_uniformExpectation_sum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (F : Ω → ι → ℝ) :
    uniformExpectation (fun ω ↦ ∑ i, F ω i) =
      ∑ i, uniformExpectation (fun ω ↦ F ω i) := by
  rw [uniformExpectation]
  simp_rw [uniformExpectation]
  rw [Finset.sum_comm, Finset.sum_div]

lemma sum_pair_product_sq
    {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ p, ∑ q, (x p * x q) ^ 2) = (∑ j, (x j) ^ 2) ^ 2 := by
  calc
    _ = ∑ p, (x p) ^ 2 * ∑ q, (x q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = (∑ p, (x p) ^ 2) * ∑ q, (x q) ^ 2 := by
      rw [Finset.sum_mul]
    _ = _ := by rw [pow_two]

lemma sum_matrix_entry_product_sq
    {α : Type*} [Fintype α] {r : ℕ} (X : Matrix α (Fin r) ℝ) :
    (∑ p, ∑ q, ∑ i, (X i p * X i q) ^ 2) =
      ∑ i, (∑ j, (X i j) ^ 2) ^ 2 := by
  calc
    _ = ∑ p, ∑ i, ∑ q, (X i p * X i q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ p, ∑ q, (X i p * X i q) ^ 2 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_pair_product_sq (fun p ↦ X i p)

lemma sum_sum_mul_left
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (F : ι → κ → ℝ) :
    (∑ i, ∑ j, c * F i j) = c * ∑ i, ∑ j, F i j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma sum_matrix_entry_variance_kernel
    {α : Type*} [Fintype α] {r : ℕ} [DecidableEq (Fin r)]
    (X : Matrix α (Fin r) ℝ) :
    Finset.sum (Finset.univ : Finset (Fin r)) (fun p ↦
      Finset.sum (Finset.univ : Finset (Fin r)) (fun q ↦
        (Fintype.card α : ℝ) * ∑ i, (X i p * X i q) ^ 2 -
          (if p = q then (1 : ℝ) else 0) ^ 2)) =
      (Fintype.card α : ℝ) * ∑ i, (∑ j, (X i j) ^ 2) ^ 2 - r := by
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_sum_mul_left, sum_matrix_entry_product_sq]
  simp

lemma fixedSampleGram_entry_second_moment
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X)
    (hn : 1 < Fintype.card α) (hk₁ : 1 ≤ k)
    (hkₙ : k ≤ Fintype.card α) (p q : Fin r) :
    uniformExpectation (Ω := FixedSubset α k) (fun J ↦
      ((fixedSampleGram X J - 1) p q) ^ 2) =
      ((Fintype.card α - k : ℕ) : ℝ) /
        ((k : ℝ) * (Fintype.card α - 1 : ℕ)) *
        ((Fintype.card α : ℝ) *
          ∑ i, (X i p * X i q) ^ 2 -
          (if p = q then 1 else 0) ^ 2) := by
  have hscalar := fixedSubset_scalar_second_moment k
    (fun i ↦ X i p * X i q) hn hk₁ hkₙ
  simpa [Matrix.sub_apply, Matrix.one_apply, fixedSampleGram_apply_sum,
    orthonormalFrame_sum_mul X hX p q] using hscalar

theorem finite_population_second_moment_identity
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X)
    (hn : 1 < Fintype.card α) (hk₁ : 1 ≤ k) (hkₙ : k ≤ Fintype.card α) :
    uniformExpectation (Ω := FixedSubset α k) (fun J ↦
      frobeniusNormSq (fixedSampleGram X J - 1)) =
      ((Fintype.card α - k : ℕ) : ℝ) /
        ((k : ℝ) * (Fintype.card α - 1 : ℕ)) *
        ((Fintype.card α : ℝ) * ∑ i, (∑ j, (X i j) ^ 2) ^ 2 - r) := by
  classical
  rw [show (fun J : FixedSubset α k ↦
      frobeniusNormSq (fixedSampleGram X J - 1)) =
      (fun J ↦ ∑ p, ∑ q, ((fixedSampleGram X J - 1) p q) ^ 2) by
    funext J
    rfl]
  rw [finitePopulation_uniformExpectation_sum]
  simp_rw [finitePopulation_uniformExpectation_sum]
  simp_rw [fixedSampleGram_entry_second_moment X hX hn hk₁ hkₙ]
  rw [sum_sum_mul_left]
  congr 1
  exact sum_matrix_entry_variance_kernel X

end Problem56
