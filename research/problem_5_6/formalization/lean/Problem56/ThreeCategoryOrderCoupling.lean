import Problem56.Definitions

/-!
A source-faithful finite model for the corrected sampling coupling.

The three coordinate states represent the intervals
`[0, thetaMinus]`, `(thetaMinus, thetaPlus]`, and
`(thetaPlus, 1]`.  A separate uniform permutation supplies the order.  A
canonical admissible `k`-set is relabelled by that permutation; equivalently,
after choosing an order whose first `k` entries are the canonical set, the
random permutation makes the resulting order uniform.  The sandwich
inclusions are asserted only on the count-bracketing event.
-/

open scoped BigOperators

namespace Problem56.ThreeCategoryOrder

inductive Category where
  | lower
  | middle
  | upper
  deriving DecidableEq

instance : Fintype Category where
  elems := {.lower, .middle, .upper}
  complete c := by cases c <;> simp

def categoryWeight (thetaMinus thetaPlus : ℝ) : Category → ℝ
  | .lower => thetaMinus
  | .middle => thetaPlus - thetaMinus
  | .upper => 1 - thetaPlus

def inLower : Category → Bool
  | .lower => true
  | .middle | .upper => false

def inPlus : Category → Bool
  | .lower | .middle => true
  | .upper => false

noncomputable def assignmentWeight {ι : Type*} [Fintype ι]
    (thetaMinus thetaPlus : ℝ) (c : ι → Category) : ℝ :=
  ∏ i, categoryWeight thetaMinus thetaPlus (c i)

def lowerLayer {ι : Type*} (c : ι → Category) : SignLayer ι :=
  fun i => inLower (c i)

def plusLayer {ι : Type*} (c : ι → Category) : SignLayer ι :=
  fun i => inPlus (c i)

def trueSet {ι : Type*} [Fintype ι] (b : SignLayer ι) : Finset ι :=
  Finset.univ.filter fun i => b i = true

@[simp] theorem sum_categoryWeight (thetaMinus thetaPlus : ℝ) :
    (∑ c : Category, categoryWeight thetaMinus thetaPlus c) = 1 := by
  have huniv : (Finset.univ : Finset Category) =
      {.lower, .middle, .upper} := by
    ext c
    cases c <;> simp
  rw [show (∑ c : Category, categoryWeight thetaMinus thetaPlus c) =
      ∑ c ∈ ({.lower, .middle, .upper} : Finset Category),
        categoryWeight thetaMinus thetaPlus c by simp [← huniv]]
  simp [categoryWeight]

private theorem sum_category_explicit (f : Category → ℝ) :
    (∑ c : Category, f c) = f .lower + f .middle + f .upper := by
  have huniv : (Finset.univ : Finset Category) =
      {.lower, .middle, .upper} := by
    ext c
    cases c <;> simp
  rw [show (∑ c : Category, f c) =
      ∑ c ∈ ({.lower, .middle, .upper} : Finset Category), f c by
        simp [← huniv]]
  simp
  ring

theorem lower_coordinate_marginal (thetaMinus thetaPlus : ℝ) (b : Bool) :
    (∑ c : Category,
      if inLower c = b then categoryWeight thetaMinus thetaPlus c else 0) =
      if b then thetaMinus else 1 - thetaMinus := by
  rw [sum_category_explicit]
  cases b <;> simp [inLower, categoryWeight]

theorem plus_coordinate_marginal (thetaMinus thetaPlus : ℝ) (b : Bool) :
    (∑ c : Category,
      if inPlus c = b then categoryWeight thetaMinus thetaPlus c else 0) =
      if b then thetaPlus else 1 - thetaPlus := by
  rw [sum_category_explicit]
  cases b <;> simp [inPlus, categoryWeight]

theorem categoryWeight_nonneg (thetaMinus thetaPlus : ℝ)
    (hminus : 0 ≤ thetaMinus) (hle : thetaMinus ≤ thetaPlus)
    (hplus : thetaPlus ≤ 1) (c : Category) :
    0 ≤ categoryWeight thetaMinus thetaPlus c := by
  cases c <;> simp [categoryWeight] <;> linarith

theorem assignmentWeight_nonneg {ι : Type*} [Fintype ι]
    (thetaMinus thetaPlus : ℝ)
    (hminus : 0 ≤ thetaMinus) (hle : thetaMinus ≤ thetaPlus)
    (hplus : thetaPlus ≤ 1) (c : ι → Category) :
    0 ≤ assignmentWeight thetaMinus thetaPlus c := by
  classical
  exact Finset.prod_nonneg fun i _ =>
    categoryWeight_nonneg thetaMinus thetaPlus hminus hle hplus (c i)

theorem sum_assignmentWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thetaMinus thetaPlus : ℝ) :
    (∑ c : ι → Category, assignmentWeight thetaMinus thetaPlus c) = 1 := by
  classical
  unfold assignmentWeight
  calc
    (∑ c : ι → Category,
        ∏ i, categoryWeight thetaMinus thetaPlus (c i)) =
        ∏ _i : ι, ∑ c : Category, categoryWeight thetaMinus thetaPlus c :=
      (Fintype.prod_sum fun _i : ι =>
        fun c : Category => categoryWeight thetaMinus thetaPlus c).symm
    _ = 1 := by simp

private theorem assignment_indicator_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thetaMinus thetaPlus : ℝ) (indicator : Category → Bool)
    (c : ι → Category) (b : SignLayer ι) :
    (if (fun i => indicator (c i)) = b then
        assignmentWeight thetaMinus thetaPlus c else 0) =
      ∏ i, if indicator (c i) = b i then
        categoryWeight thetaMinus thetaPlus (c i) else 0 := by
  classical
  by_cases h : (fun i => indicator (c i)) = b
  · rw [if_pos h]
    unfold assignmentWeight
    apply Finset.prod_congr rfl
    intro i _hi
    rw [if_pos (congrFun h i)]
  · rw [if_neg h]
    have hexists : ∃ i, indicator (c i) ≠ b i := by
      by_contra hnone
      apply h
      funext i
      exact not_ne_iff.mp (not_exists.mp hnone i)
    obtain ⟨i, hi⟩ := hexists
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem lower_assignment_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thetaMinus thetaPlus : ℝ) (b : SignLayer ι) :
    (∑ c : ι → Category,
      if lowerLayer c = b then assignmentWeight thetaMinus thetaPlus c else 0) =
      bernoulliWeight thetaMinus b := by
  classical
  calc
    (∑ c : ι → Category,
      if lowerLayer c = b then assignmentWeight thetaMinus thetaPlus c else 0) =
        ∑ c : ι → Category, ∏ i,
          if inLower (c i) = b i then
            categoryWeight thetaMinus thetaPlus (c i) else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact assignment_indicator_eq_prod thetaMinus thetaPlus inLower c b
    _ = ∏ i : ι, ∑ c : Category,
          if inLower c = b i then
            categoryWeight thetaMinus thetaPlus c else 0 :=
      (Fintype.prod_sum fun i : ι => fun c : Category =>
        if inLower c = b i then
          categoryWeight thetaMinus thetaPlus c else 0).symm
    _ = bernoulliWeight thetaMinus b := by
      unfold bernoulliWeight
      apply Finset.prod_congr rfl
      intro i _hi
      exact lower_coordinate_marginal thetaMinus thetaPlus (b i)

theorem plus_assignment_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thetaMinus thetaPlus : ℝ) (b : SignLayer ι) :
    (∑ c : ι → Category,
      if plusLayer c = b then assignmentWeight thetaMinus thetaPlus c else 0) =
      bernoulliWeight thetaPlus b := by
  classical
  calc
    (∑ c : ι → Category,
      if plusLayer c = b then assignmentWeight thetaMinus thetaPlus c else 0) =
        ∑ c : ι → Category, ∏ i,
          if inPlus (c i) = b i then
            categoryWeight thetaMinus thetaPlus (c i) else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact assignment_indicator_eq_prod thetaMinus thetaPlus inPlus c b
    _ = ∏ i : ι, ∑ c : Category,
          if inPlus c = b i then
            categoryWeight thetaMinus thetaPlus c else 0 :=
      (Fintype.prod_sum fun i : ι => fun c : Category =>
        if inPlus c = b i then
          categoryWeight thetaMinus thetaPlus c else 0).symm
    _ = bernoulliWeight thetaPlus b := by
      unfold bernoulliWeight
      apply Finset.prod_congr rfl
      intro i _hi
      exact plus_coordinate_marginal thetaMinus thetaPlus (b i)

@[simp] theorem lower_subset_plus {ι : Type*} [Fintype ι]
    (c : ι → Category) :
    trueSet (lowerLayer c) ⊆ trueSet (plusLayer c) := by
  intro i hi
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  cases hci : c i <;>
    simp [lowerLayer, plusLayer, inLower, inPlus, hci] at hi ⊢

private theorem exists_canonicalSubset (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) :
    ∃ J : FixedSubset (Fin n) k,
      (trueSet (lowerLayer c)).card ≤ k →
      k ≤ (trueSet (plusLayer c)).card →
      trueSet (lowerLayer c) ⊆ J.1 ∧ J.1 ⊆ trueSet (plusLayer c) := by
  classical
  by_cases hbracket :
      (trueSet (lowerLayer c)).card ≤ k ∧
        k ≤ (trueSet (plusLayer c)).card
  · obtain ⟨J, hminusJ, hJplus, hcard⟩ :=
      Finset.exists_subsuperset_card_eq (lower_subset_plus c)
        hbracket.1 hbracket.2
    exact ⟨⟨J, hcard⟩, fun _ _ => ⟨hminusJ, hJplus⟩⟩
  · obtain ⟨J, _hJuniv, hcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
        (by simpa using hk)
    exact ⟨⟨J, hcard⟩, by aesop⟩

noncomputable def canonicalSubset (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) : FixedSubset (Fin n) k :=
  Classical.choose (exists_canonicalSubset n k hk c)

theorem canonicalSubset_sandwich (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category)
    (hminus : (trueSet (lowerLayer c)).card ≤ k)
    (hplus : k ≤ (trueSet (plusLayer c)).card) :
    trueSet (lowerLayer c) ⊆ (canonicalSubset n k hk c).1 ∧
      (canonicalSubset n k hk c).1 ⊆ trueSet (plusLayer c) :=
  Classical.choose_spec (exists_canonicalSubset n k hk c) hminus hplus

def permuteLayer {ι : Type*} (sigma : Equiv.Perm ι)
    (b : SignLayer ι) : SignLayer ι :=
  fun i => b (sigma.symm i)

def permuteCategory {ι : Type*} (sigma : Equiv.Perm ι)
    (c : ι → Category) : ι → Category :=
  fun i => c (sigma.symm i)

def permuteFixedSubset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (sigma : Equiv.Perm ι) (J : FixedSubset ι k) :
    FixedSubset ι k :=
  ⟨J.1.map sigma.toEmbedding, by simp [J.2]⟩

theorem permuteFixedSubset_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (sigma tau : Equiv.Perm ι) (J : FixedSubset ι k) :
    permuteFixedSubset k sigma (permuteFixedSubset k tau J) =
      permuteFixedSubset k (sigma * tau) J := by
  apply Subtype.ext
  ext i
  simp only [permuteFixedSubset, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by simp [Equiv.Perm.mul_apply]⟩
  · rintro ⟨j, hj, hji⟩
    exact ⟨tau j, ⟨j, hj, rfl⟩, by simpa [Equiv.Perm.mul_apply] using hji⟩

@[simp] theorem permuteFixedSubset_one {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ℕ) (J : FixedSubset ι k) :
    permuteFixedSubset k (1 : Equiv.Perm ι) J = J := by
  apply Subtype.ext
  ext i
  simp only [permuteFixedSubset, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, ha, hai⟩
    simpa using hai ▸ ha
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem permuteFixedSubset_injective {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ℕ) (sigma : Equiv.Perm ι) :
    Function.Injective (permuteFixedSubset k sigma) := by
  intro J K h
  have h' := congrArg (permuteFixedSubset k sigma.symm) h
  simpa [permuteFixedSubset_mul, ← Equiv.Perm.inv_def] using h'

@[simp] theorem lowerLayer_permute {ι : Type*} (sigma : Equiv.Perm ι)
    (c : ι → Category) :
    lowerLayer (permuteCategory sigma c) = permuteLayer sigma (lowerLayer c) := rfl

@[simp] theorem plusLayer_permute {ι : Type*} (sigma : Equiv.Perm ι)
    (c : ι → Category) :
    plusLayer (permuteCategory sigma c) = permuteLayer sigma (plusLayer c) := rfl

theorem trueSet_permute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma : Equiv.Perm ι) (b : SignLayer ι) :
    trueSet (permuteLayer sigma b) = (trueSet b).map sigma.toEmbedding := by
  ext i
  constructor
  · intro hi
    have hb : b (sigma.symm i) = true := by
      exact (Finset.mem_filter.mp hi).2
    exact Finset.mem_map.mpr ⟨sigma.symm i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    have hb : b j = true := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [permuteLayer]⟩

theorem assignmentWeight_permute {ι : Type*} [Fintype ι]
    (thetaMinus thetaPlus : ℝ) (sigma : Equiv.Perm ι)
    (c : ι → Category) :
    assignmentWeight thetaMinus thetaPlus (permuteCategory sigma c) =
      assignmentWeight thetaMinus thetaPlus c := by
  classical
  unfold assignmentWeight permuteCategory
  exact Equiv.prod_comp sigma.symm
    (fun i => categoryWeight thetaMinus thetaPlus (c i))

def categoryLayerPermEquiv {ι : Type*} (sigma : Equiv.Perm ι) :
    (ι → Category) ≃ (ι → Category) where
  toFun := permuteCategory sigma
  invFun := permuteCategory sigma.symm
  left_inv c := by
    funext i
    simp [permuteCategory]
  right_inv c := by
    funext i
    simp [permuteCategory]

theorem lower_permuted_assignment_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thetaMinus thetaPlus : ℝ) (sigma : Equiv.Perm ι)
    (b : SignLayer ι) :
    (∑ c : ι → Category,
      if lowerLayer (permuteCategory sigma c) = b then
        assignmentWeight thetaMinus thetaPlus c else 0) =
      bernoulliWeight thetaMinus b := by
  classical
  calc
    (∑ c : ι → Category,
      if lowerLayer (permuteCategory sigma c) = b then
        assignmentWeight thetaMinus thetaPlus c else 0) =
        ∑ c : ι → Category,
          if lowerLayer (permuteCategory sigma c) = b then
            assignmentWeight thetaMinus thetaPlus
              (permuteCategory sigma c) else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      split_ifs
      · exact (assignmentWeight_permute thetaMinus thetaPlus sigma c).symm
      · rfl
    _ = ∑ c : ι → Category,
        if lowerLayer c = b then
          assignmentWeight thetaMinus thetaPlus c else 0 :=
      Equiv.sum_comp (categoryLayerPermEquiv sigma)
        (fun c => if lowerLayer c = b then
          assignmentWeight thetaMinus thetaPlus c else 0)
    _ = bernoulliWeight thetaMinus b :=
      lower_assignment_marginal thetaMinus thetaPlus b

theorem plus_permuted_assignment_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thetaMinus thetaPlus : ℝ) (sigma : Equiv.Perm ι)
    (b : SignLayer ι) :
    (∑ c : ι → Category,
      if plusLayer (permuteCategory sigma c) = b then
        assignmentWeight thetaMinus thetaPlus c else 0) =
      bernoulliWeight thetaPlus b := by
  classical
  calc
    (∑ c : ι → Category,
      if plusLayer (permuteCategory sigma c) = b then
        assignmentWeight thetaMinus thetaPlus c else 0) =
        ∑ c : ι → Category,
          if plusLayer (permuteCategory sigma c) = b then
            assignmentWeight thetaMinus thetaPlus
              (permuteCategory sigma c) else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      split_ifs
      · exact (assignmentWeight_permute thetaMinus thetaPlus sigma c).symm
      · rfl
    _ = ∑ c : ι → Category,
        if plusLayer c = b then
          assignmentWeight thetaMinus thetaPlus c else 0 :=
      Equiv.sum_comp (categoryLayerPermEquiv sigma)
        (fun c => if plusLayer c = b then
          assignmentWeight thetaMinus thetaPlus c else 0)
    _ = bernoulliWeight thetaPlus b :=
      plus_assignment_marginal thetaMinus thetaPlus b

noncomputable def orderedFixedSubset (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    FixedSubset (Fin n) k :=
  permuteFixedSubset k sigma (canonicalSubset n k hk c)

def firstKSubset (n k : ℕ) (hk : k ≤ n) : FixedSubset (Fin n) k :=
  ⟨Finset.univ.map (Fin.castLEEmb hk), by simp⟩

private theorem exists_canonicalOrder (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) :
    ∃ tau : Equiv.Perm (Fin n),
      permuteFixedSubset k tau (firstKSubset n k hk) =
        canonicalSubset n k hk c := by
  obtain ⟨tau, htau⟩ := Equiv.Perm.exists_map_finset_eq
    (firstKSubset n k hk).1 (canonicalSubset n k hk c).1 (by
      rw [(firstKSubset n k hk).2, (canonicalSubset n k hk c).2])
  exact ⟨tau, Subtype.ext htau⟩

noncomputable def canonicalOrder (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) : Equiv.Perm (Fin n) :=
  Classical.choose (exists_canonicalOrder n k hk c)

theorem canonicalOrder_firstK (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) :
    permuteFixedSubset k (canonicalOrder n k hk c) (firstKSubset n k hk) =
      canonicalSubset n k hk c :=
  Classical.choose_spec (exists_canonicalOrder n k hk c)

noncomputable def outputOrder (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  sigma * canonicalOrder n k hk c

theorem orderedFixedSubset_is_firstK (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    permuteFixedSubset k (outputOrder n k hk c sigma) (firstKSubset n k hk) =
      orderedFixedSubset n k hk c sigma := by
  rw [outputOrder, ← permuteFixedSubset_mul, canonicalOrder_firstK]
  rfl

theorem outputOrder_uniform_marginal (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (tau : Equiv.Perm (Fin n)) :
    (∑ sigma : Equiv.Perm (Fin n),
      if outputOrder n k hk c sigma = tau then
        1 / Fintype.card (Equiv.Perm (Fin n)) else 0) =
      1 / Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let rho := canonicalOrder n k hk c
  let sigma0 := tau * rho.symm
  rw [Fintype.sum_eq_single sigma0]
  · simp [sigma0, rho, outputOrder, mul_assoc, ← Equiv.Perm.inv_def]
  · intro sigma hsigma
    have hne : outputOrder n k hk c sigma ≠ tau := by
      intro hout
      apply hsigma
      have hout' := congrArg (fun eta : Equiv.Perm (Fin n) => eta * rho.symm) hout
      simpa [sigma0, rho, outputOrder, mul_assoc, ← Equiv.Perm.inv_def] using hout'
    rw [if_neg hne]

theorem orderedFixedSubset_sandwich (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n))
    (hminus : (trueSet (lowerLayer c)).card ≤ k)
    (hplus : k ≤ (trueSet (plusLayer c)).card) :
    trueSet (lowerLayer (permuteCategory sigma c)) ⊆
        (orderedFixedSubset n k hk c sigma).1 ∧
      (orderedFixedSubset n k hk c sigma).1 ⊆
        trueSet (plusLayer (permuteCategory sigma c)) := by
  rw [lowerLayer_permute, plusLayer_permute,
    trueSet_permute, trueSet_permute]
  obtain ⟨hm, hp⟩ := canonicalSubset_sandwich n k hk c hminus hplus
  constructor
  · exact Finset.map_subset_map.mpr hm
  · exact Finset.map_subset_map.mpr hp

theorem permuted_count_event_iff (n k : ℕ)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    ((trueSet (lowerLayer (permuteCategory sigma c))).card ≤ k ∧
      k ≤ (trueSet (plusLayer (permuteCategory sigma c))).card) ↔
    ((trueSet (lowerLayer c)).card ≤ k ∧
      k ≤ (trueSet (plusLayer c)).card) := by
  simp [trueSet_permute]

theorem orderedFixedSubset_conditional_support (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    (∀ i, lowerLayer (permuteCategory sigma c) i = true →
      plusLayer (permuteCategory sigma c) i = true) ∧
    (((trueSet (lowerLayer (permuteCategory sigma c))).card ≤ k ∧
        k ≤ (trueSet (plusLayer (permuteCategory sigma c))).card) →
      (∀ i, lowerLayer (permuteCategory sigma c) i = true →
        i ∈ (orderedFixedSubset n k hk c sigma).1) ∧
      (∀ i, i ∈ (orderedFixedSubset n k hk c sigma).1 →
        plusLayer (permuteCategory sigma c) i = true)) := by
  constructor
  · intro i hi
    cases hci : permuteCategory sigma c i <;>
      simp [lowerLayer, plusLayer, inLower, inPlus, hci] at hi ⊢
  · intro hcount
    have hcount' := (permuted_count_event_iff n k c sigma).mp hcount
    obtain ⟨hm, hp⟩ := orderedFixedSubset_sandwich n k hk c sigma
      hcount'.1 hcount'.2
    constructor
    · intro i hi
      exact hm (by
        simpa only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and]
          using hi)
    · intro i hi
      exact (by
        simpa only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and]
          using hp hi)

noncomputable def fixedSubsetOrbitMass {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ℕ) (J0 J : FixedSubset ι k) : ℝ :=
  ∑ sigma : Equiv.Perm ι,
    if permuteFixedSubset k sigma J0 = J then
      1 / Fintype.card (Equiv.Perm ι) else 0

private theorem fixedSubsetOrbitMass_total {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ℕ) (J0 : FixedSubset ι k) :
    (∑ J, fixedSubsetOrbitMass k J0 J) = 1 := by
  classical
  let P : ℕ := Fintype.card (Equiv.Perm ι)
  have hPnat : 0 < P := Fintype.card_pos
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast hPnat.ne'
  unfold fixedSubsetOrbitMass
  rw [Finset.sum_comm]
  calc
    (∑ sigma : Equiv.Perm ι,
      ∑ J : FixedSubset ι k,
        if permuteFixedSubset k sigma J0 = J then 1 / (P : ℝ) else 0) =
        ∑ _sigma : Equiv.Perm ι, 1 / (P : ℝ) := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      rw [Fintype.sum_eq_single (permuteFixedSubset k sigma J0)]
      · simp
      · intro J hJ
        rw [if_neg (Ne.symm hJ)]
    _ = (P : ℝ) * (1 / (P : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = 1 := by field_simp

private theorem fixedSubsetOrbitMass_constant {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ℕ) (J0 J K : FixedSubset ι k) :
    fixedSubsetOrbitMass k J0 J = fixedSubsetOrbitMass k J0 K := by
  classical
  obtain ⟨tau, htauVal⟩ := Equiv.Perm.exists_map_finset_eq J.1 K.1 (by
    rw [J.2, K.2])
  have htau : permuteFixedSubset k tau J = K := Subtype.ext htauVal
  let fJ : Equiv.Perm ι → ℝ := fun sigma =>
    if permuteFixedSubset k sigma J0 = J then
      1 / Fintype.card (Equiv.Perm ι) else 0
  let fK : Equiv.Perm ι → ℝ := fun sigma =>
    if permuteFixedSubset k sigma J0 = K then
      1 / Fintype.card (Equiv.Perm ι) else 0
  have hpoint : ∀ sigma, fJ sigma = fK (tau * sigma) := by
    intro sigma
    have hiff : permuteFixedSubset k sigma J0 = J ↔
        permuteFixedSubset k (tau * sigma) J0 = K := by
      constructor
      · intro hsigma
        rw [← permuteFixedSubset_mul, hsigma, htau]
      · intro hsigma
        apply permuteFixedSubset_injective k tau
        rw [permuteFixedSubset_mul]
        simpa [htau] using hsigma
    simp only [fJ, fK]
    rw [if_congr hiff rfl rfl]
  unfold fixedSubsetOrbitMass
  calc
    (∑ sigma : Equiv.Perm ι, fJ sigma) =
        ∑ sigma : Equiv.Perm ι, fK (tau * sigma) := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      exact hpoint sigma
    _ = ∑ sigma : Equiv.Perm ι, fK sigma :=
      Equiv.sum_comp (Equiv.mulLeft tau) fK

theorem uniform_permutation_fixedSubset_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (J0 J : FixedSubset ι k) :
    fixedSubsetOrbitMass k J0 J =
      1 / Fintype.card (FixedSubset ι k) := by
  classical
  let C : ℕ := Fintype.card (FixedSubset ι k)
  have hCnat : 0 < C := Fintype.card_pos_iff.mpr ⟨J0⟩
  have hC : (C : ℝ) ≠ 0 := by exact_mod_cast hCnat.ne'
  have htotal := fixedSubsetOrbitMass_total k J0
  have hconstant :
      (∑ K, fixedSubsetOrbitMass k J0 K) =
        (C : ℝ) * fixedSubsetOrbitMass k J0 J := by
    calc
      (∑ K, fixedSubsetOrbitMass k J0 K) =
          ∑ _K : FixedSubset ι k, fixedSubsetOrbitMass k J0 J := by
        apply Finset.sum_congr rfl
        intro K _hK
        exact fixedSubsetOrbitMass_constant k J0 K J
      _ = (C : ℝ) * fixedSubsetOrbitMass k J0 J := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  apply (eq_div_iff hC).2
  rw [mul_comm]
  exact hconstant.symm.trans htotal

noncomputable def independentOrderWeight (n : ℕ)
    (thetaMinus thetaPlus : ℝ)
    (c : Fin n → Category) (_sigma : Equiv.Perm (Fin n)) : ℝ :=
  assignmentWeight thetaMinus thetaPlus c /
    Fintype.card (Equiv.Perm (Fin n))

theorem independentOrderWeight_nonneg (n : ℕ)
    (thetaMinus thetaPlus : ℝ)
    (hminus : 0 ≤ thetaMinus) (hle : thetaMinus ≤ thetaPlus)
    (hplus : thetaPlus ≤ 1)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    0 ≤ independentOrderWeight n thetaMinus thetaPlus c sigma := by
  exact div_nonneg
    (assignmentWeight_nonneg thetaMinus thetaPlus hminus hle hplus c)
    (Nat.cast_nonneg _)

theorem independentOrderWeight_total (n : ℕ)
    (thetaMinus thetaPlus : ℝ) :
    (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
      independentOrderWeight n thetaMinus thetaPlus c sigma) = 1 := by
  classical
  let P : ℕ := Fintype.card (Equiv.Perm (Fin n))
  have hPnat : 0 < P := Fintype.card_pos
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast hPnat.ne'
  calc
    (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
      independentOrderWeight n thetaMinus thetaPlus c sigma) =
        ∑ c : Fin n → Category,
          (P : ℝ) * (assignmentWeight thetaMinus thetaPlus c / (P : ℝ)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      simp only [independentOrderWeight]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = ∑ c : Fin n → Category,
        assignmentWeight thetaMinus thetaPlus c := by
      apply Finset.sum_congr rfl
      intro c _hc
      field_simp
    _ = 1 := sum_assignmentWeight thetaMinus thetaPlus

theorem generated_lower_marginal (n : ℕ)
    (thetaMinus thetaPlus : ℝ) (b : SignLayer (Fin n)) :
    (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
      if lowerLayer (permuteCategory sigma c) = b then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
      bernoulliWeight thetaMinus b := by
  classical
  let P : ℕ := Fintype.card (Equiv.Perm (Fin n))
  have hPnat : 0 < P := Fintype.card_pos
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast hPnat.ne'
  rw [Finset.sum_comm]
  calc
    (∑ sigma : Equiv.Perm (Fin n), ∑ c : Fin n → Category,
      if lowerLayer (permuteCategory sigma c) = b then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
        ∑ _sigma : Equiv.Perm (Fin n),
          bernoulliWeight thetaMinus b / (P : ℝ) := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      calc
        (∑ c : Fin n → Category,
          if lowerLayer (permuteCategory sigma c) = b then
            independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
            ∑ c : Fin n → Category,
              (if lowerLayer (permuteCategory sigma c) = b then
                assignmentWeight thetaMinus thetaPlus c else 0) / (P : ℝ) := by
          apply Finset.sum_congr rfl
          intro c _hc
          split_ifs <;> simp [independentOrderWeight, P]
        _ =
            (∑ c : Fin n → Category,
              if lowerLayer (permuteCategory sigma c) = b then
                assignmentWeight thetaMinus thetaPlus c else 0) / (P : ℝ) := by
          exact (Finset.sum_div Finset.univ
            (fun c : Fin n → Category =>
              if lowerLayer (permuteCategory sigma c) = b then
                assignmentWeight thetaMinus thetaPlus c else 0) (P : ℝ)).symm
        _ = bernoulliWeight thetaMinus b / (P : ℝ) := by
          rw [lower_permuted_assignment_marginal thetaMinus thetaPlus sigma b]
    _ = (P : ℝ) * (bernoulliWeight thetaMinus b / (P : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = bernoulliWeight thetaMinus b := by field_simp

theorem generated_plus_marginal (n : ℕ)
    (thetaMinus thetaPlus : ℝ) (b : SignLayer (Fin n)) :
    (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
      if plusLayer (permuteCategory sigma c) = b then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
      bernoulliWeight thetaPlus b := by
  classical
  let P : ℕ := Fintype.card (Equiv.Perm (Fin n))
  have hPnat : 0 < P := Fintype.card_pos
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast hPnat.ne'
  rw [Finset.sum_comm]
  calc
    (∑ sigma : Equiv.Perm (Fin n), ∑ c : Fin n → Category,
      if plusLayer (permuteCategory sigma c) = b then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
        ∑ _sigma : Equiv.Perm (Fin n),
          bernoulliWeight thetaPlus b / (P : ℝ) := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      calc
        (∑ c : Fin n → Category,
          if plusLayer (permuteCategory sigma c) = b then
            independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
            ∑ c : Fin n → Category,
              (if plusLayer (permuteCategory sigma c) = b then
                assignmentWeight thetaMinus thetaPlus c else 0) / (P : ℝ) := by
          apply Finset.sum_congr rfl
          intro c _hc
          split_ifs <;> simp [independentOrderWeight, P]
        _ =
            (∑ c : Fin n → Category,
              if plusLayer (permuteCategory sigma c) = b then
                assignmentWeight thetaMinus thetaPlus c else 0) / (P : ℝ) := by
          exact (Finset.sum_div Finset.univ
            (fun c : Fin n → Category =>
              if plusLayer (permuteCategory sigma c) = b then
                assignmentWeight thetaMinus thetaPlus c else 0) (P : ℝ)).symm
        _ = bernoulliWeight thetaPlus b / (P : ℝ) := by
          rw [plus_permuted_assignment_marginal thetaMinus thetaPlus sigma b]
    _ = (P : ℝ) * (bernoulliWeight thetaPlus b / (P : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = bernoulliWeight thetaPlus b := by field_simp

theorem generated_fixedSubset_marginal (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) (J : FixedSubset (Fin n) k) :
    (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
      if orderedFixedSubset n k hk c sigma = J then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
      1 / Fintype.card (FixedSubset (Fin n) k) := by
  classical
  calc
    (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
      if orderedFixedSubset n k hk c sigma = J then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0) =
        ∑ c : Fin n → Category,
          assignmentWeight thetaMinus thetaPlus c *
            fixedSubsetOrbitMass k (canonicalSubset n k hk c) J := by
      apply Finset.sum_congr rfl
      intro c _hc
      unfold fixedSubsetOrbitMass independentOrderWeight orderedFixedSubset
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      split_ifs <;> ring
    _ = ∑ c : Fin n → Category,
        assignmentWeight thetaMinus thetaPlus c *
          (1 / Fintype.card (FixedSubset (Fin n) k)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [uniform_permutation_fixedSubset_marginal]
    _ = (∑ c : Fin n → Category,
        assignmentWeight thetaMinus thetaPlus c) *
          (1 / Fintype.card (FixedSubset (Fin n) k)) := by
      rw [Finset.sum_mul]
    _ = 1 / Fintype.card (FixedSubset (Fin n) k) := by
      rw [sum_assignmentWeight, one_mul]

abbrev CouplingSample (n k : ℕ) :=
  FixedSubset (Fin n) k × SignLayer (Fin n) × SignLayer (Fin n)

noncomputable def generatedSample (n k : ℕ) (hk : k ≤ n)
    (c : Fin n → Category) (sigma : Equiv.Perm (Fin n)) :
    CouplingSample n k :=
  (orderedFixedSubset n k hk c sigma,
    lowerLayer (permuteCategory sigma c),
    plusLayer (permuteCategory sigma c))

noncomputable def threeCategoryOrderCoupling (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) (sample : CouplingSample n k) : ℝ :=
  ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
    if generatedSample n k hk c sigma = sample then
      independentOrderWeight n thetaMinus thetaPlus c sigma else 0

private theorem pushforward_expectation
    {A B S : Type*} [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq S] (out : A → B → S) (weight : A → B → ℝ)
    (F : S → ℝ) :
    (∑ s : S, (∑ a : A, ∑ b : B,
      if out a b = s then weight a b else 0) * F s) =
      ∑ a : A, ∑ b : B, weight a b * F (out a b) := by
  classical
  calc
    (∑ s : S, (∑ a : A, ∑ b : B,
      if out a b = s then weight a b else 0) * F s) =
        ∑ s : S, ∑ a : A, ∑ b : B,
          (if out a b = s then weight a b else 0) * F s := by
      apply Finset.sum_congr rfl
      intro s _hs
      simp_rw [Finset.sum_mul]
    _ = ∑ a : A, ∑ b : B, ∑ s : S,
        (if out a b = s then weight a b else 0) * F s := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ a : A, ∑ b : B, weight a b * F (out a b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Fintype.sum_eq_single (out a b)]
      · simp
      · intro s hs
        simp [Ne.symm hs]

theorem threeCategoryOrderCoupling_expectation (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) (F : CouplingSample n k → ℝ) :
    (∑ sample : CouplingSample n k,
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample * F sample) =
      ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          F (generatedSample n k hk c sigma) := by
  exact pushforward_expectation
    (generatedSample n k hk) (independentOrderWeight n thetaMinus thetaPlus) F

theorem threeCategoryOrderCoupling_nonneg (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ)
    (hminus : 0 ≤ thetaMinus) (hle : thetaMinus ≤ thetaPlus)
    (hplus : thetaPlus ≤ 1) (sample : CouplingSample n k) :
    0 ≤ threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample := by
  classical
  exact Finset.sum_nonneg fun c _hc => Finset.sum_nonneg fun sigma _hsigma => by
    split_ifs
    · exact independentOrderWeight_nonneg n thetaMinus thetaPlus
        hminus hle hplus c sigma
    · exact le_rfl

theorem threeCategoryOrderCoupling_total (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) :
    (∑ sample : CouplingSample n k,
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample) = 1 := by
  have h := threeCategoryOrderCoupling_expectation n k hk thetaMinus thetaPlus
    (fun _sample => 1)
  calc
    (∑ sample : CouplingSample n k,
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample) =
        ∑ sample : CouplingSample n k,
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample * 1 := by simp
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma * 1 := h
    _ = 1 := by simpa using independentOrderWeight_total n thetaMinus thetaPlus

private theorem threeCategoryOrderCoupling_has_preimage (n k : ℕ)
    (hk : k ≤ n) (thetaMinus thetaPlus : ℝ) (sample : CouplingSample n k)
    (hweight : threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample ≠ 0) :
    ∃ c : Fin n → Category, ∃ sigma : Equiv.Perm (Fin n),
      generatedSample n k hk c sigma = sample ∧
        independentOrderWeight n thetaMinus thetaPlus c sigma ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  apply hweight
  unfold threeCategoryOrderCoupling
  apply Finset.sum_eq_zero
  intro c _hc
  apply Finset.sum_eq_zero
  intro sigma _hsigma
  by_cases hout : generatedSample n k hk c sigma = sample
  · simp [hout, hnone c sigma hout]
  · simp [hout]

theorem threeCategoryOrderCoupling_support (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) (sample : CouplingSample n k)
    (hweight : threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample ≠ 0) :
    (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
      (((trueSet sample.2.1).card ≤ k ∧
          k ≤ (trueSet sample.2.2).card) →
        (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
          (∀ i, i ∈ sample.1.1 → sample.2.2 i = true)) := by
  obtain ⟨c, sigma, hout, _hsourceWeight⟩ :=
    threeCategoryOrderCoupling_has_preimage n k hk thetaMinus thetaPlus
      sample hweight
  subst sample
  exact orderedFixedSubset_conditional_support n k hk c sigma

theorem threeCategoryOrderCoupling_lower_marginal (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) (b : SignLayer (Fin n)) :
    (∑ J : FixedSubset (Fin n) k, ∑ bplus : SignLayer (Fin n),
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, b, bplus)) =
      bernoulliWeight thetaMinus b := by
  classical
  have h := threeCategoryOrderCoupling_expectation n k hk thetaMinus thetaPlus
    (fun sample => if sample.2.1 = b then 1 else 0)
  have hgenerated := generated_lower_marginal n thetaMinus thetaPlus b
  have hleft :
      (∑ sample : CouplingSample n k,
        threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample *
          (if sample.2.1 = b then 1 else 0)) =
        ∑ J : FixedSubset (Fin n) k, ∑ bplus : SignLayer (Fin n),
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, b, bplus) := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro J _hJ
    rw [Fintype.sum_eq_single b]
    · simp
    · intro b' hb'
      simp [hb']
  have hright :
      (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          (if (generatedSample n k hk c sigma).2.1 = b then 1 else 0)) =
        ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
          if lowerLayer (permuteCategory sigma c) = b then
            independentOrderWeight n thetaMinus thetaPlus c sigma else 0 := by
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro sigma _hsigma
    change independentOrderWeight n thetaMinus thetaPlus c sigma *
        (if lowerLayer (permuteCategory sigma c) = b then 1 else 0) =
      (if lowerLayer (permuteCategory sigma c) = b then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0)
    split_ifs <;> simp
  calc
    (∑ J : FixedSubset (Fin n) k, ∑ bplus : SignLayer (Fin n),
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, b, bplus)) =
        ∑ sample : CouplingSample n k,
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample *
            (if sample.2.1 = b then 1 else 0) := hleft.symm
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          (if (generatedSample n k hk c sigma).2.1 = b then 1 else 0) := h
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        if lowerLayer (permuteCategory sigma c) = b then
          independentOrderWeight n thetaMinus thetaPlus c sigma else 0 := hright
    _ = bernoulliWeight thetaMinus b := hgenerated

theorem threeCategoryOrderCoupling_plus_marginal (n k : ℕ) (hk : k ≤ n)
    (thetaMinus thetaPlus : ℝ) (b : SignLayer (Fin n)) :
    (∑ J : FixedSubset (Fin n) k, ∑ bminus : SignLayer (Fin n),
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, bminus, b)) =
      bernoulliWeight thetaPlus b := by
  classical
  have h := threeCategoryOrderCoupling_expectation n k hk thetaMinus thetaPlus
    (fun sample => if sample.2.2 = b then 1 else 0)
  have hgenerated := generated_plus_marginal n thetaMinus thetaPlus b
  have hleft :
      (∑ sample : CouplingSample n k,
        threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample *
          (if sample.2.2 = b then 1 else 0)) =
        ∑ J : FixedSubset (Fin n) k, ∑ bminus : SignLayer (Fin n),
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, bminus, b) := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro J _hJ
    apply Finset.sum_congr rfl
    intro bminus _hbminus
    rw [Fintype.sum_eq_single b]
    · simp
    · intro b' hb'
      simp [hb']
  have hright :
      (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          (if (generatedSample n k hk c sigma).2.2 = b then 1 else 0)) =
        ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
          if plusLayer (permuteCategory sigma c) = b then
            independentOrderWeight n thetaMinus thetaPlus c sigma else 0 := by
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro sigma _hsigma
    change independentOrderWeight n thetaMinus thetaPlus c sigma *
        (if plusLayer (permuteCategory sigma c) = b then 1 else 0) =
      (if plusLayer (permuteCategory sigma c) = b then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0)
    split_ifs <;> simp
  calc
    (∑ J : FixedSubset (Fin n) k, ∑ bminus : SignLayer (Fin n),
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, bminus, b)) =
        ∑ sample : CouplingSample n k,
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample *
            (if sample.2.2 = b then 1 else 0) := hleft.symm
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          (if (generatedSample n k hk c sigma).2.2 = b then 1 else 0) := h
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        if plusLayer (permuteCategory sigma c) = b then
          independentOrderWeight n thetaMinus thetaPlus c sigma else 0 := hright
    _ = bernoulliWeight thetaPlus b := hgenerated

theorem threeCategoryOrderCoupling_fixedSubset_marginal
    (n k : ℕ) (hk : k ≤ n) (thetaMinus thetaPlus : ℝ)
    (J : FixedSubset (Fin n) k) :
    (∑ bminus : SignLayer (Fin n), ∑ bplus : SignLayer (Fin n),
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, bminus, bplus)) =
      1 / Fintype.card (FixedSubset (Fin n) k) := by
  classical
  have h := threeCategoryOrderCoupling_expectation n k hk thetaMinus thetaPlus
    (fun sample => if sample.1 = J then 1 else 0)
  have hgenerated := generated_fixedSubset_marginal n k hk thetaMinus thetaPlus J
  have hleft :
      (∑ sample : CouplingSample n k,
        threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample *
          (if sample.1 = J then 1 else 0)) =
        ∑ bminus : SignLayer (Fin n), ∑ bplus : SignLayer (Fin n),
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus
            (J, bminus, bplus) := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_eq_single J]
    · simp
    · intro J' hJ'
      simp [hJ']
  have hright :
      (∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          (if (generatedSample n k hk c sigma).1 = J then 1 else 0)) =
        ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
          if orderedFixedSubset n k hk c sigma = J then
            independentOrderWeight n thetaMinus thetaPlus c sigma else 0 := by
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro sigma _hsigma
    change independentOrderWeight n thetaMinus thetaPlus c sigma *
        (if orderedFixedSubset n k hk c sigma = J then 1 else 0) =
      (if orderedFixedSubset n k hk c sigma = J then
        independentOrderWeight n thetaMinus thetaPlus c sigma else 0)
    split_ifs <;> simp
  calc
    (∑ bminus : SignLayer (Fin n), ∑ bplus : SignLayer (Fin n),
      threeCategoryOrderCoupling n k hk thetaMinus thetaPlus (J, bminus, bplus)) =
        ∑ sample : CouplingSample n k,
          threeCategoryOrderCoupling n k hk thetaMinus thetaPlus sample *
            (if sample.1 = J then 1 else 0) := hleft.symm
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        independentOrderWeight n thetaMinus thetaPlus c sigma *
          (if (generatedSample n k hk c sigma).1 = J then 1 else 0) := h
    _ = ∑ c : Fin n → Category, ∑ sigma : Equiv.Perm (Fin n),
        if orderedFixedSubset n k hk c sigma = J then
          independentOrderWeight n thetaMinus thetaPlus c sigma else 0 := hright
    _ = 1 / Fintype.card (FixedSubset (Fin n) k) := hgenerated

theorem three_category_uniform_order_coupling
    (n k : ℕ) (thetaMinus thetaPlus : ℝ) (hk : k ≤ n)
    (hminus : 0 ≤ thetaMinus) (hle : thetaMinus ≤ thetaPlus)
    (hplus : thetaPlus ≤ 1) :
    ∃ coupling : FixedSubset (Fin n) k × SignLayer (Fin n) ×
        SignLayer (Fin n) → ℝ,
      (∀ sample, 0 ≤ coupling sample) ∧
      (∑ sample, coupling sample) = 1 ∧
      (∀ sample, coupling sample ≠ 0 →
        (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
        (((Finset.univ.filter fun i => sample.2.1 i = true).card ≤ k ∧
            k ≤ (Finset.univ.filter fun i => sample.2.2 i = true).card) →
          (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
          (∀ i, i ∈ sample.1.1 → sample.2.2 i = true))) ∧
      (∀ J, (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset (Fin n) k)) ∧
      (∀ bminus, (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
        bernoulliWeight thetaMinus bminus) ∧
      (∀ bplus, (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
        bernoulliWeight thetaPlus bplus) := by
  let coupling := threeCategoryOrderCoupling n k hk thetaMinus thetaPlus
  refine ⟨coupling, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample
    exact threeCategoryOrderCoupling_nonneg n k hk thetaMinus thetaPlus
      hminus hle hplus sample
  · exact threeCategoryOrderCoupling_total n k hk thetaMinus thetaPlus
  · intro sample hweight
    simpa only [trueSet] using
      threeCategoryOrderCoupling_support n k hk thetaMinus thetaPlus
        sample hweight
  · intro J
    exact threeCategoryOrderCoupling_fixedSubset_marginal
      n k hk thetaMinus thetaPlus J
  · intro bminus
    exact threeCategoryOrderCoupling_lower_marginal
      n k hk thetaMinus thetaPlus bminus
  · intro bplus
    exact threeCategoryOrderCoupling_plus_marginal
      n k hk thetaMinus thetaPlus bplus

theorem uniform_key_nested_coupling_via_three_category
    (n k : ℕ) (alpha : ℝ) (hk : k ≤ n)
    (halpha : 0 < alpha ∧ alpha < 1)
    (htheta : (1 + alpha) * k / n ≤ 1) :
    ∃ coupling : FixedSubset (Fin n) k × SignLayer (Fin n) ×
        SignLayer (Fin n) → ℝ,
      (∀ sample, 0 ≤ coupling sample) ∧
      (∑ sample, coupling sample) = 1 ∧
      (∀ sample, coupling sample ≠ 0 →
        (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
        (((Finset.univ.filter fun i => sample.2.1 i = true).card ≤ k ∧
            k ≤ (Finset.univ.filter fun i => sample.2.2 i = true).card) →
          (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
          (∀ i, i ∈ sample.1.1 → sample.2.2 i = true))) ∧
      (∀ J, (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset (Fin n) k)) ∧
      (∀ bminus, (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
        bernoulliWeight ((1 - alpha) * k / n) bminus) ∧
      (∀ bplus, (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
        bernoulliWeight ((1 + alpha) * k / n) bplus) := by
  let thetaMinus : ℝ := (1 - alpha) * (k : ℝ) / (n : ℝ)
  let thetaPlus : ℝ := (1 + alpha) * (k : ℝ) / (n : ℝ)
  have hminus : 0 ≤ thetaMinus := by
    dsimp [thetaMinus]
    exact div_nonneg
      (mul_nonneg (by linarith [halpha.2]) (Nat.cast_nonneg k))
      (Nat.cast_nonneg n)
  have hle : thetaMinus ≤ thetaPlus := by
    dsimp [thetaMinus, thetaPlus]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith [halpha.1])
      (Nat.cast_nonneg k)
  have hplus : thetaPlus ≤ 1 := by
    simpa [thetaPlus] using htheta
  simpa [thetaMinus, thetaPlus] using
    three_category_uniform_order_coupling n k thetaMinus thetaPlus hk
      hminus hle hplus

#print axioms lower_assignment_marginal
#print axioms plus_assignment_marginal
#print axioms orderedFixedSubset_is_firstK
#print axioms outputOrder_uniform_marginal
#print axioms orderedFixedSubset_conditional_support
#print axioms threeCategoryOrderCoupling_fixedSubset_marginal
#print axioms uniform_key_nested_coupling_via_three_category

end Problem56.ThreeCategoryOrder
