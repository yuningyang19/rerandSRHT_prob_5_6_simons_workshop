import Problem56.Definitions

/-!
Finite-product Chernoff arithmetic for the fixed Bernoulli law used by the
frozen sampling statement.  The proof stays with the repository's finite-sum
probability definition.
-/

open scoped BigOperators

namespace Problem56

theorem bernoulliWeight_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (e : SignLayer α) :
    0 ≤ bernoulliWeight θ e := by
  unfold bernoulliWeight
  exact Finset.prod_nonneg fun i _ ↦ by
    by_cases hi : e i <;> simp [hi, hθ.1, hθ.2]

theorem bernoulli_count_eq_sum_indicator
    {α : Type*} [Fintype α] [DecidableEq α]
    (e : SignLayer α) :
    ((Finset.univ.filter fun i ↦ e i).card : ℝ) =
      ∑ i, if e i then (1 : ℝ) else 0 := by
  rw [Finset.natCast_card_filter]

theorem bernoulliWeight_mul_exp_count
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ t : ℝ) (e : SignLayer α) :
    bernoulliWeight θ e *
        Real.exp (t * ((Finset.univ.filter fun i ↦ e i).card : ℝ)) =
      ∏ i, if e i then θ * Real.exp t else 1 - θ := by
  rw [bernoulliWeight, bernoulli_count_eq_sum_indicator]
  rw [Finset.mul_sum, Real.exp_sum]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : e i <;> simp [hi]

theorem bernoulli_exp_count_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ t : ℝ) :
    (∑ e : SignLayer α, bernoulliWeight θ e *
        Real.exp (t * ((Finset.univ.filter fun i ↦ e i).card : ℝ))) =
      (1 - θ + θ * Real.exp t) ^ Fintype.card α := by
  simp_rw [bernoulliWeight_mul_exp_count]
  calc
    (∑ e : SignLayer α,
        ∏ i, if e i = true then θ * Real.exp t else 1 - θ) =
        ∏ i : α, ∑ b : Bool,
          if b = true then θ * Real.exp t else 1 - θ :=
      (Fintype.prod_sum
        (fun _ : α ↦ fun b : Bool ↦
          if b = true then θ * Real.exp t else 1 - θ)).symm
    _ = (1 - θ + θ * Real.exp t) ^ Fintype.card α := by
      simp [add_comm]

theorem bernoulliProbability_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ℝ) (event : SignLayer α → Prop) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    bernoulliProbability θ event ≤ 1 := by
  classical
  have hmass : (∑ e : SignLayer α, bernoulliWeight θ e) = 1 := by
    have h := bernoulli_exp_count_sum (α := α) θ 0
    simpa using h
  rw [bernoulliProbability, ← hmass]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : event e
  · simp [he]
  · simp [he, bernoulliWeight_nonneg θ hθ e]

theorem bernoulli_centered_exp_moment_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ t : ℝ) :
    (∑ e : SignLayer α, bernoulliWeight θ e *
        Real.exp (t *
          (((Finset.univ.filter fun i ↦ e i).card : ℝ) -
            (Fintype.card α : ℝ) * θ))) =
      Real.exp (-t * ((Fintype.card α : ℝ) * θ)) *
        (1 - θ + θ * Real.exp t) ^ Fintype.card α := by
  calc
    _ = ∑ e : SignLayer α,
        Real.exp (-t * ((Fintype.card α : ℝ) * θ)) *
          (bernoulliWeight θ e *
            Real.exp (t *
              ((Finset.univ.filter fun i ↦ e i).card : ℝ))) := by
      apply Finset.sum_congr rfl
      intro e _
      have hexp :
          Real.exp (t *
              (((Finset.univ.filter fun i ↦ e i).card : ℝ) -
                (Fintype.card α : ℝ) * θ)) =
            Real.exp (-t * ((Fintype.card α : ℝ) * θ)) *
              Real.exp (t *
                ((Finset.univ.filter fun i ↦ e i).card : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ = Real.exp (-t * ((Fintype.card α : ℝ) * θ)) *
        ∑ e : SignLayer α, bernoulliWeight θ e *
          Real.exp (t *
            ((Finset.univ.filter fun i ↦ e i).card : ℝ)) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [bernoulli_exp_count_sum]

theorem bernoulli_centered_exp_moment_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ t : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    (∑ e : SignLayer α, bernoulliWeight θ e *
        Real.exp (t *
          (((Finset.univ.filter fun i ↦ e i).card : ℝ) -
            (Fintype.card α : ℝ) * θ))) ≤
      Real.exp (((Fintype.card α : ℝ) * θ) *
        (Real.exp t - 1 - t)) := by
  rw [bernoulli_centered_exp_moment_eq]
  have hbase : 0 ≤ 1 - θ + θ * Real.exp t := by
    have hexp : 0 ≤ Real.exp t := (Real.exp_pos t).le
    nlinarith
  have hbaseRewrite :
      1 - θ + θ * Real.exp t = 1 + θ * (Real.exp t - 1) := by ring
  have hbaseLe :
      1 - θ + θ * Real.exp t ≤ Real.exp (θ * (Real.exp t - 1)) := by
    rw [hbaseRewrite]
    simpa only [add_comm] using Real.add_one_le_exp (θ * (Real.exp t - 1))
  have hpow :
      (1 - θ + θ * Real.exp t) ^ Fintype.card α ≤
        Real.exp (θ * (Real.exp t - 1)) ^ Fintype.card α :=
    pow_le_pow_left₀ hbase hbaseLe _
  calc
    Real.exp (-t * ((Fintype.card α : ℝ) * θ)) *
        (1 - θ + θ * Real.exp t) ^ Fintype.card α ≤
      Real.exp (-t * ((Fintype.card α : ℝ) * θ)) *
        Real.exp (θ * (Real.exp t - 1)) ^ Fintype.card α :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (((Fintype.card α : ℝ) * θ) *
        (Real.exp t - 1 - t)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem bernoulli_upper_tail_le_exp_mul_moment
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ a μ t : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ht : 0 ≤ t) :
    bernoulliProbability θ (fun e : SignLayer α ↦
        a ≤ ((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ) ≤
      Real.exp (-t * a) *
        ∑ e : SignLayer α, bernoulliWeight θ e *
          Real.exp (t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ)) := by
  classical
  rw [bernoulliProbability, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases hevent :
      a ≤ ((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ
  · simp only [hevent, if_true]
    have harg :
        0 ≤ t *
          ((((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ) - a) :=
      mul_nonneg ht (sub_nonneg.mpr hevent)
    have hexp :
        1 ≤ Real.exp (-t * a) *
          Real.exp (t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      convert harg using 1
      all_goals ring
    have hweight := bernoulliWeight_nonneg θ hθ e
    calc
      bernoulliWeight θ e = 1 * bernoulliWeight θ e := by ring
      _ ≤ (Real.exp (-t * a) *
          Real.exp (t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ))) *
            bernoulliWeight θ e :=
        mul_le_mul_of_nonneg_right hexp hweight
      _ = Real.exp (-t * a) *
          (bernoulliWeight θ e *
            Real.exp (t *
              (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ))) := by ring
  · simp only [hevent, if_false]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (bernoulliWeight_nonneg θ hθ e) (Real.exp_pos _).le)

theorem bernoulli_upper_tail_chernoff
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ a t : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ht : 0 ≤ t) :
    bernoulliProbability θ (fun e : SignLayer α ↦
        a ≤ ((Finset.univ.filter fun i ↦ e i).card : ℝ) -
          (Fintype.card α : ℝ) * θ) ≤
      Real.exp (-t * a + ((Fintype.card α : ℝ) * θ) *
        (Real.exp t - 1 - t)) := by
  calc
    _ ≤ Real.exp (-t * a) *
        ∑ e : SignLayer α, bernoulliWeight θ e *
          Real.exp (t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) -
              (Fintype.card α : ℝ) * θ)) :=
      bernoulli_upper_tail_le_exp_mul_moment θ a
        ((Fintype.card α : ℝ) * θ) t hθ ht
    _ ≤ Real.exp (-t * a) *
        Real.exp (((Fintype.card α : ℝ) * θ) *
          (Real.exp t - 1 - t)) :=
      mul_le_mul_of_nonneg_left
        (bernoulli_centered_exp_moment_le θ t hθ) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

theorem bernoulli_lower_tail_le_exp_mul_moment
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ a μ t : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ht : 0 ≤ t) :
    bernoulliProbability θ (fun e : SignLayer α ↦
        a ≤ μ - ((Finset.univ.filter fun i ↦ e i).card : ℝ)) ≤
      Real.exp (-t * a) *
        ∑ e : SignLayer α, bernoulliWeight θ e *
          Real.exp (-t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ)) := by
  classical
  rw [bernoulliProbability, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases hevent :
      a ≤ μ - ((Finset.univ.filter fun i ↦ e i).card : ℝ)
  · simp only [hevent, if_true]
    have harg :
        0 ≤ t *
          ((μ - ((Finset.univ.filter fun i ↦ e i).card : ℝ)) - a) :=
      mul_nonneg ht (sub_nonneg.mpr hevent)
    have hexp :
        1 ≤ Real.exp (-t * a) *
          Real.exp (-t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      convert harg using 1
      all_goals ring
    have hweight := bernoulliWeight_nonneg θ hθ e
    calc
      bernoulliWeight θ e = 1 * bernoulliWeight θ e := by ring
      _ ≤ (Real.exp (-t * a) *
          Real.exp (-t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ))) *
            bernoulliWeight θ e :=
        mul_le_mul_of_nonneg_right hexp hweight
      _ = Real.exp (-t * a) *
          (bernoulliWeight θ e *
            Real.exp (-t *
              (((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ))) := by ring
  · simp only [hevent, if_false]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (bernoulliWeight_nonneg θ hθ e) (Real.exp_pos _).le)

theorem bernoulli_lower_tail_chernoff
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ a t : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ht : 0 ≤ t) :
    bernoulliProbability θ (fun e : SignLayer α ↦
        a ≤ (Fintype.card α : ℝ) * θ -
          ((Finset.univ.filter fun i ↦ e i).card : ℝ)) ≤
      Real.exp (-t * a + ((Fintype.card α : ℝ) * θ) *
        (Real.exp (-t) - 1 + t)) := by
  calc
    _ ≤ Real.exp (-t * a) *
        ∑ e : SignLayer α, bernoulliWeight θ e *
          Real.exp (-t *
            (((Finset.univ.filter fun i ↦ e i).card : ℝ) -
              (Fintype.card α : ℝ) * θ)) :=
      bernoulli_lower_tail_le_exp_mul_moment θ a
        ((Fintype.card α : ℝ) * θ) t hθ ht
    _ ≤ Real.exp (-t * a) *
        Real.exp (((Fintype.card α : ℝ) * θ) *
          (Real.exp (-t) - 1 - (-t))) :=
      mul_le_mul_of_nonneg_left
        (bernoulli_centered_exp_moment_le θ (-t) hθ) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma exp_le_rational_fourth (x : ℝ) (hx0 : 0 ≤ x) (hx3 : x < 3) :
    Real.exp x ≤ 81 / (3 - x) ^ 4 := by
  have hd : 0 < 3 - x := sub_pos.mpr hx3
  have hb := Real.exp_bound_div_one_sub_of_interval
    (x := x / 3) (by positivity) (by linarith)
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le hb 3
  calc
    Real.exp x = Real.exp (x / 3) ^ 3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (1 / (1 - x / 3)) ^ 3 := hp
    _ = 27 / (3 - x) ^ 3 := by field_simp; ring
    _ ≤ 81 / (3 - x) ^ 4 := by
      rw [div_le_div_iff₀ (pow_pos hd 3) (pow_pos hd 4)]
      nlinarith [pow_pos hd 3]

lemma exp_sub_one_sub_le_bernstein
    (t : ℝ) (ht0 : 0 ≤ t) (ht3 : t < 3) :
    Real.exp t - 1 - t ≤ 3 * t ^ 2 / (2 * (3 - t)) := by
  let d : ℝ → ℝ := (fun _ ↦ 3) - id
  let f2 : ℝ → ℝ := (fun _ ↦ 27) / d ^ 3 - Real.exp
  have hdpos : ∀ x ∈ Set.Icc (0 : ℝ) t, 0 < d x := by
    intro x hx
    dsimp [d]
    linarith [hx.2]
  have hf2deriv : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt f2 (81 / (d x) ^ 4 - Real.exp x) x := by
    intro x hx
    have hdx : d x ≠ 0 := (hdpos x hx).ne'
    have hdderiv : HasDerivAt d (-1) x := by
      exact ((hasDerivAt_const x (3 : ℝ)).sub
        (hasDerivAt_id x)).congr_deriv (by norm_num)
    have hraw := ((hasDerivAt_const x (27 : ℝ)).div (hdderiv.pow 3)
      (pow_ne_zero 3 hdx)).sub (Real.hasDerivAt_exp x)
    apply hraw.congr_deriv
    dsimp
    field_simp [hdx]
    ring
  have hf2mono : MonotoneOn f2 (Set.Icc (0 : ℝ) t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t)
    · exact continuousOn_of_forall_continuousAt fun x hx ↦
        (hf2deriv x hx).continuousAt
    · intro x hx
      exact (hf2deriv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi := interior_subset hx
      rw [(hf2deriv x hxi).deriv]
      have hexp : Real.exp x ≤ 81 / (3 - x) ^ 4 :=
        exp_le_rational_fourth x hxi.1 (lt_of_le_of_lt hxi.2 ht3)
      simpa [d] using sub_nonneg.mpr hexp
  let f1 : ℝ → ℝ :=
    (fun _ ↦ 27) / ((fun _ ↦ 2) * d ^ 2) - Real.exp - (fun _ ↦ 1 / 2)
  have hf1deriv : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt f1 (f2 x) x := by
    intro x hx
    have hdx : d x ≠ 0 := (hdpos x hx).ne'
    have hdderiv : HasDerivAt d (-1) x :=
      ((hasDerivAt_const x (3 : ℝ)).sub
        (hasDerivAt_id x)).congr_deriv (by norm_num)
    have hden := (hasDerivAt_const x (2 : ℝ)).mul (hdderiv.pow 2)
    have hraw := (((hasDerivAt_const x (27 : ℝ)).div hden
      (by simp [hdx])).sub (Real.hasDerivAt_exp x)).sub
        (hasDerivAt_const x (1 / 2 : ℝ))
    apply hraw.congr_deriv
    dsimp [f2, d]
    field_simp [hdx]
    ring
  have hf1mono : MonotoneOn f1 (Set.Icc (0 : ℝ) t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t)
    · exact continuousOn_of_forall_continuousAt fun x hx ↦
        (hf1deriv x hx).continuousAt
    · intro x hx
      exact (hf1deriv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi := interior_subset hx
      rw [(hf1deriv x hxi).deriv]
      have h := hf2mono (by simp [ht0]) hxi hxi.1
      norm_num [f2, d] at h ⊢
      linarith
  let f0 : ℝ → ℝ :=
    (fun _ ↦ 3) * id ^ 2 / ((fun _ ↦ 2) * d) - Real.exp +
      (fun _ ↦ 1) + id
  have hf0deriv : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt f0 (f1 x) x := by
    intro x hx
    have hdx : d x ≠ 0 := (hdpos x hx).ne'
    have hdderiv : HasDerivAt d (-1) x :=
      ((hasDerivAt_const x (3 : ℝ)).sub
        (hasDerivAt_id x)).congr_deriv (by norm_num)
    have hnum := (hasDerivAt_const x (3 : ℝ)).mul
      ((hasDerivAt_id x).pow 2)
    have hden := (hasDerivAt_const x (2 : ℝ)).mul hdderiv
    have hraw := ((((hnum.div hden (by simp [hdx])).sub
      (Real.hasDerivAt_exp x)).add (hasDerivAt_const x (1 : ℝ))).add
        (hasDerivAt_id x))
    apply hraw.congr_deriv
    dsimp [f1]
    field_simp [hdx]
    dsimp [d]
    ring
  have hf0mono : MonotoneOn f0 (Set.Icc (0 : ℝ) t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t)
    · exact continuousOn_of_forall_continuousAt fun x hx ↦
        (hf0deriv x hx).continuousAt
    · intro x hx
      exact (hf0deriv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi := interior_subset hx
      rw [(hf0deriv x hxi).deriv]
      have h := hf1mono (by simp [ht0]) hxi hxi.1
      norm_num [f1, d] at h ⊢
      linarith
  have h := hf0mono (by simp [ht0]) (by simp [ht0]) ht0
  norm_num [f0, d] at h ⊢
  linarith

lemma exp_neg_sub_one_add_le_half_sq (t : ℝ) (ht0 : 0 ≤ t) :
    Real.exp (-t) - 1 + t ≤ t ^ 2 / 2 := by
  let eneg : ℝ → ℝ := Real.exp ∘ Neg.neg
  have heneg : ∀ x : ℝ, HasDerivAt eneg (-Real.exp (-x)) x := by
    intro x
    exact ((Real.hasDerivAt_exp (-x)).comp x
      ((hasDerivAt_id x).neg)).congr_deriv (by ring)
  let g1 : ℝ → ℝ := id + eneg - (fun _ ↦ 1)
  have hg1deriv : ∀ x : ℝ, HasDerivAt g1 (1 - Real.exp (-x)) x := by
    intro x
    have hraw := ((hasDerivAt_id x).add (heneg x)).sub
      (hasDerivAt_const x (1 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hg1mono : MonotoneOn g1 (Set.Icc (0 : ℝ) t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t)
    · exact continuousOn_of_forall_continuousAt fun x _ ↦
        (hg1deriv x).continuousAt
    · intro x _
      exact (hg1deriv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hg1deriv x).deriv]
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by
        have hxi := interior_subset hx
        linarith [hxi.1]))
  let g0 : ℝ → ℝ :=
    (fun _ ↦ 1 / 2) * id ^ 2 - eneg + (fun _ ↦ 1) - id
  have hg0deriv : ∀ x : ℝ, HasDerivAt g0 (g1 x) x := by
    intro x
    have hraw := ((((hasDerivAt_const x (1 / 2 : ℝ)).mul
      ((hasDerivAt_id x).pow 2)).sub (heneg x)).add
        (hasDerivAt_const x (1 : ℝ))).sub (hasDerivAt_id x)
    apply hraw.congr_deriv
    norm_num [g1, eneg, Function.comp_apply, id_eq]
    ring
  have hg0mono : MonotoneOn g0 (Set.Icc (0 : ℝ) t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t)
    · exact continuousOn_of_forall_continuousAt fun x _ ↦
        (hg0deriv x).continuousAt
    · intro x _
      exact (hg0deriv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hg0deriv x).deriv]
      have h := hg1mono (by simp [ht0]) (interior_subset hx)
        (interior_subset hx).1
      norm_num [g1, eneg, Function.comp_apply, id_eq] at h ⊢
      linarith
  have h := hg0mono (by simp [ht0]) (by simp [ht0]) ht0
  norm_num [g0, eneg, Function.comp_apply, id_eq] at h ⊢
  linarith

theorem binomial_tail_bounds
    (n : ℕ) (θ a : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ha : 0 ≤ a) :
    let μ := n * θ
    bernoulliProbability (α := Fin n) θ (fun e ↦
      a ≤ ((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ) ≤
        Real.exp (-(a ^ 2) / (2 * μ + 2 * a / 3)) ∧
    bernoulliProbability (α := Fin n) θ (fun e ↦
      a ≤ μ - ((Finset.univ.filter fun i ↦ e i).card : ℝ)) ≤
        Real.exp (-(a ^ 2) / (2 * μ)) := by
  let μ : ℝ := (n : ℝ) * θ
  change
    bernoulliProbability (α := Fin n) θ (fun e ↦
      a ≤ ((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ) ≤
        Real.exp (-(a ^ 2) / (2 * μ + 2 * a / 3)) ∧
    bernoulliProbability (α := Fin n) θ (fun e ↦
      a ≤ μ - ((Finset.univ.filter fun i ↦ e i).card : ℝ)) ≤
        Real.exp (-(a ^ 2) / (2 * μ))
  have hμ0 : 0 ≤ μ := by
    dsimp [μ]
    exact mul_nonneg (Nat.cast_nonneg n) hθ.1
  by_cases hμ : μ = 0
  · constructor
    · by_cases ha0 : a = 0
      · have h := bernoulliProbability_le_one
          (α := Fin n) θ
          (fun e ↦ a ≤
            ((Finset.univ.filter fun i ↦ e i).card : ℝ) - μ) hθ
        simpa [hμ, ha0] using h
      · have h := bernoulli_upper_tail_chernoff
          (α := Fin n) θ a (3 / 2) hθ (by norm_num)
        have hexp :
            -(3 / 2) * a = -(a ^ 2) / (2 * a / 3) := by
          field_simp [ha0]
        simpa [μ, hμ, hexp] using h
    · have h := bernoulliProbability_le_one
        (α := Fin n) θ
        (fun e ↦ a ≤ μ -
          ((Finset.univ.filter fun i ↦ e i).card : ℝ)) hθ
      simpa [hμ] using h
  · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
    constructor
    · let t : ℝ := 3 * a / (3 * μ + a)
      have hden : 0 < 3 * μ + a := by positivity
      have ht0 : 0 ≤ t := by
        dsimp [t]
        positivity
      have ht3 : t < 3 := by
        dsimp [t]
        rw [div_lt_iff₀ hden]
        nlinarith
      have hchern := bernoulli_upper_tail_chernoff
        (α := Fin n) θ a t hθ ht0
      have hrem := exp_sub_one_sub_le_bernstein t ht0 ht3
      have hcg :
          μ * (Real.exp t - 1 - t) ≤
            μ * (3 * t ^ 2 / (2 * (3 - t))) :=
        mul_le_mul_of_nonneg_left hrem hμ0
      have hexponent :
          -t * a + μ * (Real.exp t - 1 - t) ≤
            -(a ^ 2) / (2 * μ + 2 * a / 3) := by
        calc
          _ ≤ -t * a + μ * (3 * t ^ 2 / (2 * (3 - t))) :=
            by simpa [add_comm] using add_le_add_left hcg (-t * a)
          _ = _ := by
            dsimp [t]
            field_simp [ne_of_gt hden, ne_of_gt (sub_pos.mpr ht3)]
            ring
      calc
        _ ≤ Real.exp (-t * a + μ * (Real.exp t - 1 - t)) := by
          simpa [μ] using hchern
        _ ≤ _ := Real.exp_le_exp.mpr hexponent
    · let t : ℝ := a / μ
      have ht0 : 0 ≤ t := by
        dsimp [t]
        positivity
      have hchern := bernoulli_lower_tail_chernoff
        (α := Fin n) θ a t hθ ht0
      have hrem := exp_neg_sub_one_add_le_half_sq t ht0
      have hcg :
          μ * (Real.exp (-t) - 1 + t) ≤ μ * (t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hrem hμ0
      have hexponent :
          -t * a + μ * (Real.exp (-t) - 1 + t) ≤
            -(a ^ 2) / (2 * μ) := by
        calc
          _ ≤ -t * a + μ * (t ^ 2 / 2) := by
            simpa [add_comm] using add_le_add_left hcg (-t * a)
          _ = _ := by
            dsimp [t]
            field_simp [ne_of_gt hμpos]
            ring
      calc
        _ ≤ Real.exp (-t * a + μ * (Real.exp (-t) - 1 + t)) := by
          simpa [μ] using hchern
        _ ≤ _ := Real.exp_le_exp.mpr hexponent

end Problem56
