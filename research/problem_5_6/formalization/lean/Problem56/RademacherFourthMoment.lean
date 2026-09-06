import Problem56.ProjectionMean

/-!
The exact fourth moment of the Euclidean norm of a finite Rademacher sum.
This module contains the implementation used by the `I39` statement wrapper;
it does not import the admitted statement layer.
-/

open scoped BigOperators Matrix

namespace Problem56

@[simp] theorem signValue_mul_self
    {α : Type*} (ξ : SignLayer α) (i : α) :
    signValue ξ i * signValue ξ i = 1 := by
  cases hξ : ξ i <;> simp [signValue, hξ]

theorem uniformExpectation_signValue_four_eq_zero_of_first_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    (i j k l : α) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
    uniformExpectation (fun ξ : SignLayer α ↦
      signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l) = 0 := by
  classical
  let e : Equiv.Perm (SignLayer α) :=
    (flipSignAt_involutive i).toPerm (flipSignAt i)
  let S := ∑ ξ : SignLayer α,
    signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l
  have hperm : S = ∑ ξ : SignLayer α,
      signValue (flipSignAt i ξ) i * signValue (flipSignAt i ξ) j *
        signValue (flipSignAt i ξ) k * signValue (flipSignAt i ξ) l := by
    exact Fintype.sum_equiv e
      (fun ξ ↦ signValue ξ i * signValue ξ j *
        signValue ξ k * signValue ξ l)
      (fun ξ ↦ signValue (flipSignAt i ξ) i *
        signValue (flipSignAt i ξ) j *
        signValue (flipSignAt i ξ) k *
        signValue (flipSignAt i ξ) l)
      (fun ξ ↦ by
        change signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l =
          signValue (flipSignAt i (flipSignAt i ξ)) i *
            signValue (flipSignAt i (flipSignAt i ξ)) j *
            signValue (flipSignAt i (flipSignAt i ξ)) k *
            signValue (flipSignAt i (flipSignAt i ξ)) l
        rw [flipSignAt_involutive i ξ])
  have hneg : (∑ ξ : SignLayer α,
      signValue (flipSignAt i ξ) i * signValue (flipSignAt i ξ) j *
        signValue (flipSignAt i ξ) k * signValue (flipSignAt i ξ) l) = -S := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [signValue_flipSignAt_self,
      signValue_flipSignAt_of_ne hij.symm,
      signValue_flipSignAt_of_ne hik.symm,
      signValue_flipSignAt_of_ne hil.symm]
    ring
  have hS : S = 0 := by
    rw [hneg] at hperm
    linarith
  simp only [uniformExpectation]
  rw [show (∑ ξ : SignLayer α,
      signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l) = S by rfl,
    hS, zero_div]

theorem uniformExpectation_signValue_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (i j k l : α) :
    uniformExpectation (fun ξ : SignLayer α ↦
      signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0) +
      (if i = l then 1 else 0) * (if j = k then 1 else 0) -
      2 * (if i = j then 1 else 0) * (if i = k then 1 else 0) *
        (if i = l then 1 else 0) := by
  classical
  by_cases hij : i = j
  · subst j
    calc
      uniformExpectation (fun ξ : SignLayer α ↦
          signValue ξ i * signValue ξ i * signValue ξ k * signValue ξ l) =
          uniformExpectation (fun ξ : SignLayer α ↦
            signValue ξ k * signValue ξ l) := by
            congr 1
            funext ξ
            rw [signValue_mul_self]
            ring
      _ = if k = l then 1 else 0 := uniformExpectation_signValue_pair k l
      _ = _ := by
        by_cases hik : i = k <;> by_cases hil : i = l <;>
          by_cases hkl : k = l <;> simp [hik, hil, hkl, eq_comm] <;> norm_num
  · by_cases hik : i = k
    · subst k
      calc
        uniformExpectation (fun ξ : SignLayer α ↦
            signValue ξ i * signValue ξ j * signValue ξ i * signValue ξ l) =
            uniformExpectation (fun ξ : SignLayer α ↦
              signValue ξ j * signValue ξ l) := by
              congr 1
              funext ξ
              rw [show signValue ξ i * signValue ξ j * signValue ξ i * signValue ξ l =
                (signValue ξ i * signValue ξ i) *
                  (signValue ξ j * signValue ξ l) by ring,
                signValue_mul_self, one_mul]
        _ = if j = l then 1 else 0 := uniformExpectation_signValue_pair j l
        _ = _ := by
          have hji : j ≠ i := Ne.symm hij
          simp [hij, hji]
    · by_cases hil : i = l
      · subst l
        calc
          uniformExpectation (fun ξ : SignLayer α ↦
              signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ i) =
              uniformExpectation (fun ξ : SignLayer α ↦
                signValue ξ j * signValue ξ k) := by
                congr 1
                funext ξ
                rw [show signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ i =
                  (signValue ξ i * signValue ξ i) *
                    (signValue ξ j * signValue ξ k) by ring,
                  signValue_mul_self, one_mul]
          _ = if j = k then 1 else 0 := uniformExpectation_signValue_pair j k
          _ = _ := by simp [hij, hik]
      · rw [uniformExpectation_signValue_four_eq_zero_of_first_ne
          i j k l hij hik hil]
        simp [hij, hik, hil]

private lemma sum_three_rotate
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

theorem euclideanNorm_rademacher_sum_pow_four
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (U : Matrix α (Fin r) ℝ) (ξ : SignLayer α) :
    (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4 =
      (∑ i, ∑ j, signValue ξ i * signValue ξ j * (U * U.transpose) i j) ^ 2 := by
  classical
  let S := ∑ a, (∑ j, signValue ξ j * U j a) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ ↦ sq_nonneg _)
  have hquad : S =
      ∑ i, ∑ j, signValue ξ i * signValue ξ j * (U * U.transpose) i j := by
    calc
      S = ∑ a, ∑ i, ∑ j,
          signValue ξ i * signValue ξ j * U i a * U j a := by
        dsimp only [S]
        apply Finset.sum_congr rfl
        intro a _
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, ∑ a,
          signValue ξ i * signValue ξ j * U i a * U j a :=
        sum_three_rotate _
      _ = ∑ i, ∑ j,
          signValue ξ i * signValue ξ j * (U * U.transpose) i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  rw [euclideanNorm, show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hS,
    hquad]

private theorem fourth_delta_contraction
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : Matrix α α ℝ) (hG : G.transpose = G) :
    (∑ i, ∑ j, ∑ k, ∑ l, G i j * G k l *
      ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
       (if i = k then 1 else 0) * (if j = l then 1 else 0) +
       (if i = l then 1 else 0) * (if j = k then 1 else 0) -
       2 * (if i = j then 1 else 0) * (if i = k then 1 else 0) *
         (if i = l then 1 else 0))) =
      (∑ i, G i i) ^ 2 + 2 * ∑ i, ∑ j, (G i j) ^ 2 -
        2 * ∑ i, (G i i) ^ 2 := by
  classical
  have hsymm (i j : α) : G j i = G i j := by
    have h := congrFun (congrFun hG i) j
    simpa only [Matrix.transpose_apply] using h
  have hdiagcomm :
      (∑ i, ∑ j, G i i * G j j) = ∑ i, ∑ j, G j j * G i i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdouble :
      (∑ i, ∑ j, (G i j) ^ 2) * 2 = ∑ i, ∑ j, (G i j) ^ 2 * 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [pow_two, Finset.sum_mul, Finset.mul_sum, hsymm]
  ring_nf
  rw [← hdiagcomm]
  rw [hdouble, sub_eq_add_neg]
  abel

theorem uniformExpectation_sign_quadratic_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : Matrix α α ℝ) (hG : G.transpose = G) :
    uniformExpectation (fun ξ : SignLayer α ↦
      (∑ i, ∑ j, signValue ξ i * signValue ξ j * G i j) ^ 2) =
      (∑ i, G i i) ^ 2 + 2 * ∑ i, ∑ j, (G i j) ^ 2 -
        2 * ∑ i, (G i i) ^ 2 := by
  classical
  have hexpand (ξ : SignLayer α) :
      (∑ i, ∑ j, signValue ξ i * signValue ξ j * G i j) ^ 2 =
        ∑ i, ∑ j, ∑ k, ∑ l, G i j * G k l *
          (signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    uniformExpectation (fun ξ : SignLayer α ↦
        (∑ i, ∑ j, signValue ξ i * signValue ξ j * G i j) ^ 2) =
        uniformExpectation (fun ξ : SignLayer α ↦
          ∑ i, ∑ j, ∑ k, ∑ l, G i j * G k l *
            (signValue ξ i * signValue ξ j * signValue ξ k * signValue ξ l)) := by
      congr 1
      funext ξ
      exact hexpand ξ
    _ = ∑ i, ∑ j, ∑ k, ∑ l, G i j * G k l *
        ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
         (if i = k then 1 else 0) * (if j = l then 1 else 0) +
         (if i = l then 1 else 0) * (if j = k then 1 else 0) -
         2 * (if i = j then 1 else 0) * (if i = k then 1 else 0) *
           (if i = l then 1 else 0)) := by
      rw [uniformExpectation_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [uniformExpectation_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [uniformExpectation_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [uniformExpectation_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [uniformExpectation_const_mul,
        uniformExpectation_signValue_four]
    _ = _ := fourth_delta_contraction G hG

theorem rademacher_vector_fourth_moment
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (U : Matrix α (Fin r) ℝ) (hU : OrthonormalFrame U) :
    uniformExpectation (Ω := SignLayer α) (fun ξ ↦
      (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) =
      ((r : ℝ) ^ 2 + 2 * r -
        2 * ∑ j, (∑ a, (U j a) ^ 2) ^ 2) ∧
    uniformExpectation (Ω := SignLayer α) (fun ξ ↦
      (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) ≤
      ((r : ℝ) ^ 2 + 2 * r) := by
  classical
  let G := U * U.transpose
  have hGsymm : G.transpose = G := by
    simp [G, Matrix.transpose_mul]
  have hGidempotent : G * G = G := by
    simp only [G, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.transpose U U.transpose, hU]
    simp
  have htrace : (∑ i, G i i) = (r : ℝ) := by
    simpa [G] using frameProjection_trace U hU
  have hsymm (i j : α) : G j i = G i j := by
    have h := congrFun (congrFun hGsymm i) j
    simpa only [Matrix.transpose_apply] using h
  have hfrob : (∑ i, ∑ j, (G i j) ^ 2) = (r : ℝ) := by
    calc
      (∑ i, ∑ j, (G i j) ^ 2) = Matrix.trace (G * G) := by
        rw [Matrix.trace]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [hsymm]
        ring
      _ = Matrix.trace G := by rw [hGidempotent]
      _ = (r : ℝ) := by
        simpa [Matrix.trace, G] using frameProjection_trace U hU
  have hdiag (i : α) : G i i = ∑ a, (U i a) ^ 2 := by
    simp only [G, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hmoment :
      uniformExpectation (Ω := SignLayer α) (fun ξ ↦
        (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) =
        (∑ i, G i i) ^ 2 + 2 * ∑ i, ∑ j, (G i j) ^ 2 -
          2 * ∑ i, (G i i) ^ 2 := by
    calc
      uniformExpectation (Ω := SignLayer α) (fun ξ ↦
          (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) =
          uniformExpectation (fun ξ : SignLayer α ↦
            (∑ i, ∑ j, signValue ξ i * signValue ξ j * G i j) ^ 2) := by
        congr 1
        funext ξ
        simpa [G] using euclideanNorm_rademacher_sum_pow_four U ξ
      _ = _ := uniformExpectation_sign_quadratic_sq G hGsymm
  have hexact :
      uniformExpectation (Ω := SignLayer α) (fun ξ ↦
        (euclideanNorm (fun a ↦ ∑ j, signValue ξ j * U j a)) ^ 4) =
        ((r : ℝ) ^ 2 + 2 * r -
          2 * ∑ j, (∑ a, (U j a) ^ 2) ^ 2) := by
    rw [hmoment, htrace, hfrob]
    simp_rw [hdiag]
  refine ⟨hexact, ?_⟩
  rw [hexact]
  have hnonneg : 0 ≤ ∑ j, (∑ a, (U j a) ^ 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)
  linarith

#print axioms uniformExpectation_signValue_four
#print axioms rademacher_vector_fourth_moment

end Problem56
