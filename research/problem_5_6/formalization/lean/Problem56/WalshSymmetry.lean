import Problem56.Definitions

/-!
Finite Walsh translation/modulation identities used by the corrected I14
interface.  The probability invariance is proved by explicit equivalences of
the finite sign-layer sample space.
-/

open scoped BigOperators Matrix

namespace Problem56

private theorem zmod2_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

theorem walshCharacter_comm' {m : ℕ} (a b : WalshIndex m) :
    walshCharacter a b = walshCharacter b a := by
  have hdot : walshDot a b = walshDot b a := by
    simp only [walshDot]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  simp only [walshCharacter, hdot]

theorem walshCharacter_add_right' {m : ℕ} (c x y : WalshIndex m) :
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

theorem walshCharacter_add_left {m : ℕ} (i s a : WalshIndex m) :
    walshCharacter (i + s) a = walshCharacter i a * walshCharacter s a := by
  rw [walshCharacter_comm' (i + s) a, walshCharacter_add_right',
    walshCharacter_comm' a i, walshCharacter_comm' a s]

theorem walshModulation_mul_normalizedWalsh {m : ℕ} (s : WalshIndex m) :
    walshModulation s * normalizedWalsh m =
      normalizedWalsh m * walshTranslation s := by
  classical
  ext i j
  simp [walshModulation, normalizedWalsh, walshTranslation,
    Matrix.mul_apply, Matrix.diagonal_apply, walshCharacter_add_right',
    walshCharacter_comm']
  ring

theorem walshTranslation_mul_normalizedWalsh {m : ℕ} (s : WalshIndex m) :
    walshTranslation s * normalizedWalsh m =
      normalizedWalsh m * walshModulation s := by
  classical
  ext i j
  have hss : s + s = 0 := by
    funext a
    exact CharTwo.add_self_eq_zero (s a)
  have hiff : ∀ x : WalshIndex m, i = x + s ↔ x = i + s := by
    intro x
    constructor
    · intro h
      calc
        x = (x + s) + s := by simp [add_assoc, hss]
        _ = i + s := by rw [h]
    · intro h
      rw [h]
      simp [add_assoc, hss]
  simp [walshModulation, normalizedWalsh, walshTranslation,
    Matrix.mul_apply, Matrix.diagonal_apply, walshCharacter_add_right',
    walshCharacter_comm', hiff]
  ring

theorem translateSign_involutive {m : ℕ} (s : WalshIndex m) :
    Function.Involutive (translateSign s) := by
  have hss : s + s = 0 := by
    funext a
    exact CharTwo.add_self_eq_zero (s a)
  intro d
  funext i
  simp [translateSign, add_assoc, hss]

theorem modulateSign_involutive {m : ℕ} (s : WalshIndex m) :
    Function.Involutive (modulateSign s) := by
  intro d
  funext i
  by_cases h : walshCharacter s i = 1 <;> simp [modulateSign, h]

theorem signPairExpectation_walsh_symmetry {m : ℕ} (s : WalshIndex m)
    (F : SignLayer (WalshIndex m) → SignLayer (WalshIndex m) → ℝ) :
    signPairExpectation (fun d₁ d₂ ↦
      F (modulateSign s d₁) (translateSign s d₂)) = signPairExpectation F := by
  classical
  let emod : Equiv.Perm (SignLayer (WalshIndex m)) :=
    (modulateSign_involutive s).toPerm (modulateSign s)
  let etrans : Equiv.Perm (SignLayer (WalshIndex m)) :=
    (translateSign_involutive s).toPerm (translateSign s)
  let e := emod.prodCongr etrans
  have hsum :
      (∑ d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m),
        F (modulateSign s d.1) (translateSign s d.2)) =
      ∑ d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m), F d.1 d.2 := by
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  simp only [signPairExpectation, uniformExpectation]
  rw [hsum]

theorem exists_walshCharacter_eq_neg_one {m : ℕ} (x : WalshIndex m)
    (hx : x ≠ 0) : ∃ c : WalshIndex m, walshCharacter c x = -1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  refine ⟨Pi.single i 1, ?_⟩
  have hdot : walshDot (Pi.single i 1) x = x i := by
    simp [walshDot, Pi.single_apply]
  simp [walshCharacter, hdot, hi]

theorem signValue_modulate {m : ℕ} (s : WalshIndex m)
    (d : SignLayer (WalshIndex m)) (i : WalshIndex m) :
    signValue (modulateSign s d) i = walshCharacter s i * signValue d i := by
  by_cases hdot : walshDot s i = 0
  · simp [modulateSign, walshCharacter, signValue, hdot]
  · cases hdi : d i <;>
      simp [modulateSign, walshCharacter, signValue, hdot, hdi] <;> norm_num

theorem signDiagonal_modulate {m : ℕ} (s : WalshIndex m)
    (d : SignLayer (WalshIndex m)) :
    signDiagonal (modulateSign s d) = walshModulation s * signDiagonal d := by
  simp only [signDiagonal, walshModulation, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact signValue_modulate s d i

theorem signDiagonal_translate {m : ℕ} (s : WalshIndex m)
    (d : SignLayer (WalshIndex m)) :
    signDiagonal (translateSign s d) =
      walshTranslation s * signDiagonal d * walshTranslation s := by
  classical
  ext i j
  have hss : s + s = 0 := by
    funext a
    exact CharTwo.add_self_eq_zero (s a)
  have hiff : ∀ x : WalshIndex m, i = x + s ↔ x = i + s := by
    intro x
    constructor
    · intro h
      calc
        x = (x + s) + s := by simp [add_assoc, hss]
        _ = i + s := by rw [h]
    · intro h
      rw [h]
      simp [add_assoc, hss]
  by_cases hij : i = j
  · subst j
    simp [signDiagonal, translateSign, walshTranslation, Matrix.mul_apply, hiff]
    rfl
  · simp [signDiagonal, translateSign, walshTranslation, Matrix.mul_apply, hiff, hij]

theorem walshModulation_mul_self {m : ℕ} (s : WalshIndex m) :
    walshModulation s * walshModulation s =
      (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ) := by
  simp only [walshModulation, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [walshCharacter]
  split_ifs <;> norm_num

theorem transformedFrame_walsh_symmetry {m r : ℕ} (s : WalshIndex m)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) :
    transformedFrame (modulateSign s d₁) (translateSign s d₂) V =
      walshModulation s * transformedFrame d₁ d₂ V := by
  simp only [transformedFrame, signDiagonal_translate, signDiagonal_modulate,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (normalizedWalsh m) (walshTranslation s)]
  rw [← walshModulation_mul_normalizedWalsh s]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (walshTranslation s) (normalizedWalsh m)]
  rw [walshTranslation_mul_normalizedWalsh s]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (walshModulation s) (walshModulation s)]
  rw [walshModulation_mul_self]
  simp

theorem randomProjection_walsh_symmetry {m r : ℕ} (s : WalshIndex m)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) :
    randomProjection (modulateSign s d₁) (translateSign s d₂) V =
      walshModulation s * randomProjection d₁ d₂ V * walshModulation s := by
  simp only [randomProjection, transformedFrame_walsh_symmetry, Matrix.transpose_mul,
    walshModulation, Matrix.diagonal_transpose, Matrix.mul_assoc]

theorem walsh_translation_modulation_package {m : ℕ} (s : WalshIndex m) :
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
  exact ⟨(fun i a ↦ walshCharacter_add_left i s a),
    walshModulation_mul_normalizedWalsh s,
    walshTranslation_mul_normalizedWalsh s,
    signPairExpectation_walsh_symmetry s,
    (fun _ V d₁ d₂ ↦ randomProjection_walsh_symmetry s V d₁ d₂),
    (fun x hx ↦ exists_walshCharacter_eq_neg_one x hx)⟩

#print axioms walshCharacter_add_left
#print axioms walshModulation_mul_normalizedWalsh
#print axioms walshTranslation_mul_normalizedWalsh
#print axioms signPairExpectation_walsh_symmetry
#print axioms exists_walshCharacter_eq_neg_one
#print axioms signDiagonal_modulate
#print axioms signDiagonal_translate
#print axioms transformedFrame_walsh_symmetry
#print axioms randomProjection_walsh_symmetry
#print axioms walsh_translation_modulation_package

end Problem56
