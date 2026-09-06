import Problem56.WalshSymmetry
import Problem56.CumulantMoment

/-!
Finite sign-averaging identities for the exact mean of the randomized
projection.  The basic cancellation is proved by a coordinate-flip
permutation of the finite sign layer.
-/

open scoped BigOperators Matrix

namespace Problem56

private lemma projectionMean_sum_five_permute
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

private lemma projectionMean_walshCharacter_comm {m : ℕ}
    (a b : WalshIndex m) :
    walshCharacter a b = walshCharacter b a := by
  have hdot : walshDot a b = walshDot b a := by
    simp only [walshDot]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  simp only [walshCharacter, hdot]

theorem sum_walshCharacter_projectionMean {m : ℕ} (c : WalshIndex m) :
    (∑ x, walshCharacter c x) =
      if c = 0 then (walshCard m : ℝ) else 0 := by
  classical
  let ψ : AddChar (WalshIndex m) ℝ :=
    { toFun := walshCharacter c
      map_zero_eq_one' := by simp [walshCharacter, walshDot]
      map_add_eq_mul' := walshCharacter_add_right' c }
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

theorem sum_walshCharacter_pair {m : ℕ} (i j : WalshIndex m) :
    (∑ a, walshCharacter i a * walshCharacter j a) =
      if i = j then (walshCard m : ℝ) else 0 := by
  have hij : i + j = 0 ↔ i = j := by
    have hneg : -j = j := by
      funext x
      exact ZMod.neg_eq_self_mod_two (j x)
    rw [add_eq_zero_iff_eq_neg, hneg]
  calc
    _ = ∑ a, walshCharacter (i + j) a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (walshCharacter_add_left i j a).symm
    _ = _ := by
      rw [sum_walshCharacter_projectionMean, if_congr hij rfl rfl]

theorem normalizedWalsh_mul_swap {m : ℕ} (a x : WalshIndex m) :
    normalizedWalsh m a x * normalizedWalsh m x a =
      1 / (walshCard m : ℝ) := by
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  rw [normalizedWalsh, normalizedWalsh,
    projectionMean_walshCharacter_comm x a]
  have hsq : walshCharacter a x * walshCharacter a x = 1 := by
    simp only [walshCharacter]
    split_ifs <;> norm_num
  field_simp
  rw [Real.sq_sqrt hcard.le]
  have hsq' : walshCharacter a x ^ 2 = 1 := by
    nlinarith [hsq]
  rw [hsq']
  ring

theorem frameProjection_trace {α : Type*} [Fintype α] [DecidableEq α]
    {r : ℕ} (V : Matrix α (Fin r) ℝ) (hV : OrthonormalFrame V) :
    ∑ x, (V * V.transpose) x x = (r : ℝ) := by
  change Matrix.trace (V * V.transpose) = (r : ℝ)
  rw [Matrix.trace_mul_comm, hV, Matrix.trace_one]
  simp

def flipSignAt {α : Type*} [DecidableEq α] (i : α)
    (d : SignLayer α) : SignLayer α :=
  fun j ↦ if j = i then !d j else d j

theorem flipSignAt_involutive {α : Type*} [DecidableEq α] (i : α) :
    Function.Involutive (flipSignAt i) := by
  intro d
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipSignAt]
  · simp [flipSignAt, hji]

@[simp]
theorem signValue_flipSignAt_self {α : Type*} [DecidableEq α]
    (i : α) (d : SignLayer α) :
    signValue (flipSignAt i d) i = -signValue d i := by
  cases hdi : d i <;> simp [flipSignAt, signValue, hdi]

@[simp]
theorem signValue_flipSignAt_of_ne {α : Type*} [DecidableEq α]
    {i j : α} (hji : j ≠ i) (d : SignLayer α) :
    signValue (flipSignAt i d) j = signValue d j := by
  unfold signValue
  rw [show flipSignAt i d j = d j by simp [flipSignAt, hji]]

theorem sum_signValue_pair_eq_zero_of_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {i j : α} (hij : i ≠ j) :
    (∑ d : SignLayer α, signValue d i * signValue d j) = 0 := by
  classical
  let e : Equiv.Perm (SignLayer α) :=
    (flipSignAt_involutive i).toPerm (flipSignAt i)
  let S := ∑ d : SignLayer α, signValue d i * signValue d j
  have hperm : S =
      ∑ d : SignLayer α,
        signValue (flipSignAt i d) i * signValue (flipSignAt i d) j := by
    exact Fintype.sum_equiv e
      (fun d ↦ signValue d i * signValue d j)
      (fun d ↦ signValue (flipSignAt i d) i *
        signValue (flipSignAt i d) j)
      (fun d ↦ by
        change signValue d i * signValue d j =
          signValue (flipSignAt i (flipSignAt i d)) i *
            signValue (flipSignAt i (flipSignAt i d)) j
        rw [flipSignAt_involutive i d])
  have hneg :
      (∑ d : SignLayer α,
        signValue (flipSignAt i d) i * signValue (flipSignAt i d) j) = -S := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [signValue_flipSignAt_self,
      signValue_flipSignAt_of_ne hij.symm]
    ring
  rw [hneg] at hperm
  linarith

theorem uniformExpectation_signValue_pair
    {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) :
    uniformExpectation (fun d : SignLayer α ↦
      signValue d i * signValue d j) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [uniformExpectation, if_pos]
    have hone : ∀ d : SignLayer α,
        signValue d i * signValue d i = (1 : ℝ) := by
      intro d
      cases hdi : d i <;> simp [signValue, hdi]
    simp_rw [hone]
    have hcard : (Fintype.card (SignLayer α) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (SignLayer α) ≠ 0)
    simp [hcard]
  · rw [if_neg hij]
    simp [uniformExpectation, sum_signValue_pair_eq_zero_of_ne hij]

theorem uniformExpectation_prod_factor
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] (F : Ω₁ → ℝ) (G : Ω₂ → ℝ) :
    uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1 * G z.2) =
      uniformExpectation F * uniformExpectation G := by
  classical
  simp only [uniformExpectation, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, Fintype.card_prod]
  push_cast
  have hcard₁ : (Fintype.card Ω₁ : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω₁ ≠ 0)
  have hcard₂ : (Fintype.card Ω₂ : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω₂ ≠ 0)
  field_simp

theorem uniformExpectation_sum
    {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (F : κ → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∑ k, F k ω) =
      ∑ k, uniformExpectation (F k) := by
  classical
  simp only [uniformExpectation, Finset.sum_div]
  rw [Finset.sum_comm]

theorem uniformExpectation_const_mul
    {Ω : Type*} [Fintype Ω] (c : ℝ) (F : Ω → ℝ) :
    uniformExpectation (fun ω ↦ c * F ω) = c * uniformExpectation F := by
  classical
  simp only [uniformExpectation]
  rw [← Finset.mul_sum]
  ring

theorem uniformExpectation_sub_const
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (F : Ω → ℝ) (c : ℝ) :
    uniformExpectation (fun ω ↦ F ω - c) = uniformExpectation F - c := by
  classical
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  have hsumc : (∑ _ : Ω, c) = (Fintype.card Ω : ℝ) * c := by
    simp
  simp only [uniformExpectation, Finset.sum_sub_distrib]
  rw [hsumc]
  field_simp

theorem uniformExpectation_sub
    {Ω : Type*} [Fintype Ω] (F G : Ω → ℝ) :
    uniformExpectation (fun ω ↦ F ω - G ω) =
      uniformExpectation F - uniformExpectation G := by
  classical
  simp only [uniformExpectation, Finset.sum_sub_distrib]
  ring

theorem signPairExpectation_sum
    {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ]
    (F : κ → SignLayer α → SignLayer α → ℝ) :
    signPairExpectation (fun d₁ d₂ ↦ ∑ k, F k d₁ d₂) =
      ∑ k, signPairExpectation (F k) := by
  change uniformExpectation
      (fun d : SignLayer α × SignLayer α ↦ ∑ k, F k d.1 d.2) =
    ∑ k, uniformExpectation
      (fun d : SignLayer α × SignLayer α ↦ F k d.1 d.2)
  exact uniformExpectation_sum
    (fun (k : κ) (d : SignLayer α × SignLayer α) ↦ F k d.1 d.2)

theorem signPairExpectation_const_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (F : SignLayer α → SignLayer α → ℝ) :
    signPairExpectation (fun d₁ d₂ ↦ c * F d₁ d₂) =
      c * signPairExpectation F := by
  simpa only [signPairExpectation] using uniformExpectation_const_mul c
    (fun d : SignLayer α × SignLayer α ↦ F d.1 d.2)

theorem signPairExpectation_sub_const
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : SignLayer α → SignLayer α → ℝ) (c : ℝ) :
    signPairExpectation (fun d₁ d₂ ↦ F d₁ d₂ - c) =
      signPairExpectation F - c := by
  simpa only [signPairExpectation] using uniformExpectation_sub_const
    (fun d : SignLayer α × SignLayer α ↦ F d.1 d.2) c

theorem partitionMomentProduct_insertPoint
    {Ω α : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s)
    (Y : α → Ω → ℝ) (c : ℝ) (hY : ∀ ω, Y a ω = c)
    (Q : Finpartition s) (choice : Option Q.parts) :
    (∏ C ∈ (finpartitionInsertPoint ha Q choice).parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω)) =
      c * ∏ C ∈ Q.parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω) := by
  classical
  cases choice with
  | none =>
      rw [finpartitionInsertPoint_parts_none]
      have hsingleton : {a} ∉ Q.parts := by
        intro hmem
        exact ha (Q.subset hmem (Finset.mem_singleton_self a))
      rw [Finset.prod_insert hsingleton]
      have hsingle : uniformExpectation (fun ω ↦ ∏ j ∈ ({a} : Finset α),
          Y j ω) = c := by
        simp [hY, uniformExpectation, Fintype.card_ne_zero]
      rw [hsingle]
  | some B =>
      rw [finpartitionInsertPoint_parts_some]
      have hnew : insert a B.1 ∉ Q.parts.erase B.1 := by
        intro hmem
        have hpart : insert a B.1 ∈ Q.parts := (Finset.mem_erase.mp hmem).2
        exact ha (Q.subset hpart (Finset.mem_insert_self a B.1))
      rw [Finset.prod_insert hnew]
      have haB : a ∉ B.1 := fun haB ↦ ha (Q.subset B.2 haB)
      have hblock : uniformExpectation (fun ω ↦
          ∏ j ∈ insert a B.1, Y j ω) =
          c * uniformExpectation (fun ω ↦ ∏ j ∈ B.1, Y j ω) := by
        simp_rw [Finset.prod_insert haB, hY]
        exact uniformExpectation_const_mul c _
      rw [hblock]
      rw [mul_assoc, Finset.mul_prod_erase Q.parts
        (fun C ↦ uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω)) B.2]

theorem jointCumulantOn_eq_zero_of_constant_coordinate
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    [DecidableEq ι] (Y : ι → Ω → ℝ) (a : ι) (c : ℝ)
    (hY : ∀ ω, Y a ω = c) (hcard : 2 ≤ Fintype.card ι) :
    jointCumulantOn Y = 0 := by
  classical
  let s : Finset ι := Finset.univ.erase a
  have ha : a ∉ s := Finset.notMem_erase a Finset.univ
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hsempty
    have hcardErase := Finset.card_erase_of_mem (Finset.mem_univ a)
    rw [show (Finset.univ : Finset ι).erase a = s by rfl, hsempty,
      Finset.card_empty, Finset.card_univ] at hcardErase
    omega
  have hinsert : insert a s = (Finset.univ : Finset ι) := by
    exact Finset.insert_erase (Finset.mem_univ a)
  rw [jointCumulantOn, ← hinsert]
  change (∑ P : Finpartition (insert a s),
      finpartitionWeight P *
        ∏ C ∈ P.parts,
          uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω)) = 0
  calc
    _ = ∑ data : Σ Q : Finpartition s, Option Q.parts,
        finpartitionWeight (finpartitionInsertPoint ha data.1 data.2) *
          ∏ C ∈ (finpartitionInsertPoint ha data.1 data.2).parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω) := by
      exact (Fintype.sum_equiv (finpartitionInsertPointEquiv ha)
        (fun data ↦
          finpartitionWeight (finpartitionInsertPoint ha data.1 data.2) *
            ∏ C ∈ (finpartitionInsertPoint ha data.1 data.2).parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω))
        (fun P ↦ finpartitionWeight P *
          ∏ C ∈ P.parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω))
        (fun _ ↦ rfl)).symm
    _ = ∑ Q : Finpartition s, ∑ choice : Option Q.parts,
        finpartitionWeight (finpartitionInsertPoint ha Q choice) *
          ∏ C ∈ (finpartitionInsertPoint ha Q choice).parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω) :=
      Fintype.sum_sigma _
    _ = ∑ Q : Finpartition s,
        (∑ choice : Option Q.parts,
          finpartitionWeight (finpartitionInsertPoint ha Q choice)) *
            (c * ∏ C ∈ Q.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ C, Y j ω)) := by
      apply Finset.sum_congr rfl
      intro Q _
      simp_rw [partitionMomentProduct_insertPoint ha Y c hY Q]
      rw [Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro Q _
      rw [sum_finpartitionWeight_insertPoint_choices ha Q]
      have hparts : Q.parts.card ≠ 0 := by
        exact Finset.card_ne_zero.mpr (Q.parts_nonempty hs.ne_empty)
      simp [hparts]

def replaceCoordinate {Ω ι : Type*} [DecidableEq ι]
    (Y : ι → Ω → ℝ) (a : ι) (F : Ω → ℝ) : ι → Ω → ℝ :=
  fun j ↦ if j = a then F else Y j

theorem blockProduct_replaceCoordinate
    {Ω ι : Type*} [DecidableEq ι]
    (Y : ι → Ω → ℝ) (a : ι) (F : Ω → ℝ)
    (B : Finset ι) (haB : a ∈ B) (ω : Ω) :
    (∏ j ∈ B, replaceCoordinate Y a F j ω) =
      F ω * ∏ j ∈ B.erase a, Y j ω := by
  classical
  rw [← Finset.mul_prod_erase B (fun j ↦ replaceCoordinate Y a F j ω) haB]
  simp only [replaceCoordinate, if_pos]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hja : j ≠ a := (Finset.mem_erase.mp hj).1
  simp [replaceCoordinate, hja]

theorem blockMoment_replaceCoordinate_eq_of_not_mem
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (Y : ι → Ω → ℝ) (a : ι) (F : Ω → ℝ)
    (B : Finset ι) (haB : a ∉ B) :
    uniformExpectation (fun ω ↦
      ∏ j ∈ B, replaceCoordinate Y a F j ω) =
      uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω) := by
  apply congrArg uniformExpectation
  funext ω
  apply Finset.prod_congr rfl
  intro j hj
  have hja : j ≠ a := fun hja ↦ haB (hja ▸ hj)
  simp [replaceCoordinate, hja]

theorem blockMoment_replace_sub
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (Y : ι → Ω → ℝ) (a : ι) (c : ℝ)
    (B : Finset ι) (haB : a ∈ B) :
    uniformExpectation (fun ω ↦
      ∏ j ∈ B, replaceCoordinate Y a (fun ω ↦ Y a ω - c) j ω) =
      uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω) -
        uniformExpectation (fun ω ↦
          ∏ j ∈ B, replaceCoordinate Y a (fun _ ↦ c) j ω) := by
  simp_rw [blockProduct_replaceCoordinate Y a
    (fun ω ↦ Y a ω - c) B haB]
  simp_rw [blockProduct_replaceCoordinate Y a (fun _ ↦ c) B haB]
  have hbase : ∀ ω,
      (∏ j ∈ B, Y j ω) = Y a ω * ∏ j ∈ B.erase a, Y j ω := by
    intro ω
    exact (Finset.mul_prod_erase B (fun j ↦ Y j ω) haB).symm
  simp_rw [hbase]
  rw [← uniformExpectation_sub]
  apply congrArg uniformExpectation
  funext ω
  ring

theorem partitionMomentProduct_replace_sub
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ) (a : ι) (c : ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∏ B ∈ P.parts,
      uniformExpectation (fun ω ↦ ∏ j ∈ B,
        replaceCoordinate Y a (fun ω ↦ Y a ω - c) j ω)) =
      (∏ B ∈ P.parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω)) -
      (∏ B ∈ P.parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ B,
          replaceCoordinate Y a (fun _ ↦ c) j ω)) := by
  classical
  let A := P.part a
  have hA : A ∈ P.parts := P.part_mem.mpr (Finset.mem_univ a)
  have haA : a ∈ A := P.mem_part (Finset.mem_univ a)
  let msub : Finset ι → ℝ := fun B ↦
    uniformExpectation (fun ω ↦ ∏ j ∈ B,
      replaceCoordinate Y a (fun ω ↦ Y a ω - c) j ω)
  let morig : Finset ι → ℝ := fun B ↦
    uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω)
  let mconst : Finset ι → ℝ := fun B ↦
    uniformExpectation (fun ω ↦ ∏ j ∈ B,
      replaceCoordinate Y a (fun _ ↦ c) j ω)
  have hrestSub : (∏ B ∈ P.parts.erase A, msub B) =
      ∏ B ∈ P.parts.erase A, morig B := by
    apply Finset.prod_congr rfl
    intro B hB
    have hBparts := (Finset.mem_erase.mp hB).2
    have hBA : B ≠ A := (Finset.mem_erase.mp hB).1
    have haB : a ∉ B := by
      intro haB
      exact hBA (P.eq_of_mem_parts hBparts hA haB haA)
    exact blockMoment_replaceCoordinate_eq_of_not_mem Y a
      (fun ω ↦ Y a ω - c) B haB
  have hrestConst : (∏ B ∈ P.parts.erase A, mconst B) =
      ∏ B ∈ P.parts.erase A, morig B := by
    apply Finset.prod_congr rfl
    intro B hB
    have hBparts := (Finset.mem_erase.mp hB).2
    have hBA : B ≠ A := (Finset.mem_erase.mp hB).1
    have haB : a ∉ B := by
      intro haB
      exact hBA (P.eq_of_mem_parts hBparts hA haB haA)
    exact blockMoment_replaceCoordinate_eq_of_not_mem Y a
      (fun _ ↦ c) B haB
  change (∏ B ∈ P.parts, msub B) =
    (∏ B ∈ P.parts, morig B) - ∏ B ∈ P.parts, mconst B
  rw [← Finset.mul_prod_erase P.parts msub hA,
    ← Finset.mul_prod_erase P.parts morig hA,
    ← Finset.mul_prod_erase P.parts mconst hA,
    hrestSub, hrestConst]
  have hAblock : msub A = morig A - mconst A := by
    exact blockMoment_replace_sub Y a c A haA
  rw [hAblock]
  ring

theorem jointCumulantOn_replace_sub_eq
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    [DecidableEq ι] (Y : ι → Ω → ℝ) (a : ι) (c : ℝ)
    (hcard : 2 ≤ Fintype.card ι) :
    jointCumulantOn
        (replaceCoordinate Y a (fun ω ↦ Y a ω - c)) =
      jointCumulantOn Y := by
  classical
  let Z := replaceCoordinate Y a (fun _ ↦ c)
  have hzero : jointCumulantOn Z = 0 := by
    apply jointCumulantOn_eq_zero_of_constant_coordinate Z a c
    · intro ω
      simp [Z, replaceCoordinate]
    · exact hcard
  rw [jointCumulantOn, jointCumulantOn]
  calc
    (∑ P : Finpartition (Finset.univ : Finset ι),
        ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ∏ B ∈ P.parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ B,
              replaceCoordinate Y a (fun ω ↦ Y a ω - c) j ω)) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        (((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
            ∏ B ∈ P.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω) -
         ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
            ∏ B ∈ P.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ B, Z j ω)) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [partitionMomentProduct_replace_sub Y a c P]
        dsimp only [Z]
        ring
    _ = jointCumulantOn Y - jointCumulantOn Z := by
      rw [jointCumulantOn, jointCumulantOn, Finset.sum_sub_distrib]
    _ = jointCumulantOn Y := by rw [hzero, sub_zero]

def centerCoordinatesOn {Ω ι : Type*} [DecidableEq ι]
    (S : Finset ι) (Y : ι → Ω → ℝ) (c : ι → ℝ) : ι → Ω → ℝ :=
  fun j ω ↦ if j ∈ S then Y j ω - c j else Y j ω

theorem jointCumulantOn_centerCoordinatesOn
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (Y : ι → Ω → ℝ) (c : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) :
    jointCumulantOn (centerCoordinatesOn S Y c) = jointCumulantOn Y := by
  classical
  induction S using Finset.induction with
  | empty =>
      apply congrArg jointCumulantOn
      funext j ω
      simp [centerCoordinatesOn]
  | @insert a S ha ih =>
      have hfun : centerCoordinatesOn (insert a S) Y c =
          replaceCoordinate (centerCoordinatesOn S Y c) a
            (fun ω ↦ centerCoordinatesOn S Y c a ω - c a) := by
        funext j ω
        by_cases hja : j = a
        · subst j
          simp [centerCoordinatesOn, replaceCoordinate, ha]
        · simp [centerCoordinatesOn, replaceCoordinate, hja]
      rw [hfun, jointCumulantOn_replace_sub_eq
        (centerCoordinatesOn S Y c) a (c a) hcard]
      exact ih

theorem jointCumulantOn_sub_constants
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    [DecidableEq ι] (Y : ι → Ω → ℝ) (c : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) :
    jointCumulantOn (fun j ω ↦ Y j ω - c j) = jointCumulantOn Y := by
  have hcenter := jointCumulantOn_centerCoordinatesOn
    (Finset.univ : Finset ι) Y c hcard
  rw [show centerCoordinatesOn (Finset.univ : Finset ι) Y c =
      (fun j ω ↦ Y j ω - c j) by
    funext j ω
    simp [centerCoordinatesOn]] at hcenter
  exact hcenter

theorem signPairExpectation_signValue_pairs
    {α : Type*} [Fintype α] [DecidableEq α]
    (i j a b : α) :
    signPairExpectation (fun d₁ d₂ ↦
      (signValue d₁ i * signValue d₁ j) *
        (signValue d₂ a * signValue d₂ b)) =
      (if i = j then 1 else 0) * (if a = b then 1 else 0) := by
  rw [signPairExpectation,
    uniformExpectation_prod_factor
      (fun d₁ : SignLayer α ↦ signValue d₁ i * signValue d₁ j)
      (fun d₂ : SignLayer α ↦ signValue d₂ a * signValue d₂ b),
    uniformExpectation_signValue_pair,
    uniformExpectation_signValue_pair]

theorem signPairExpectation_sign_monomial
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (x y a b : α) :
    signPairExpectation (fun d₁ d₂ ↦
      c * signValue d₂ a * signValue d₂ b *
        signValue d₁ x * signValue d₁ y) =
      c * ((if x = y then 1 else 0) * (if a = b then 1 else 0)) := by
  calc
    _ = signPairExpectation (fun d₁ d₂ ↦
        c * ((signValue d₁ x * signValue d₁ y) *
          (signValue d₂ a * signValue d₂ b))) := by
      congr 1
      funext d₁ d₂
      ring
    _ = c * signPairExpectation (fun d₁ d₂ ↦
        (signValue d₁ x * signValue d₁ y) *
          (signValue d₂ a * signValue d₂ b)) :=
      signPairExpectation_const_mul c _
    _ = _ := by rw [signPairExpectation_signValue_pairs]

theorem scaled_randomProjection_entry_expansion {m r : ℕ}
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
  rw [projectionMean_sum_five_permute]
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
  rw [projectionMean_walshCharacter_comm b y]
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  field_simp
  rw [Real.sq_sqrt hcard.le]
  ring

theorem scaled_randomProjection_mean_entry {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (i j : WalshIndex m) :
    (walshCard m : ℝ) *
        signPairExpectation (fun d₁ d₂ ↦ randomProjection d₁ d₂ V i j) =
      ∑ a, ∑ x,
        walshCharacter i a * walshCharacter j a *
          normalizedWalsh m a x * (V * V.transpose) x x *
          normalizedWalsh m x a := by
  classical
  calc
    _ = signPairExpectation (fun d₁ d₂ ↦
        (walshCard m : ℝ) * randomProjection d₁ d₂ V i j) :=
      (signPairExpectation_const_mul (walshCard m : ℝ)
        (fun d₁ d₂ ↦ randomProjection d₁ d₂ V i j)).symm
    _ = signPairExpectation (fun d₁ d₂ ↦
        ∑ a, ∑ b, ∑ x, ∑ y,
          walshCharacter i a * walshCharacter j b * signValue d₂ a *
          signValue d₂ b * signValue d₁ x * signValue d₁ y *
          normalizedWalsh m a x * (V * V.transpose) x y *
          normalizedWalsh m y b) := by
      congr 1
      funext d₁ d₂
      exact scaled_randomProjection_entry_expansion V d₁ d₂ i j
    _ = ∑ a, ∑ b, ∑ x, ∑ y,
        signPairExpectation (fun d₁ d₂ ↦
          walshCharacter i a * walshCharacter j b * signValue d₂ a *
          signValue d₂ b * signValue d₁ x * signValue d₁ y *
          normalizedWalsh m a x * (V * V.transpose) x y *
          normalizedWalsh m y b) := by
      rw [signPairExpectation_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [signPairExpectation_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [signPairExpectation_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [signPairExpectation_sum]
    _ = _ := by
      have hmono (a b x y : WalshIndex m) :
          signPairExpectation (fun d₁ d₂ ↦
            walshCharacter i a * walshCharacter j b * signValue d₂ a *
            signValue d₂ b * signValue d₁ x * signValue d₁ y *
            normalizedWalsh m a x * (V * V.transpose) x y *
            normalizedWalsh m y b) =
          (walshCharacter i a * walshCharacter j b *
            normalizedWalsh m a x * (V * V.transpose) x y *
            normalizedWalsh m y b) *
              ((if x = y then 1 else 0) *
                (if a = b then 1 else 0)) := by
        let c := walshCharacter i a * walshCharacter j b *
          normalizedWalsh m a x * (V * V.transpose) x y *
          normalizedWalsh m y b
        calc
          _ = signPairExpectation (fun d₁ d₂ ↦
              c * signValue d₂ a * signValue d₂ b *
                signValue d₁ x * signValue d₁ y) := by
            congr 1
            funext d₁ d₂
            dsimp only [c]
            ring
          _ = _ := signPairExpectation_sign_monomial c x y a b
      simp_rw [hmono]
      simp

theorem scaled_randomProjection_mean_entry_eq {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : WalshIndex m) :
    (walshCard m : ℝ) *
        signPairExpectation (fun d₁ d₂ ↦ randomProjection d₁ d₂ V i j) =
      if i = j then (r : ℝ) else 0 := by
  rw [scaled_randomProjection_mean_entry]
  calc
    (∑ a, ∑ x,
        walshCharacter i a * walshCharacter j a *
          normalizedWalsh m a x * (V * V.transpose) x x *
          normalizedWalsh m x a) =
        ∑ a, (walshCharacter i a * walshCharacter j a) *
          (1 / (walshCard m : ℝ)) *
          (∑ x, (V * V.transpose) x x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hH := normalizedWalsh_mul_swap a x
      calc
        _ = (walshCharacter i a * walshCharacter j a) *
              (normalizedWalsh m a x * normalizedWalsh m x a) *
              (V * V.transpose) x x := by ring
        _ = _ := by rw [hH]
    _ = (∑ a, walshCharacter i a * walshCharacter j a) *
          (1 / (walshCard m : ℝ)) *
          (∑ x, (V * V.transpose) x x) := by
      rw [Finset.sum_mul]
      rw [Finset.sum_mul]
    _ = _ := by
      rw [sum_walshCharacter_pair, frameProjection_trace V hV]
      have hcard : (walshCard m : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : walshCard m ≠ 0)
      by_cases hij : i = j <;> simp [hij, hcard]

theorem randomProjection_mean_entry {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : WalshIndex m) :
    signPairExpectation (fun d₁ d₂ ↦ randomProjection d₁ d₂ V i j) =
      if i = j then (r : ℝ) / walshCard m else 0 := by
  have hscaled := scaled_randomProjection_mean_entry_eq V hV i j
  have hcard : (walshCard m : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : walshCard m ≠ 0)
  by_cases hij : i = j
  · rw [if_pos hij] at hscaled ⊢
    apply (eq_div_iff hcard).2
    simpa only [mul_comm] using hscaled
  · rw [if_neg hij] at hscaled ⊢
    exact (mul_eq_zero.mp hscaled).resolve_left hcard

theorem randomProjection_centered_mean_entry {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : WalshIndex m) :
    signPairExpectation (fun d₁ d₂ ↦
      (randomProjection d₁ d₂ V - ((r : ℝ) / walshCard m) • 1) i j) = 0 := by
  have hentry : (((r : ℝ) / walshCard m) •
      (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) i j =
        if i = j then (r : ℝ) / walshCard m else 0 := by
    simp [Matrix.one_apply]
  simp only [Matrix.sub_apply, hentry]
  rw [signPairExpectation_sub_const, randomProjection_mean_entry V hV i j]
  ring

theorem randomProjection_jointCumulant_centering {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    (∀ (q : ℕ), 2 ≤ q → ∀ i j : Fin q → WalshIndex m,
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦
          (randomProjection d.1 d.2 V - ((r : ℝ) / walshCard m) • 1)
            (i f) (j f)) =
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ randomProjection d.1 d.2 V (i f) (j f))) := by
  intro q hq i j
  have hcard : 2 ≤ Fintype.card (Fin q) := by simpa using hq
  simpa only [jointCumulant, Matrix.sub_apply] using
    (jointCumulantOn_sub_constants
      (fun (f : Fin q)
          (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) ↦
        randomProjection d.1 d.2 V (i f) (j f))
      (fun f : Fin q ↦
        (((r : ℝ) / walshCard m) •
          (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) (i f) (j f))
      hcard)

theorem projection_mean_and_centering {m r : ℕ}
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
  exact ⟨randomProjection_mean_entry V hV,
    randomProjection_centered_mean_entry V hV,
    randomProjection_jointCumulant_centering V⟩

#print axioms uniformExpectation_signValue_pair
#print axioms signPairExpectation_signValue_pairs
#print axioms randomProjection_mean_entry
#print axioms randomProjection_centered_mean_entry
#print axioms projection_mean_and_centering

end Problem56
