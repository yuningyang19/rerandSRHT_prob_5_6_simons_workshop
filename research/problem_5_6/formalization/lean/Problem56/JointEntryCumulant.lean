import Problem56.MixedCumulant
import Problem56.OccurrenceGraph
import Problem56.RademacherCumulant

/-!
Kernel-clean assembly toward the named joint-entry cumulant lemma.

The Walsh-covariance vanishing and the exact projection mean are independent
of the still-open graph-rank theorem.  The quantitative estimate is organized
below around the literal occurrence-partition expansion, so that the only
analytic input it will require is the exact graph-rank contraction inequality.
-/

open scoped BigOperators Matrix

namespace Problem56

set_option maxHeartbeats 8000000

private theorem uniformExpectation_const_family_mul
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (c : ι → ℝ) (Y : ι → Ω → ℝ) (B : Finset ι) :
    uniformExpectation (fun ω ↦ ∏ j ∈ B, c j * Y j ω) =
      (∏ j ∈ B, c j) * uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω) := by
  classical
  simp only [uniformExpectation]
  let C : ℝ := ∏ j ∈ B, c j
  calc
    (∑ ω, ∏ j ∈ B, c j * Y j ω) / (Fintype.card Ω : ℝ) =
        (∑ ω, C * ∏ j ∈ B, Y j ω) / (Fintype.card Ω : ℝ) := by
      congr 2
      funext ω
      simp only [C]
      rw [Finset.prod_mul_distrib]
    _ = (C * ∑ ω, ∏ j ∈ B, Y j ω) / (Fintype.card Ω : ℝ) := by
      rw [Finset.mul_sum]
    _ = C * ((∑ ω, ∏ j ∈ B, Y j ω) / (Fintype.card Ω : ℝ)) := by
      ring

theorem jointCumulantOn_const_family_mul
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (Y : ι → Ω → ℝ) :
    jointCumulantOn (fun j ω ↦ c j * Y j ω) =
      (∏ j, c j) * jointCumulantOn Y := by
  classical
  unfold jointCumulantOn
  calc
    (∑ P : Finpartition (Finset.univ : Finset ι),
        ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ∏ B ∈ P.parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ B, c j * Y j ω)) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ((∏ j, c j) *
            ∏ B ∈ P.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω)) := by
        apply Finset.sum_congr rfl
        intro P _
        congr 1
        rw [Finset.prod_congr rfl (fun B hB ↦
          uniformExpectation_const_family_mul c Y B)]
        rw [Finset.prod_mul_distrib]
        have hpartition :
            ∏ B ∈ P.parts, ∏ j ∈ B, c j = ∏ j, c j := by
          calc
            ∏ B ∈ P.parts, ∏ j ∈ B, c j =
                ∏ j ∈ P.parts.biUnion id, c j :=
              (Finset.prod_biUnion P.disjoint).symm
            _ = ∏ j, c j := by rw [P.biUnion_parts]
        rw [hpartition]
    _ = (∏ j, c j) *
        ∑ P : Finpartition (Finset.univ : Finset ι),
          ((-1 : ℝ) ^ (P.parts.card - 1) *
            (Nat.factorial (P.parts.card - 1) : ℝ)) *
            ∏ B ∈ P.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      ring

private theorem blockMoment_sum_expansion
    {Ω ι α : Type*} [Fintype Ω] [Fintype ι] [Fintype α]
    [DecidableEq ι]
    (Y : ι → α → Ω → ℝ) (B : Finset ι) :
    uniformExpectation (fun ω ↦ ∏ j ∈ B, ∑ a, Y j a ω) =
      ∑ g : B → α,
        uniformExpectation (fun ω ↦ ∏ j : B, Y j.1 (g j) ω) := by
  classical
  calc
    uniformExpectation (fun ω ↦ ∏ j ∈ B, ∑ a, Y j a ω) =
        uniformExpectation (fun ω ↦ ∑ g : B → α,
          ∏ j : B, Y j.1 (g j) ω) := by
      congr 1
      funext ω
      calc
        (∏ j ∈ B, ∑ a, Y j a ω) =
            ∏ j : B, ∑ a, Y j.1 a ω :=
          Finset.prod_subtype B (fun _ ↦ Iff.rfl) _
        _ = ∑ g : B → α, ∏ j : B, Y j.1 (g j) ω :=
          Fintype.prod_sum (fun j : B ↦ fun a ↦ Y j.1 a ω)
    _ = _ := uniformExpectation_sum _

private noncomputable def partitionSigmaEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι)) :
    (Σ B : P.parts, B.1) ≃ ι := by
  classical
  apply Equiv.ofBijective (fun z : Σ B : P.parts, B.1 ↦ z.2.1)
  constructor
  · rintro ⟨B, j⟩ ⟨C, k⟩ h
    change j.1 = k.1 at h
    have hkB : k.1 ∈ B.1 := by
      rw [← h]
      exact j.2
    have hBC : B = C := Subtype.ext (P.eq_of_mem_parts B.2 C.2 hkB k.2)
    subst C
    have hjk : j = k := Subtype.ext h
    subst k
    rfl
  · intro j
    refine ⟨⟨⟨P.part j, P.part_mem.mpr (Finset.mem_univ j)⟩,
      ⟨j, P.mem_part_self.mpr (Finset.mem_univ j)⟩⟩, rfl⟩

private def piSigmaCurryEquiv
    {β : Type*} {γ : β → Type*} {α : Type*} :
    (∀ b, γ b → α) ≃ ((Σ b, γ b) → α) where
  toFun g z := g z.1 z.2
  invFun g b x := g ⟨b, x⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def arrowEquivOfEquiv
    {σ ι α : Type*} (e : σ ≃ ι) : (σ → α) ≃ (ι → α) where
  toFun g i := g (e.symm i)
  invFun g s := g (e s)
  left_inv g := by funext s; simp
  right_inv g := by funext i; simp

private noncomputable def partitionChoiceEquiv
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∀ B : P.parts, B.1 → α) ≃ (ι → α) :=
  piSigmaCurryEquiv.trans (arrowEquivOfEquiv (partitionSigmaEquiv P))

private theorem partitionChoiceEquiv_apply_of_mem
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (Finset.univ : Finset ι))
    (g : ∀ B : P.parts, B.1 → α) (B : P.parts) (j : B.1) :
    partitionChoiceEquiv P g j.1 = g B j := by
  let e := partitionSigmaEquiv P
  have hz : e.symm j.1 = ⟨B, j⟩ := by
    apply e.injective
    have hepair : e ⟨B, j⟩ = j.1 := rfl
    rw [e.apply_symm_apply, hepair]
  change g (e.symm j.1).1 (e.symm j.1).2 = g B j
  rw [hz]

private theorem partitionMomentProduct_sum_expansion
    {Ω ι α : Type*} [Fintype Ω] [Fintype ι] [Fintype α]
    [DecidableEq ι]
    (Y : ι → α → Ω → ℝ)
    (P : Finpartition (Finset.univ : Finset ι)) :
    (∏ B ∈ P.parts,
      uniformExpectation (fun ω ↦ ∏ j ∈ B, ∑ a, Y j a ω)) =
      ∑ g : ι → α,
        ∏ B ∈ P.parts,
          uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j (g j) ω) := by
  classical
  let e := partitionChoiceEquiv (α := α) P
  calc
    (∏ B ∈ P.parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ B, ∑ a, Y j a ω)) =
      ∏ B : P.parts,
        uniformExpectation (fun ω ↦ ∏ j ∈ B.1, ∑ a, Y j a ω) :=
        Finset.prod_subtype P.parts (fun _ ↦ Iff.rfl) _
    _ = ∏ B : P.parts, ∑ g : B.1 → α,
        uniformExpectation
          (fun ω ↦ ∏ j : B.1, Y j.1 (g j) ω) := by
      apply Finset.prod_congr rfl
      intro B _
      exact blockMoment_sum_expansion Y B.1
    _ = ∑ g : ∀ B : P.parts, B.1 → α,
        ∏ B : P.parts,
          uniformExpectation
            (fun ω ↦ ∏ j : B.1, Y j.1 (g B j) ω) := by
      exact Fintype.prod_sum (fun B : P.parts ↦ fun g : B.1 → α ↦
        uniformExpectation
          (fun ω ↦ ∏ j : B.1, Y j.1 (g j) ω))
    _ = ∑ g : ι → α,
        ∏ B : P.parts,
          uniformExpectation (fun ω ↦ ∏ j : B.1, Y j.1 (g j.1) ω) := by
      apply Fintype.sum_equiv e
      intro g
      apply Finset.prod_congr rfl
      intro B _
      congr 1
      funext ω
      apply Finset.prod_congr rfl
      intro j hj
      rw [partitionChoiceEquiv_apply_of_mem P g B j]
    _ = ∑ g : ι → α,
        ∏ B ∈ P.parts,
          uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j (g j) ω) := by
      apply Finset.sum_congr rfl
      intro g _
      calc
        (∏ B : P.parts,
            uniformExpectation (fun ω ↦ ∏ j : B.1, Y j.1 (g j.1) ω)) =
          ∏ B : P.parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ B.1, Y j (g j) ω) := by
          apply Finset.prod_congr rfl
          intro B _
          congr 1
          funext ω
          exact (Finset.prod_subtype B.1 (fun _ ↦ Iff.rfl)
            (fun j ↦ Y j (g j) ω)).symm
        _ = ∏ B ∈ P.parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j (g j) ω) :=
          (Finset.prod_subtype P.parts (fun _ ↦ Iff.rfl)
            (fun B ↦ uniformExpectation
              (fun ω ↦ ∏ j ∈ B, Y j (g j) ω))).symm

theorem jointCumulantOn_sum_family
    {Ω ι α : Type*} [Fintype Ω] [Fintype ι] [Fintype α]
    [DecidableEq ι]
    (Y : ι → α → Ω → ℝ) :
    jointCumulantOn (fun j ω ↦ ∑ a, Y j a ω) =
      ∑ g : ι → α, jointCumulantOn (fun j ω ↦ Y j (g j) ω) := by
  classical
  unfold jointCumulantOn
  calc
    (∑ P : Finpartition (Finset.univ : Finset ι),
        ((-1 : ℝ) ^ (P.parts.card - 1) *
          (Nat.factorial (P.parts.card - 1) : ℝ)) *
          ∏ B ∈ P.parts,
            uniformExpectation (fun ω ↦ ∏ j ∈ B, ∑ a, Y j a ω)) =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        ∑ g : ι → α,
          (((-1 : ℝ) ^ (P.parts.card - 1) *
            (Nat.factorial (P.parts.card - 1) : ℝ)) *
            ∏ B ∈ P.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j (g j) ω)) := by
      apply Finset.sum_congr rfl
      intro P _
      rw [partitionMomentProduct_sum_expansion]
      exact Finset.mul_sum _ _ _
    _ = ∑ g : ι → α,
        ∑ P : Finpartition (Finset.univ : Finset ι),
          (((-1 : ℝ) ^ (P.parts.card - 1) *
            (Nat.factorial (P.parts.card - 1) : ℝ)) *
            ∏ B ∈ P.parts,
              uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j (g j) ω)) := by
      rw [Finset.sum_comm]

private theorem jointCumulant_walsh_sample_transform
    {m q : ℕ} (s : WalshIndex m)
    (Y : Fin q →
      (SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) → ℝ) :
    jointCumulant
        (fun f (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) ↦
          Y f (modulateSign s d.1, translateSign s d.2)) =
      jointCumulant Y := by
  classical
  unfold jointCumulant jointCumulantOn
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  change signPairExpectation (fun d₁ d₂ ↦
      ∏ j ∈ B, Y j (modulateSign s d₁, translateSign s d₂)) =
    signPairExpectation (fun d₁ d₂ ↦ ∏ j ∈ B, Y j (d₁, d₂))
  simpa only using signPairExpectation_walsh_symmetry s
    (fun d₁ d₂ ↦ ∏ j ∈ B, Y j (d₁, d₂))

private theorem randomProjection_walsh_transform_entry
    {m r : ℕ} (s : WalshIndex m)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (a b : WalshIndex m) :
    randomProjection (modulateSign s d₁) (translateSign s d₂) V a b =
      (walshCharacter s a * walshCharacter s b) *
        randomProjection d₁ d₂ V a b := by
  rw [randomProjection_walsh_symmetry s V d₁ d₂]
  classical
  simp [walshModulation, Matrix.mul_apply, Matrix.diagonal_apply]
  ring

private theorem walshCharacter_sum
    {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (s : WalshIndex m) (z : α → WalshIndex m) :
    walshCharacter s (∑ a, z a) = ∏ a, walshCharacter s (z a) := by
  classical
  have aux (S : Finset α) :
      walshCharacter s (∑ a ∈ S, z a) =
        ∏ a ∈ S, walshCharacter s (z a) := by
    induction S using Finset.induction_on with
    | empty =>
        have hz : walshDot s 0 = 0 := by simp [walshDot]
        simp [walshCharacter, hz]
    | @insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          walshCharacter_add_right', ih]
  simpa using aux Finset.univ

private theorem joint_entry_cumulant_covariance
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) (s : WalshIndex m) :
    jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ (walshCard m : ℝ) *
          randomProjection d.1 d.2 V (i f) (j f)) =
      walshCharacter s (∑ f, (i f + j f)) *
        jointCumulant
          (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
          (fun f d ↦ (walshCard m : ℝ) *
            randomProjection d.1 d.2 V (i f) (j f)) := by
  let X : Fin q →
      (SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) → ℝ :=
    fun f d ↦ (walshCard m : ℝ) *
      randomProjection d.1 d.2 V (i f) (j f)
  let c : Fin q → ℝ :=
    fun f ↦ walshCharacter s (i f) * walshCharacter s (j f)
  calc
    jointCumulant X =
        jointCumulant
          (fun f (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) ↦
            X f (modulateSign s d.1, translateSign s d.2)) :=
      (jointCumulant_walsh_sample_transform (q := q) s X).symm
    _ = jointCumulant (fun f d ↦ c f * X f d) := by
      congr 1
      funext f d
      simp only [X, c]
      rw [randomProjection_walsh_transform_entry]
      ring
    _ = (∏ f, c f) * jointCumulant X :=
      jointCumulantOn_const_family_mul c X
    _ = walshCharacter s (∑ f, (i f + j f)) * jointCumulant X := by
      congr 1
      rw [walshCharacter_sum]
      apply Finset.prod_congr rfl
      intro f _
      exact (walshCharacter_add_right' s (i f) (j f)).symm

theorem joint_entry_cumulant_vanish
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    (∑ f, (i f + j f)) ≠ 0 →
      jointCumulant
        (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ (walshCard m : ℝ) *
          randomProjection d.1 d.2 V (i f) (j f)) = 0 := by
  intro hxor
  obtain ⟨s, hs⟩ := exists_walshCharacter_eq_neg_one _ hxor
  have hcov := joint_entry_cumulant_covariance V i j s
  rw [hs] at hcov
  linarith

theorem joint_entry_projection_mean
    {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V) :
    ∀ a b, signPairExpectation
        (fun d₁ d₂ ↦ randomProjection d₁ d₂ V a b) =
      if a = b then (r : ℝ) / walshCard m else 0 :=
  randomProjection_mean_entry V hV

/-! ## Multilinear expansion into concrete coordinate labels -/

abbrev ProjectionEntryLabel (m : ℕ) :=
  (WalshIndex m × WalshIndex m) × (WalshIndex m × WalshIndex m)

private noncomputable def projectionEntryCoefficient
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (a b : WalshIndex m) (L : ProjectionEntryLabel m) : ℝ :=
  walshCharacter a L.1.1 * walshCharacter b L.1.2 *
    normalizedWalsh m L.1.1 L.2.1 *
    (V * V.transpose) L.2.1 L.2.2 *
    normalizedWalsh m L.2.2 L.1.2

private def projectionEntrySignMonomial
    {m : ℕ} (L : ProjectionEntryLabel m)
    (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) : ℝ :=
  signValue d.2 L.1.1 * signValue d.2 L.1.2 *
    signValue d.1 L.2.1 * signValue d.1 L.2.2

private theorem scaled_randomProjection_entry_expansion_label
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (i j : WalshIndex m) :
    (walshCard m : ℝ) * randomProjection d₁ d₂ V i j =
      ∑ L : ProjectionEntryLabel m,
        projectionEntryCoefficient V i j L *
          projectionEntrySignMonomial L (d₁, d₂) := by
  rw [scaled_randomProjection_entry_expansion]
  simp only [ProjectionEntryLabel, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [projectionEntryCoefficient, projectionEntrySignMonomial]
  ring

/-- Exact finite multilinear expansion before applying the product-cumulant
partition formula.  This is useful independently of the subsequent
connected-even reindexing. -/
theorem joint_entry_label_expansion
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    jointCumulant
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) *
        randomProjection d.1 d.2 V (i f) (j f)) =
      ∑ labels : Fin q → ProjectionEntryLabel m,
        (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
          jointCumulant
            (fun f d ↦ projectionEntrySignMonomial (labels f) d) := by
  classical
  calc
    jointCumulant
        (fun f (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) ↦
          (walshCard m : ℝ) *
            randomProjection d.1 d.2 V (i f) (j f)) =
      jointCumulant (fun f d ↦ ∑ L : ProjectionEntryLabel m,
        projectionEntryCoefficient V (i f) (j f) L *
          projectionEntrySignMonomial L d) := by
        congr 1
        funext f d
        exact scaled_randomProjection_entry_expansion_label
          V d.1 d.2 (i f) (j f)
    _ = ∑ labels : Fin q → ProjectionEntryLabel m,
        jointCumulant (fun f d ↦
          projectionEntryCoefficient V (i f) (j f) (labels f) *
            projectionEntrySignMonomial (labels f) d) := by
      exact jointCumulantOn_sum_family _
    _ = ∑ labels : Fin q → ProjectionEntryLabel m,
        (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
          jointCumulant
            (fun f d ↦ projectionEntrySignMonomial (labels f) d) := by
      apply Finset.sum_congr rfl
      intro labels _
      exact jointCumulantOn_const_family_mul
        (fun f ↦ projectionEntryCoefficient V (i f) (j f) (labels f))
        (fun f d ↦ projectionEntrySignMonomial (labels f) d)

/-! ## Fixed-label connected product-cumulant formula -/

private def sameEntryFactorSetoid (q : ℕ) : Setoid (Fin q × Fin 4) where
  r z z' := z.1 = z'.1
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

private noncomputable def entryFactorPartition (q : ℕ) :
    Finpartition (Finset.univ : Finset (Fin q × Fin 4)) := by
  classical
  exact Finpartition.ofSetoid (sameEntryFactorSetoid q)

private noncomputable def entryFactorBlock {q : ℕ} (f : Fin q) :
    Finset (Fin q × Fin 4) :=
  (entryFactorPartition q).part (f, 0)

@[simp] private theorem mem_entryFactorBlock_iff
    {q : ℕ} (f : Fin q) (z : Fin q × Fin 4) :
    z ∈ entryFactorBlock f ↔ f = z.1 := by
  classical
  rw [entryFactorBlock, entryFactorPartition,
    Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

private noncomputable def entryFactorBlockEquiv (q : ℕ) :
    Fin q ≃ (entryFactorPartition q).parts := by
  classical
  apply Equiv.ofBijective (fun f : Fin q ↦
    ⟨entryFactorBlock f, by
      rw [entryFactorBlock]
      exact (entryFactorPartition q).part_mem.mpr (Finset.mem_univ _)⟩)
  constructor
  · intro f g h
    have hmem : (f, (0 : Fin 4)) ∈ entryFactorBlock f := by simp
    have hblocks : entryFactorBlock f = entryFactorBlock g :=
      congrArg Subtype.val h
    rw [hblocks, mem_entryFactorBlock_iff] at hmem
    exact hmem.symm
  · intro B
    obtain ⟨z, hz⟩ := (entryFactorPartition q).nonempty_of_mem_parts B.2
    refine ⟨z.1, Subtype.ext ?_⟩
    exact (entryFactorPartition q).eq_of_mem_parts
      (by
        change (entryFactorPartition q).part (z.1, 0) ∈
          (entryFactorPartition q).parts
        exact (entryFactorPartition q).part_mem.mpr (Finset.mem_univ _))
      B.2 (by simp) hz

private noncomputable def factorOccurrenceEquiv
    {q : ℕ} (f : Fin q) : Fin 4 ≃ entryFactorBlock f := by
  classical
  apply Equiv.ofBijective (fun k : Fin 4 ↦
    ⟨(f, k), (mem_entryFactorBlock_iff f (f, k)).mpr rfl⟩)
  constructor
  · intro k l h
    exact congrArg (fun z : entryFactorBlock f ↦ z.1.2) h
  · intro z
    refine ⟨z.1.2, Subtype.ext ?_⟩
    apply Prod.ext
    · exact (mem_entryFactorBlock_iff f z.1).mp z.2
    · rfl

private def projectionOccurrenceVariable
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m) :
    (Fin q × Fin 4) →
      (SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) → ℝ
  | (f, k), d =>
      if k = 0 then signValue d.2 (labels f).1.1
      else if k = 1 then signValue d.2 (labels f).1.2
      else if k = 2 then signValue d.1 (labels f).2.1
      else signValue d.1 (labels f).2.2

private theorem entryFactorBlock_product
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m) (f : Fin q)
    (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) :
    (∏ z ∈ entryFactorBlock f, projectionOccurrenceVariable labels z d) =
      projectionEntrySignMonomial (labels f) d := by
  classical
  rw [Finset.prod_subtype (entryFactorBlock f) (fun _ ↦ Iff.rfl)]
  rw [← Fintype.prod_equiv (factorOccurrenceEquiv f)
      (fun k : Fin 4 ↦ projectionOccurrenceVariable labels (f, k) d)
      (fun z : entryFactorBlock f ↦ projectionOccurrenceVariable labels z.1 d)
      (fun _ ↦ rfl)]
  rw [Fin.prod_univ_four]
  simp [projectionOccurrenceVariable, projectionEntrySignMonomial]

/-- For a fixed coordinate-label assignment, the cumulant of the four-sign
monomials is exactly the connected-partition sum supplied by I09's closed
finite product-cumulant identity. -/
theorem joint_entry_sign_connected_partition_expansion
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m) :
    jointCumulant
        (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ projectionEntrySignMonomial (labels f) d) =
      connectedPartitionCumulantSum
        (projectionOccurrenceVariable labels) (entryFactorPartition q) := by
  classical
  let τ := entryFactorPartition q
  let Y := projectionOccurrenceVariable labels
  let Z : τ.parts →
      (SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) → ℝ :=
    fun B d ↦ ∏ z ∈ B.1, Y z d
  calc
    jointCumulant (fun f d ↦ projectionEntrySignMonomial (labels f) d) =
        jointCumulant (fun f d ↦ Z (entryFactorBlockEquiv q f) d) := by
      congr 1
      funext f d
      change projectionEntrySignMonomial (labels f) d =
        ∏ z ∈ entryFactorBlock f, projectionOccurrenceVariable labels z d
      exact (entryFactorBlock_product labels f d).symm
    _ = jointCumulantOn Z :=
      jointCumulantOn_equiv_index (entryFactorBlockEquiv q) Z
    _ = connectedPartitionCumulantSum Y τ := by
      exact product_cumulant_connected_identity Y τ

/-! ## Cumulants of coordinates of one finite sign layer -/

private theorem uniformExpectation_equiv
    {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω' ≃ Ω) (F : Ω → ℝ) :
    uniformExpectation (fun ω' ↦ F (e ω')) = uniformExpectation F := by
  classical
  unfold uniformExpectation
  have hsum : (∑ ω', F (e ω')) = ∑ ω, F ω :=
    Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  rw [hsum, Fintype.card_congr e]

private theorem jointCumulantOn_sample_equiv
    {Ω Ω' ι : Type*} [Fintype Ω] [Fintype Ω'] [Fintype ι]
    [DecidableEq ι] (e : Ω' ≃ Ω) (Y : ι → Ω → ℝ) :
    jointCumulantOn (fun j ω' ↦ Y j (e ω')) = jointCumulantOn Y := by
  classical
  unfold jointCumulantOn
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  simpa only using uniformExpectation_equiv e
    (fun ω ↦ ∏ j ∈ B, Y j ω)

private theorem jointCumulantOn_lift_fst
    {Ω₁ Ω₂ ι : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω₁ → ℝ) :
    jointCumulantOn (fun j (z : Ω₁ × Ω₂) ↦ Y j z.1) =
      jointCumulantOn Y := by
  classical
  unfold jointCumulantOn
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  let F : Ω₁ → ℝ := fun ω ↦ ∏ j ∈ B, Y j ω
  calc
    uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1) =
        uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.1 * (1 : ℝ)) := by
      congr 1
      funext z
      ring
    _ = uniformExpectation F *
        uniformExpectation (fun _ : Ω₂ ↦ (1 : ℝ)) :=
      uniformExpectation_prod_factor (Ω₂ := Ω₂) F (fun _ : Ω₂ ↦ (1 : ℝ))
    _ = uniformExpectation F := by
      rw [uniformExpectation_one_of_nonempty, mul_one]

private theorem jointCumulantOn_lift_snd
    {Ω₁ Ω₂ ι : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω₂ → ℝ) :
    jointCumulantOn (fun j (z : Ω₁ × Ω₂) ↦ Y j z.2) =
      jointCumulantOn Y := by
  classical
  unfold jointCumulantOn
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  let F : Ω₂ → ℝ := fun ω ↦ ∏ j ∈ B, Y j ω
  calc
    uniformExpectation (fun z : Ω₁ × Ω₂ ↦ F z.2) =
        uniformExpectation (fun z : Ω₁ × Ω₂ ↦ (1 : ℝ) * F z.2) := by
      congr 1
      funext z
      ring
    _ = uniformExpectation (fun _ : Ω₁ ↦ (1 : ℝ)) *
        uniformExpectation F :=
      uniformExpectation_prod_factor (Ω₁ := Ω₁)
        (fun _ : Ω₁ ↦ (1 : ℝ)) F
    _ = uniformExpectation F := by
      rw [uniformExpectation_one_of_nonempty, one_mul]

private noncomputable def signLayerSplitEquiv
    {κ : Type*} [DecidableEq κ] (a : κ) :
    Bool × SignLayer {x : κ // x ≠ a} ≃ SignLayer κ where
  toFun z x := if h : x = a then z.1 else z.2 ⟨x, h⟩
  invFun d := (d a, fun x ↦ d x.1)
  left_inv z := by
    apply Prod.ext
    · simp
    · funext x
      simp [x.2]
  right_inv d := by
    funext x
    by_cases h : x = a
    · subst x
      simp
    · simp [h]

@[simp] private theorem signLayerSplitEquiv_apply_anchor
    {κ : Type*} [DecidableEq κ] (a : κ)
    (z : Bool × SignLayer {x : κ // x ≠ a}) :
    signLayerSplitEquiv a z a = z.1 := by
  simp [signLayerSplitEquiv]

@[simp] private theorem signLayerSplitEquiv_apply_ne
    {κ : Type*} [DecidableEq κ] (a x : κ) (hx : x ≠ a)
    (z : Bool × SignLayer {x : κ // x ≠ a}) :
    signLayerSplitEquiv a z x = z.2 ⟨x, hx⟩ := by
  simp [signLayerSplitEquiv, hx]

private theorem jointCumulantOn_signValue_constant
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c : ι → κ) (a : κ) (hconstant : ∀ t, c t = a) :
    jointCumulantOn (fun t (d : SignLayer κ) ↦ signValue d (c t)) =
      rademacherCumulant (Fintype.card ι) := by
  classical
  let e := signLayerSplitEquiv a
  let Y : ι → SignLayer κ → ℝ := fun t d ↦ signValue d (c t)
  let R : ι → Bool → ℝ := fun _ b ↦ if b then (-1 : ℝ) else 1
  calc
    jointCumulantOn Y =
        jointCumulantOn (fun t z ↦ Y t (e z)) :=
      (jointCumulantOn_sample_equiv e Y).symm
    _ = jointCumulantOn (fun t (z : Bool × SignLayer {x : κ // x ≠ a}) ↦
        R t z.1) := by
      congr 1
      funext t z
      simp only [Y, R, hconstant t, signValue]
      have he : e z a = z.1 := by simp [e]
      rw [he]
    _ = jointCumulantOn R := jointCumulantOn_lift_fst R
    _ = rademacherCumulant (Fintype.card ι) := by
      let idx : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
      have hidx := jointCumulantOn_equiv_index idx R
      simpa [R, rademacherCumulant, jointCumulant] using hidx.symm

private theorem jointCumulantOn_signValue_nonconstant
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (c : ι → κ) (a t : ι) (hne : c t ≠ c a) :
    jointCumulantOn (fun u (d : SignLayer κ) ↦ signValue d (c u)) = 0 := by
  classical
  let anchor := c a
  let e := signLayerSplitEquiv anchor
  let Y : ι → SignLayer κ → ℝ := fun u d ↦ signValue d (c u)
  let Y' : ι → (Bool × SignLayer {x : κ // x ≠ anchor}) → ℝ :=
    fun u z ↦ Y u (e z)
  let A : Finset ι := Finset.univ.filter (fun u ↦ c u ≠ anchor)
  let B : Finset ι := Finset.univ.filter (fun u ↦ c u = anchor)
  have hcover : A ∪ B = Finset.univ := by
    ext u
    by_cases hu : c u = anchor <;> simp [A, B, hu]
  have hdisjoint : Disjoint A B := by
    exact Finset.disjoint_left.mpr (by
      intro u huA huB
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at huA
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at huB
      exact huA huB)
  have hA : A.Nonempty := by
    refine ⟨t, by simpa [A, anchor] using hne⟩
  have hB : B.Nonempty := by
    exact ⟨a, by simp [B, anchor]⟩
  have hfirst : ∀ u ∈ A, ∀ x y z, Y' u (x, z) = Y' u (y, z) := by
    intro u hu x y z
    have hcu : c u ≠ anchor := by simpa [A] using hu
    simp [Y', Y, e, signValue, signLayerSplitEquiv_apply_ne anchor (c u) hcu]
  have hsecond : ∀ u ∈ B, ∀ x y z, Y' u (z, x) = Y' u (z, y) := by
    intro u hu x y z
    have hcu : c u = anchor := by simpa [B] using hu
    simp [Y', Y, e, hcu, signValue]
  have hvanish : jointCumulantOn Y' = 0 :=
    independent_families_mixed_cumulant_vanish_on
      Y' A B hcover hdisjoint hfirst hsecond hA hB
  calc
    jointCumulantOn Y = jointCumulantOn Y' :=
      (jointCumulantOn_sample_equiv e Y).symm
    _ = 0 := hvanish

private def boolNotEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

private theorem rademacherCumulant_eq_zero_of_odd
    {b : ℕ} (hodd : Odd b) : rademacherCumulant b = 0 := by
  let R : Fin b → Bool → ℝ := fun _ ξ ↦ if ξ then (-1 : ℝ) else 1
  have hflip :
      jointCumulantOn (fun f ξ ↦ R f (boolNotEquiv ξ)) =
        jointCumulantOn R :=
    jointCumulantOn_sample_equiv boolNotEquiv R
  have hpoint : (fun f ξ ↦ R f (boolNotEquiv ξ)) =
      (fun f ξ ↦ (-1 : ℝ) * R f ξ) := by
    funext f ξ
    cases ξ <;> norm_num [R, boolNotEquiv]
  rw [hpoint] at hflip
  have hscale := jointCumulantOn_const_family_mul
    (Ω := Bool) (ι := Fin b) (fun _ ↦ (-1 : ℝ)) R
  have hprod : (∏ _f : Fin b, (-1 : ℝ)) = (-1 : ℝ) ^ b := by simp
  rw [hprod] at hscale
  obtain ⟨k, rfl⟩ := hodd
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpow] at hscale
  unfold rademacherCumulant jointCumulant
  linarith

private def projectionOccurrenceIsMiddle {q : ℕ} (z : Fin q × Fin 4) : Prop :=
  z.2 = 0 ∨ z.2 = 1

private def projectionOccurrenceCoordinate
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (z : Fin q × Fin 4) : WalshIndex m :=
  if z.2 = 0 then (labels z.1).1.1
  else if z.2 = 1 then (labels z.1).1.2
  else if z.2 = 2 then (labels z.1).2.1
  else (labels z.1).2.2

private theorem projectionOccurrenceVariable_of_middle
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (z : Fin q × Fin 4) (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
    (hz : projectionOccurrenceIsMiddle z) :
    projectionOccurrenceVariable labels z d =
      signValue d.2 (projectionOccurrenceCoordinate labels z) := by
  rcases z with ⟨f, k⟩
  fin_cases k <;>
    simp [projectionOccurrenceIsMiddle, projectionOccurrenceVariable,
      projectionOccurrenceCoordinate] at hz ⊢

private theorem projectionOccurrenceVariable_of_not_middle
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (z : Fin q × Fin 4) (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
    (hz : ¬projectionOccurrenceIsMiddle z) :
    projectionOccurrenceVariable labels z d =
      signValue d.1 (projectionOccurrenceCoordinate labels z) := by
  rcases z with ⟨f, k⟩
  fin_cases k <;>
    simp [projectionOccurrenceIsMiddle, projectionOccurrenceVariable,
      projectionOccurrenceCoordinate] at hz ⊢

private def OccurrenceBlockLayerPure {q : ℕ} (B : Finset (Fin q × Fin 4)) : Prop :=
  (∀ z : B, projectionOccurrenceIsMiddle z.1) ∨
    (∀ z : B, ¬projectionOccurrenceIsMiddle z.1)

private def OccurrenceBlockLabelsConstant
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (B : Finset (Fin q × Fin 4)) : Prop :=
  ∀ z w : B,
    projectionOccurrenceCoordinate labels z.1 =
      projectionOccurrenceCoordinate labels w.1

private noncomputable def occurrenceBlockCumulantValue
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (B : Finset (Fin q × Fin 4)) : ℝ := by
  classical
  exact if OccurrenceBlockLayerPure B ∧ OccurrenceBlockLabelsConstant labels B then
    rademacherCumulant B.card
  else 0

private theorem projectionOccurrence_block_cumulant
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (B : Finset (Fin q × Fin 4)) (hB : B.Nonempty) :
    jointCumulantOn (fun z : B ↦ projectionOccurrenceVariable labels z.1) =
      occurrenceBlockCumulantValue labels B := by
  classical
  let _ : Nonempty B := Finset.nonempty_coe_sort.mpr hB
  let c : B → WalshIndex m :=
    fun z ↦ projectionOccurrenceCoordinate labels z.1
  rw [occurrenceBlockCumulantValue]
  by_cases hpure : OccurrenceBlockLayerPure B
  · by_cases hconstant : OccurrenceBlockLabelsConstant labels B
    · rw [if_pos ⟨hpure, hconstant⟩]
      let z0 : B := ⟨Classical.choose hB, Classical.choose_spec hB⟩
      rcases hpure with hmiddle | hnotMiddle
      · have hvariables :
            (fun z : B ↦ projectionOccurrenceVariable labels z.1) =
              (fun z d ↦ signValue d.2 (c z)) := by
          funext z d
          exact projectionOccurrenceVariable_of_middle labels z.1 d (hmiddle z)
        rw [hvariables]
        calc
          jointCumulantOn (fun z (d : SignLayer (WalshIndex m) ×
              SignLayer (WalshIndex m)) ↦ signValue d.2 (c z)) =
              jointCumulantOn
                (fun z (d : SignLayer (WalshIndex m)) ↦ signValue d (c z)) :=
            jointCumulantOn_lift_snd
              (Ω₁ := SignLayer (WalshIndex m))
              (Ω₂ := SignLayer (WalshIndex m))
              (fun z (d : SignLayer (WalshIndex m)) ↦ signValue d (c z))
          _ = rademacherCumulant (Fintype.card B) :=
            jointCumulantOn_signValue_constant c (c z0)
              (fun z ↦ hconstant z z0)
          _ = rademacherCumulant B.card := by simp
      · have hvariables :
            (fun z : B ↦ projectionOccurrenceVariable labels z.1) =
              (fun z d ↦ signValue d.1 (c z)) := by
          funext z d
          exact projectionOccurrenceVariable_of_not_middle labels z.1 d
            (hnotMiddle z)
        rw [hvariables]
        calc
          jointCumulantOn (fun z (d : SignLayer (WalshIndex m) ×
              SignLayer (WalshIndex m)) ↦ signValue d.1 (c z)) =
              jointCumulantOn
                (fun z (d : SignLayer (WalshIndex m)) ↦ signValue d (c z)) :=
            jointCumulantOn_lift_fst
              (Ω₁ := SignLayer (WalshIndex m))
              (Ω₂ := SignLayer (WalshIndex m))
              (fun z (d : SignLayer (WalshIndex m)) ↦ signValue d (c z))
          _ = rademacherCumulant (Fintype.card B) :=
            jointCumulantOn_signValue_constant c (c z0)
              (fun z ↦ hconstant z z0)
          _ = rademacherCumulant B.card := by simp
    · rw [if_neg (fun h ↦ hconstant h.2)]
      simp only [OccurrenceBlockLabelsConstant] at hconstant
      push Not at hconstant
      obtain ⟨z, w, hzw⟩ := hconstant
      rcases hpure with hmiddle | hnotMiddle
      · have hvariables :
            (fun u : B ↦ projectionOccurrenceVariable labels u.1) =
              (fun u d ↦ signValue d.2 (c u)) := by
          funext u d
          exact projectionOccurrenceVariable_of_middle labels u.1 d (hmiddle u)
        rw [hvariables]
        calc
          jointCumulantOn (fun u (d : SignLayer (WalshIndex m) ×
              SignLayer (WalshIndex m)) ↦ signValue d.2 (c u)) =
              jointCumulantOn
                (fun u (d : SignLayer (WalshIndex m)) ↦ signValue d (c u)) :=
            jointCumulantOn_lift_snd
              (Ω₁ := SignLayer (WalshIndex m))
              (Ω₂ := SignLayer (WalshIndex m))
              (fun u (d : SignLayer (WalshIndex m)) ↦ signValue d (c u))
          _ = 0 := jointCumulantOn_signValue_nonconstant c w z hzw
      · have hvariables :
            (fun u : B ↦ projectionOccurrenceVariable labels u.1) =
              (fun u d ↦ signValue d.1 (c u)) := by
          funext u d
          exact projectionOccurrenceVariable_of_not_middle labels u.1 d
            (hnotMiddle u)
        rw [hvariables]
        calc
          jointCumulantOn (fun u (d : SignLayer (WalshIndex m) ×
              SignLayer (WalshIndex m)) ↦ signValue d.1 (c u)) =
              jointCumulantOn
                (fun u (d : SignLayer (WalshIndex m)) ↦ signValue d (c u)) :=
            jointCumulantOn_lift_fst
              (Ω₁ := SignLayer (WalshIndex m))
              (Ω₂ := SignLayer (WalshIndex m))
              (fun u (d : SignLayer (WalshIndex m)) ↦ signValue d (c u))
          _ = 0 := jointCumulantOn_signValue_nonconstant c w z hzw
  · rw [if_neg (fun h ↦ hpure h.1)]
    simp only [OccurrenceBlockLayerPure] at hpure
    have hnotAllMiddle : ¬(∀ z : B, projectionOccurrenceIsMiddle z.1) :=
      fun h ↦ hpure (Or.inl h)
    have hnotAllInput : ¬(∀ z : B, ¬projectionOccurrenceIsMiddle z.1) :=
      fun h ↦ hpure (Or.inr h)
    push Not at hnotAllMiddle hnotAllInput
    obtain ⟨zInput, hzInput⟩ := hnotAllMiddle
    obtain ⟨zMiddle, hzMiddle⟩ := hnotAllInput
    let A : Finset B := Finset.univ.filter
      (fun z ↦ projectionOccurrenceIsMiddle z.1)
    let C : Finset B := Finset.univ.filter
      (fun z ↦ ¬projectionOccurrenceIsMiddle z.1)
    have hcover : A ∪ C = Finset.univ := by
      ext z
      by_cases hz : projectionOccurrenceIsMiddle z.1 <;> simp [A, C, hz]
    have hdisjoint : Disjoint A C := by
      exact Finset.disjoint_left.mpr (by
        intro z hzA hzC
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hzA
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hzC
        exact hzC hzA)
    have hA : A.Nonempty := ⟨zMiddle, by simp [A, hzMiddle]⟩
    have hC : C.Nonempty := ⟨zInput, by simp [C, hzInput]⟩
    apply independent_families_mixed_cumulant_vanish_on
      (fun z : B ↦ projectionOccurrenceVariable labels z.1)
      A C hcover hdisjoint
    · intro z hz a b d₂
      have hzMiddle' : projectionOccurrenceIsMiddle z.1 := by simpa [A] using hz
      rw [projectionOccurrenceVariable_of_middle labels z.1 (a, d₂) hzMiddle',
        projectionOccurrenceVariable_of_middle labels z.1 (b, d₂) hzMiddle']
    · intro z hz a b d₁
      have hzInput' : ¬projectionOccurrenceIsMiddle z.1 := by simpa [C] using hz
      rw [projectionOccurrenceVariable_of_not_middle labels z.1 (d₁, a) hzInput',
        projectionOccurrenceVariable_of_not_middle labels z.1 (d₁, b) hzInput']
    · exact hA
    · exact hC

private noncomputable def fixedLabelConnectedPartitionTerm
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4))) : ℝ := by
  classical
  exact if ProductPartitionConnected σ (entryFactorPartition q) then
    ∏ B ∈ σ.parts, occurrenceBlockCumulantValue labels B
  else 0

/-- The connected product-cumulant sum with every block evaluated exactly.
Mixed-layer blocks and nonconstant coordinate blocks are represented by zero;
pure constant-coordinate blocks carry their literal Rademacher cumulant. -/
theorem joint_entry_sign_evaluated_partition_expansion
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m) :
    jointCumulant
        (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ projectionEntrySignMonomial (labels f) d) =
      ∑ σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4)),
        fixedLabelConnectedPartitionTerm labels σ := by
  classical
  rw [joint_entry_sign_connected_partition_expansion]
  unfold connectedPartitionCumulantSum
  apply Finset.sum_congr rfl
  intro σ _
  rw [fixedLabelConnectedPartitionTerm]
  by_cases hconnected : ProductPartitionConnected σ (entryFactorPartition q)
  · rw [if_pos hconnected, if_pos hconnected]
    unfold partitionCumulantProduct
    apply Finset.prod_congr rfl
    intro B hB
    exact projectionOccurrence_block_cumulant labels B
      (σ.nonempty_of_mem_parts hB)
  · rw [if_neg hconnected, if_neg hconnected]

/-! ## Exact occurrence expansion and its quantitative consequence -/

/-! The four sign occurrences of one entry are reindexed as the two middle
occurrences followed by the two input occurrences.  Keeping this equivalence
explicit makes the passage between a partition of all `4q` occurrences and a
pair of partitions of `2q` occurrences checkable in the kernel. -/

private noncomputable def pairOccurrenceEquiv (q : ℕ) :
    Fin q × Fin 2 ≃ Fin (2 * q) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm q 2))

@[simp] private theorem pairOccurrenceEquiv_zero {q : ℕ} (f : Fin q) :
    pairOccurrenceEquiv q (f, 0) = leftOccurrence f := by
  apply Fin.ext
  simp [pairOccurrenceEquiv, finProdFinEquiv, leftOccurrence]

@[simp] private theorem pairOccurrenceEquiv_one {q : ℕ} (f : Fin q) :
    pairOccurrenceEquiv q (f, 1) = rightOccurrence f := by
  apply Fin.ext
  simp [pairOccurrenceEquiv, finProdFinEquiv, rightOccurrence]
  omega

private def positionToOccurrence {q : ℕ}
    (z : Fin q × Fin 4) : ProductOccurrence q :=
  if z.2 = 0 then Sum.inl (leftOccurrence z.1)
  else if z.2 = 1 then Sum.inl (rightOccurrence z.1)
  else if z.2 = 2 then Sum.inr (leftOccurrence z.1)
  else Sum.inr (rightOccurrence z.1)

private theorem positionToOccurrence_injective {q : ℕ} :
    Function.Injective (@positionToOccurrence q) := by
  rintro ⟨f, k⟩ ⟨g, l⟩ h
  fin_cases k <;> fin_cases l <;>
    simp [positionToOccurrence, leftOccurrence, rightOccurrence, Fin.ext_iff]
      at h ⊢ <;> omega

private theorem positionToOccurrence_surjective {q : ℕ} :
    Function.Surjective (@positionToOccurrence q) := by
  intro x
  rcases x with a | a
  · obtain ⟨z, rfl⟩ := (pairOccurrenceEquiv q).surjective a
    rcases z with ⟨f, k⟩
    fin_cases k
    · exact ⟨(f, 0), by simp [positionToOccurrence]⟩
    · exact ⟨(f, 1), by simp [positionToOccurrence]⟩
  · obtain ⟨z, rfl⟩ := (pairOccurrenceEquiv q).surjective a
    rcases z with ⟨f, k⟩
    fin_cases k
    · exact ⟨(f, 2), by simp [positionToOccurrence]⟩
    · exact ⟨(f, 3), by simp [positionToOccurrence]⟩

private noncomputable def occurrencePositionEquiv (q : ℕ) :
    Fin q × Fin 4 ≃ ProductOccurrence q :=
  Equiv.ofBijective positionToOccurrence
    ⟨positionToOccurrence_injective, positionToOccurrence_surjective⟩

@[simp] private theorem occurrencePositionEquiv_zero {q : ℕ} (f : Fin q) :
    occurrencePositionEquiv q (f, 0) = Sum.inl (leftOccurrence f) := by
  change positionToOccurrence (f, 0) = _
  simp [positionToOccurrence]

@[simp] private theorem occurrencePositionEquiv_one {q : ℕ} (f : Fin q) :
    occurrencePositionEquiv q (f, 1) = Sum.inl (rightOccurrence f) := by
  change positionToOccurrence (f, 1) = _
  simp [positionToOccurrence]

@[simp] private theorem occurrencePositionEquiv_two {q : ℕ} (f : Fin q) :
    occurrencePositionEquiv q (f, 2) = Sum.inr (leftOccurrence f) := by
  change positionToOccurrence (f, 2) = _
  simp [positionToOccurrence]

@[simp] private theorem occurrencePositionEquiv_three {q : ℕ} (f : Fin q) :
    occurrencePositionEquiv q (f, 3) = Sum.inr (rightOccurrence f) := by
  change positionToOccurrence (f, 3) = _
  simp [positionToOccurrence]

@[simp] private theorem occurrencePositionEquiv_symm_inl_left
    {q : ℕ} (f : Fin q) :
    (occurrencePositionEquiv q).symm (Sum.inl (leftOccurrence f)) = (f, 0) := by
  apply (occurrencePositionEquiv q).injective
  simp

@[simp] private theorem occurrencePositionEquiv_symm_inl_right
    {q : ℕ} (f : Fin q) :
    (occurrencePositionEquiv q).symm (Sum.inl (rightOccurrence f)) = (f, 1) := by
  apply (occurrencePositionEquiv q).injective
  simp

@[simp] private theorem occurrencePositionEquiv_symm_inr_left
    {q : ℕ} (f : Fin q) :
    (occurrencePositionEquiv q).symm (Sum.inr (leftOccurrence f)) = (f, 2) := by
  apply (occurrencePositionEquiv q).injective
  simp

@[simp] private theorem occurrencePositionEquiv_symm_inr_right
    {q : ℕ} (f : Fin q) :
    (occurrencePositionEquiv q).symm (Sum.inr (rightOccurrence f)) = (f, 3) := by
  apply (occurrencePositionEquiv q).injective
  simp

private noncomputable def middlePositionEmbedding (q : ℕ) :
    Fin (2 * q) ↪ Fin q × Fin 4 where
  toFun a := (occurrencePositionEquiv q).symm (Sum.inl a)
  inj' _ _ h := Sum.inl.inj ((occurrencePositionEquiv q).symm.injective h)

private noncomputable def inputPositionEmbedding (q : ℕ) :
    Fin (2 * q) ↪ Fin q × Fin 4 where
  toFun a := (occurrencePositionEquiv q).symm (Sum.inr a)
  inj' _ _ h := Sum.inr.inj ((occurrencePositionEquiv q).symm.injective h)

@[simp] private theorem occurrencePositionEquiv_middleEmbedding
    {q : ℕ} (a : Fin (2 * q)) :
    occurrencePositionEquiv q (middlePositionEmbedding q a) = Sum.inl a := by
  exact (occurrencePositionEquiv q).apply_symm_apply _

@[simp] private theorem occurrencePositionEquiv_inputEmbedding
    {q : ℕ} (a : Fin (2 * q)) :
    occurrencePositionEquiv q (inputPositionEmbedding q a) = Sum.inr a := by
  exact (occurrencePositionEquiv q).apply_symm_apply _

@[simp] private theorem middlePositionEmbedding_left {q : ℕ} (f : Fin q) :
    middlePositionEmbedding q (leftOccurrence f) = (f, 0) := by
  apply (occurrencePositionEquiv q).injective
  simp

@[simp] private theorem middlePositionEmbedding_right {q : ℕ} (f : Fin q) :
    middlePositionEmbedding q (rightOccurrence f) = (f, 1) := by
  apply (occurrencePositionEquiv q).injective
  simp

@[simp] private theorem inputPositionEmbedding_left {q : ℕ} (f : Fin q) :
    inputPositionEmbedding q (leftOccurrence f) = (f, 2) := by
  apply (occurrencePositionEquiv q).injective
  simp

@[simp] private theorem inputPositionEmbedding_right {q : ℕ} (f : Fin q) :
    inputPositionEmbedding q (rightOccurrence f) = (f, 3) := by
  apply (occurrencePositionEquiv q).injective
  simp

private noncomputable def middleBlockEmbedding (q : ℕ) :
    Finset (Fin (2 * q)) ↪ Finset (Fin q × Fin 4) where
  toFun B := B.map (middlePositionEmbedding q)
  inj' _ _ h := Finset.map_injective (middlePositionEmbedding q) h

private noncomputable def inputBlockEmbedding (q : ℕ) :
    Finset (Fin (2 * q)) ↪ Finset (Fin q × Fin 4) where
  toFun B := B.map (inputPositionEmbedding q)
  inj' _ _ h := Finset.map_injective (inputPositionEmbedding q) h

private noncomputable def occurrencePartitionParts {q : ℕ}
    (D : OccurrencePartitionData q) : Finset (Finset (Fin q × Fin 4)) :=
  D.middle.parts.map (middleBlockEmbedding q) ∪
    D.input.parts.map (inputBlockEmbedding q)

private noncomputable def occurrencePartitionOfData {q : ℕ}
    (D : OccurrencePartitionData q) :
    Finpartition (Finset.univ : Finset (Fin q × Fin 4)) := by
  classical
  apply Finpartition.ofExistsUnique (occurrencePartitionParts D)
  · intro B _ z _
    exact Finset.mem_univ z
  · intro z _
    rcases hz : occurrencePositionEquiv q z with a | a
    · obtain ⟨B, hB, haB⟩ := D.middle.exists_mem (Finset.mem_univ a)
      refine ⟨B.map (middlePositionEmbedding q), ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨B, hB, rfl⟩)
      · rw [Finset.mem_map]
        refine ⟨a, haB, ?_⟩
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_middleEmbedding, hz]
      · intro C hC
        rcases hC with ⟨hC, hzC⟩
        rw [occurrencePartitionParts, Finset.mem_union] at hC
        rcases hC with hC | hC
        · rw [Finset.mem_map] at hC
          obtain ⟨C0, hC0, rfl⟩ := hC
          change z ∈ Finset.map (middlePositionEmbedding q) C0 at hzC
          rw [Finset.mem_map] at hzC
          obtain ⟨b, hbC0, hbz⟩ := hzC
          have hab : a = b := by
            apply Sum.inl.inj
            rw [← hz, ← occurrencePositionEquiv_middleEmbedding b]
            exact congrArg (occurrencePositionEquiv q) hbz.symm
          subst b
          have hBC : B = C0 :=
            D.middle.eq_of_mem_parts hB hC0 haB hbC0
          change Finset.map (middlePositionEmbedding q) C0 =
            Finset.map (middlePositionEmbedding q) B
          rw [hBC]
        · rw [Finset.mem_map] at hC
          obtain ⟨C0, hC0, rfl⟩ := hC
          change z ∈ Finset.map (inputPositionEmbedding q) C0 at hzC
          rw [Finset.mem_map] at hzC
          obtain ⟨b, hbC0, hbz⟩ := hzC
          have : Sum.inl a = Sum.inr b := by
            rw [← hz, ← occurrencePositionEquiv_inputEmbedding b]
            exact congrArg (occurrencePositionEquiv q) hbz.symm
          cases this
    · obtain ⟨B, hB, haB⟩ := D.input.exists_mem (Finset.mem_univ a)
      refine ⟨B.map (inputPositionEmbedding q), ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨B, hB, rfl⟩)
      · rw [Finset.mem_map]
        refine ⟨a, haB, ?_⟩
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_inputEmbedding, hz]
      · intro C hC
        rcases hC with ⟨hC, hzC⟩
        rw [occurrencePartitionParts, Finset.mem_union] at hC
        rcases hC with hC | hC
        · rw [Finset.mem_map] at hC
          obtain ⟨C0, hC0, rfl⟩ := hC
          change z ∈ Finset.map (middlePositionEmbedding q) C0 at hzC
          rw [Finset.mem_map] at hzC
          obtain ⟨b, hbC0, hbz⟩ := hzC
          have : Sum.inr a = Sum.inl b := by
            rw [← hz, ← occurrencePositionEquiv_middleEmbedding b]
            exact congrArg (occurrencePositionEquiv q) hbz.symm
          cases this
        · rw [Finset.mem_map] at hC
          obtain ⟨C0, hC0, rfl⟩ := hC
          change z ∈ Finset.map (inputPositionEmbedding q) C0 at hzC
          rw [Finset.mem_map] at hzC
          obtain ⟨b, hbC0, hbz⟩ := hzC
          have hab : a = b := by
            apply Sum.inr.inj
            rw [← hz, ← occurrencePositionEquiv_inputEmbedding b]
            exact congrArg (occurrencePositionEquiv q) hbz.symm
          subst b
          have hBC : B = C0 := D.input.eq_of_mem_parts hB hC0 haB hbC0
          change Finset.map (inputPositionEmbedding q) C0 =
            Finset.map (inputPositionEmbedding q) B
          rw [hBC]
  · rw [occurrencePartitionParts, Finset.mem_union]
    push Not
    constructor
    · intro h
      rw [Finset.mem_map] at h
      obtain ⟨B, hB, hB0⟩ := h
      have hne := D.middle.ne_empty hB
      exact hne (Finset.map_eq_empty.mp hB0)
    · intro h
      rw [Finset.mem_map] at h
      obtain ⟨B, hB, hB0⟩ := h
      have hne := D.input.ne_empty hB
      exact hne (Finset.map_eq_empty.mp hB0)

@[simp] private theorem occurrencePartitionOfData_parts {q : ℕ}
    (D : OccurrencePartitionData q) :
    (occurrencePartitionOfData D).parts = occurrencePartitionParts D := rfl

private theorem projectionOccurrenceIsMiddle_iff_exists {q : ℕ}
    (z : Fin q × Fin 4) :
    projectionOccurrenceIsMiddle z ↔
      ∃ a : Fin (2 * q), occurrencePositionEquiv q z = Sum.inl a := by
  rcases z with ⟨f, k⟩
  fin_cases k <;> simp [projectionOccurrenceIsMiddle]

private theorem projectionOccurrenceIsInput_iff_exists {q : ℕ}
    (z : Fin q × Fin 4) :
    ¬projectionOccurrenceIsMiddle z ↔
      ∃ a : Fin (2 * q), occurrencePositionEquiv q z = Sum.inr a := by
  rcases z with ⟨f, k⟩
  fin_cases k <;> simp [projectionOccurrenceIsMiddle]

private def OccurrencePartitionLayerPure {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4))) : Prop :=
  ∀ B ∈ σ.parts, OccurrenceBlockLayerPure B

private theorem occurrencePartitionOfData_layerPure {q : ℕ}
    (D : OccurrencePartitionData q) :
    OccurrencePartitionLayerPure (occurrencePartitionOfData D) := by
  classical
  intro B hB
  rw [occurrencePartitionOfData_parts, occurrencePartitionParts,
    Finset.mem_union] at hB
  rcases hB with hB | hB
  · rw [Finset.mem_map] at hB
    obtain ⟨B0, hB0, rfl⟩ := hB
    left
    intro z
    obtain ⟨a, ha, haz⟩ := Finset.mem_map.mp z.2
    rw [projectionOccurrenceIsMiddle_iff_exists]
    refine ⟨a, ?_⟩
    rw [← haz]
    exact occurrencePositionEquiv_middleEmbedding a
  · rw [Finset.mem_map] at hB
    obtain ⟨B0, hB0, rfl⟩ := hB
    right
    intro z
    obtain ⟨a, ha, haz⟩ := Finset.mem_map.mp z.2
    rw [projectionOccurrenceIsInput_iff_exists]
    refine ⟨a, ?_⟩
    rw [← haz]
    exact occurrencePositionEquiv_inputEmbedding a

private theorem occurrencePartitionOfData_part_middle {q : ℕ}
    (D : OccurrencePartitionData q) (a : Fin (2 * q)) :
    (occurrencePartitionOfData D).part (middlePositionEmbedding q a) =
      (D.middle.part a).map (middlePositionEmbedding q) := by
  classical
  apply (occurrencePartitionOfData D).part_eq_of_mem
  · rw [occurrencePartitionOfData_parts, occurrencePartitionParts]
    exact Finset.mem_union_left _ (Finset.mem_map.mpr
      ⟨D.middle.part a, D.middle.part_mem.mpr (Finset.mem_univ a), rfl⟩)
  · exact Finset.mem_map.mpr
      ⟨a, D.middle.mem_part (Finset.mem_univ a), rfl⟩

private theorem occurrencePartitionOfData_part_input {q : ℕ}
    (D : OccurrencePartitionData q) (a : Fin (2 * q)) :
    (occurrencePartitionOfData D).part (inputPositionEmbedding q a) =
      (D.input.part a).map (inputPositionEmbedding q) := by
  classical
  apply (occurrencePartitionOfData D).part_eq_of_mem
  · rw [occurrencePartitionOfData_parts, occurrencePartitionParts]
    exact Finset.mem_union_right _ (Finset.mem_map.mpr
      ⟨D.input.part a, D.input.part_mem.mpr (Finset.mem_univ a), rfl⟩)
  · exact Finset.mem_map.mpr
      ⟨a, D.input.mem_part (Finset.mem_univ a), rfl⟩

private theorem occurrencePartitionOfData_middle_part_eq_iff {q : ℕ}
    (D : OccurrencePartitionData q) (a b : Fin (2 * q)) :
    (occurrencePartitionOfData D).part (middlePositionEmbedding q a) =
        (occurrencePartitionOfData D).part (middlePositionEmbedding q b) ↔
      D.middle.part a = D.middle.part b := by
  rw [occurrencePartitionOfData_part_middle,
    occurrencePartitionOfData_part_middle, Finset.map_inj]

private theorem occurrencePartitionOfData_input_part_eq_iff {q : ℕ}
    (D : OccurrencePartitionData q) (a b : Fin (2 * q)) :
    (occurrencePartitionOfData D).part (inputPositionEmbedding q a) =
        (occurrencePartitionOfData D).part (inputPositionEmbedding q b) ↔
      D.input.part a = D.input.part b := by
  rw [occurrencePartitionOfData_part_input,
    occurrencePartitionOfData_part_input, Finset.map_inj]

private theorem occurrencePartitionOfData_middle_ne_input {q : ℕ}
    (D : OccurrencePartitionData q) (a b : Fin (2 * q)) :
    (occurrencePartitionOfData D).part (middlePositionEmbedding q a) ≠
      (occurrencePartitionOfData D).part (inputPositionEmbedding q b) := by
  classical
  intro h
  have ha : middlePositionEmbedding q a ∈
      (occurrencePartitionOfData D).part (middlePositionEmbedding q a) :=
    (occurrencePartitionOfData D).mem_part (Finset.mem_univ _)
  rw [h, occurrencePartitionOfData_part_input] at ha
  obtain ⟨c, hc, hca⟩ := Finset.mem_map.mp ha
  have hfalse : Sum.inr c = Sum.inl a := by
    rw [← occurrencePositionEquiv_inputEmbedding c,
      ← occurrencePositionEquiv_middleEmbedding a]
    exact congrArg (occurrencePositionEquiv q) hca
  cases hfalse

private theorem entryFactorPartition_part_eq_iff {q : ℕ}
    (z w : Fin q × Fin 4) :
    (entryFactorPartition q).part z = (entryFactorPartition q).part w ↔
      z.1 = w.1 := by
  classical
  rw [eq_comm]
  rw [← Finpartition.mem_part_iff_part_eq_part (entryFactorPartition q)
    (Finset.mem_univ w) (Finset.mem_univ z)]
  rw [entryFactorPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

private theorem productJoinRelated_symm {q : ℕ} (D : OccurrencePartitionData q)
    {x y : ProductOccurrence q} :
    productJoinRelated D x y → productJoinRelated D y x := by
  rcases x with a | a <;> rcases y with b | b
  · exact fun h ↦ h.symm
  · rintro ⟨f, h | h⟩
    · exact ⟨f, Or.inl h⟩
    · exact ⟨f, Or.inr h⟩
  · rintro ⟨f, h | h⟩
    · exact ⟨f, Or.inl h⟩
    · exact ⟨f, Or.inr h⟩
  · rintro (h | ⟨f, h | h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨f, Or.inr h⟩
    · exact Or.inr ⟨f, Or.inl h⟩

private theorem sameEntryFactor_productJoin_path {q : ℕ}
    (D : OccurrencePartitionData q) (f : Fin q) (k l : Fin 4) :
    Relation.ReflTransGen (productJoinRelated D)
      (occurrencePositionEquiv q (f, k))
      (occurrencePositionEquiv q (f, l)) := by
  have h02 : productJoinRelated D
      (occurrencePositionEquiv q (f, 0))
      (occurrencePositionEquiv q (f, 2)) := by
    simp only [occurrencePositionEquiv_zero, occurrencePositionEquiv_two]
    exact ⟨f, Or.inl ⟨rfl, rfl⟩⟩
  have h23 : productJoinRelated D
      (occurrencePositionEquiv q (f, 2))
      (occurrencePositionEquiv q (f, 3)) := by
    simp only [occurrencePositionEquiv_two, occurrencePositionEquiv_three]
    exact Or.inr ⟨f, Or.inl ⟨rfl, rfl⟩⟩
  have h31 : productJoinRelated D
      (occurrencePositionEquiv q (f, 3))
      (occurrencePositionEquiv q (f, 1)) := by
    simp only [occurrencePositionEquiv_three, occurrencePositionEquiv_one]
    exact ⟨f, Or.inr ⟨rfl, rfl⟩⟩
  have h20 := productJoinRelated_symm D h02
  have h32 := productJoinRelated_symm D h23
  have h13 := productJoinRelated_symm D h31
  fin_cases k <;> fin_cases l
  · exact Relation.ReflTransGen.refl
  · exact (Relation.ReflTransGen.single h02).trans
      ((Relation.ReflTransGen.single h23).trans
        (Relation.ReflTransGen.single h31))
  · exact Relation.ReflTransGen.single h02
  · exact (Relation.ReflTransGen.single h02).trans
      (Relation.ReflTransGen.single h23)
  · exact (Relation.ReflTransGen.single h13).trans
      ((Relation.ReflTransGen.single h32).trans
        (Relation.ReflTransGen.single h20))
  · exact Relation.ReflTransGen.refl
  · exact (Relation.ReflTransGen.single h13).trans
      (Relation.ReflTransGen.single h32)
  · exact Relation.ReflTransGen.single h13
  · exact Relation.ReflTransGen.single h20
  · exact (Relation.ReflTransGen.single h23).trans
      (Relation.ReflTransGen.single h31)
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h23
  · exact (Relation.ReflTransGen.single h32).trans
      (Relation.ReflTransGen.single h20)
  · exact Relation.ReflTransGen.single h31
  · exact Relation.ReflTransGen.single h32
  · exact Relation.ReflTransGen.refl

private theorem combinedRelation_to_productJoin_path {q : ℕ}
    (D : OccurrencePartitionData q) (z w : Fin q × Fin 4)
    (hrel :
      (occurrencePartitionOfData D).part z =
          (occurrencePartitionOfData D).part w ∨
        (entryFactorPartition q).part z = (entryFactorPartition q).part w) :
    Relation.ReflTransGen (productJoinRelated D)
      (occurrencePositionEquiv q z) (occurrencePositionEquiv q w) := by
  rcases hrel with hpartition | hfactor
  · rcases hz : occurrencePositionEquiv q z with a | a <;>
      rcases hw : occurrencePositionEquiv q w with b | b
    · have hza : middlePositionEmbedding q a = z := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_middleEmbedding, hz]
      have hwb : middlePositionEmbedding q b = w := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_middleEmbedding, hw]
      rw [← hza, ← hwb] at hpartition
      exact Relation.ReflTransGen.single
        ((occurrencePartitionOfData_middle_part_eq_iff D a b).mp hpartition)
    · have hza : middlePositionEmbedding q a = z := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_middleEmbedding, hz]
      have hwb : inputPositionEmbedding q b = w := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_inputEmbedding, hw]
      rw [← hza, ← hwb] at hpartition
      exact False.elim
        (occurrencePartitionOfData_middle_ne_input D a b hpartition)
    · have hza : inputPositionEmbedding q a = z := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_inputEmbedding, hz]
      have hwb : middlePositionEmbedding q b = w := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_middleEmbedding, hw]
      rw [← hza, ← hwb] at hpartition
      exact False.elim
        (occurrencePartitionOfData_middle_ne_input D b a hpartition.symm)
    · have hza : inputPositionEmbedding q a = z := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_inputEmbedding, hz]
      have hwb : inputPositionEmbedding q b = w := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_inputEmbedding, hw]
      rw [← hza, ← hwb] at hpartition
      exact Relation.ReflTransGen.single (Or.inl
        ((occurrencePartitionOfData_input_part_eq_iff D a b).mp hpartition))
  · rcases z with ⟨f, k⟩
    rcases w with ⟨g, l⟩
    have hfg : f = g :=
      (entryFactorPartition_part_eq_iff (f, k) (g, l)).mp hfactor
    subst g
    exact sameEntryFactor_productJoin_path D f k l

private theorem productJoin_to_combinedRelation_path {q : ℕ}
    (D : OccurrencePartitionData q) (x y : ProductOccurrence q)
    (hrel : productJoinRelated D x y) :
    Relation.ReflTransGen
      (fun z w : Fin q × Fin 4 ↦
        (occurrencePartitionOfData D).part z =
            (occurrencePartitionOfData D).part w ∨
          (entryFactorPartition q).part z = (entryFactorPartition q).part w)
      ((occurrencePositionEquiv q).symm x)
      ((occurrencePositionEquiv q).symm y) := by
  rcases x with a | a <;> rcases y with b | b
  · have ha : (occurrencePositionEquiv q).symm (Sum.inl a) =
        middlePositionEmbedding q a := rfl
    have hb : (occurrencePositionEquiv q).symm (Sum.inl b) =
        middlePositionEmbedding q b := rfl
    rw [ha, hb]
    exact Relation.ReflTransGen.single (Or.inl
      ((occurrencePartitionOfData_middle_part_eq_iff D a b).mpr hrel))
  · rcases hrel with ⟨f, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      simp only [occurrencePositionEquiv_symm_inl_left,
        occurrencePositionEquiv_symm_inr_left]
      exact Relation.ReflTransGen.single (Or.inr
        ((entryFactorPartition_part_eq_iff (f, 0) (f, 2)).mpr rfl))
    · rcases h with ⟨rfl, rfl⟩
      simp only [occurrencePositionEquiv_symm_inl_right,
        occurrencePositionEquiv_symm_inr_right]
      exact Relation.ReflTransGen.single (Or.inr
        ((entryFactorPartition_part_eq_iff (f, 1) (f, 3)).mpr rfl))
  · rcases hrel with ⟨f, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      simp only [occurrencePositionEquiv_symm_inr_left,
        occurrencePositionEquiv_symm_inl_left]
      exact Relation.ReflTransGen.single (Or.inr
        ((entryFactorPartition_part_eq_iff (f, 2) (f, 0)).mpr rfl))
    · rcases h with ⟨rfl, rfl⟩
      simp only [occurrencePositionEquiv_symm_inr_right,
        occurrencePositionEquiv_symm_inl_right]
      exact Relation.ReflTransGen.single (Or.inr
        ((entryFactorPartition_part_eq_iff (f, 3) (f, 1)).mpr rfl))
  · rcases hrel with hinput | ⟨f, h | h⟩
    · have ha : (occurrencePositionEquiv q).symm (Sum.inr a) =
          inputPositionEmbedding q a := rfl
      have hb : (occurrencePositionEquiv q).symm (Sum.inr b) =
          inputPositionEmbedding q b := rfl
      rw [ha, hb]
      exact Relation.ReflTransGen.single (Or.inl
        ((occurrencePartitionOfData_input_part_eq_iff D a b).mpr hinput))
    · rcases h with ⟨rfl, rfl⟩
      simp only [occurrencePositionEquiv_symm_inr_left,
        occurrencePositionEquiv_symm_inr_right]
      exact Relation.ReflTransGen.single (Or.inr
        ((entryFactorPartition_part_eq_iff (f, 2) (f, 3)).mpr rfl))
    · rcases h with ⟨rfl, rfl⟩
      simp only [occurrencePositionEquiv_symm_inr_right,
        occurrencePositionEquiv_symm_inr_left]
      exact Relation.ReflTransGen.single (Or.inr
        ((entryFactorPartition_part_eq_iff (f, 3) (f, 2)).mpr rfl))

private theorem occurrenceProductConnected_iff_partitionConnected {q : ℕ}
    (D : OccurrencePartitionData q) :
    ProductOccurrenceConnected D ↔
      ProductPartitionConnected (occurrencePartitionOfData D)
        (entryFactorPartition q) := by
  constructor
  · intro hconnected z w
    have hpath := hconnected
      (occurrencePositionEquiv q z) (occurrencePositionEquiv q w)
    have hlift := hpath.lift' (occurrencePositionEquiv q).symm
      (productJoin_to_combinedRelation_path D)
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hlift
  · intro hconnected x y
    have hpath := hconnected
      ((occurrencePositionEquiv q).symm x)
      ((occurrencePositionEquiv q).symm y)
    have hlift := hpath.lift' (occurrencePositionEquiv q)
      (combinedRelation_to_productJoin_path D)
    simpa only [Function.onFun, Equiv.apply_symm_apply] using hlift

private def partitionPartSetoid {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finpartition (Finset.univ : Finset α)) : Setoid α where
  r a b := P.part a = P.part b
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

private noncomputable def occurrenceMiddleRestriction {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4))) :
    Finpartition (Finset.univ : Finset (Fin (2 * q))) := by
  classical
  exact Finpartition.ofSetoid
    (Setoid.comap (middlePositionEmbedding q) (partitionPartSetoid σ))

private noncomputable def occurrenceInputRestriction {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4))) :
    Finpartition (Finset.univ : Finset (Fin (2 * q))) := by
  classical
  exact Finpartition.ofSetoid
    (Setoid.comap (inputPositionEmbedding q) (partitionPartSetoid σ))

private noncomputable def occurrenceDataOfPartition {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4))) :
    OccurrencePartitionData q :=
  ⟨occurrenceMiddleRestriction σ, occurrenceInputRestriction σ⟩

private theorem mem_occurrenceMiddleRestriction_part_iff {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4)))
    (a b : Fin (2 * q)) :
    b ∈ (occurrenceMiddleRestriction σ).part a ↔
      σ.part (middlePositionEmbedding q a) =
        σ.part (middlePositionEmbedding q b) := by
  classical
  rw [occurrenceMiddleRestriction, Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

private theorem mem_occurrenceInputRestriction_part_iff {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4)))
    (a b : Fin (2 * q)) :
    b ∈ (occurrenceInputRestriction σ).part a ↔
      σ.part (inputPositionEmbedding q a) =
        σ.part (inputPositionEmbedding q b) := by
  classical
  rw [occurrenceInputRestriction, Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

private theorem finpartition_eq_of_part_eq {α : Type*}
    [Fintype α] [DecidableEq α]
    (P Q : Finpartition (Finset.univ : Finset α))
    (h : ∀ a, P.part a = Q.part a) : P = Q := by
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB ha, h a]
    exact Q.part_mem.mpr (Finset.mem_univ a)
  · intro hB
    obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB ha, ← h a]
    exact P.part_mem.mpr (Finset.mem_univ a)

private theorem occurrenceDataOfPartition_ofData {q : ℕ}
    (D : OccurrencePartitionData q) :
    occurrenceDataOfPartition (occurrencePartitionOfData D) = D := by
  classical
  cases D with
  | mk middle input =>
      have hmiddle : occurrenceMiddleRestriction
          (occurrencePartitionOfData ⟨middle, input⟩) = middle := by
        apply finpartition_eq_of_part_eq
        intro a
        ext b
        rw [mem_occurrenceMiddleRestriction_part_iff,
          occurrencePartitionOfData_part_middle,
          occurrencePartitionOfData_part_middle]
        change Finset.map (middlePositionEmbedding q) (middle.part a) =
            Finset.map (middlePositionEmbedding q) (middle.part b) ↔
          b ∈ middle.part a
        rw [Finset.map_inj]
        rw [Finpartition.mem_part_iff_part_eq_part middle
          (Finset.mem_univ b) (Finset.mem_univ a)]
        exact eq_comm
      have hinput : occurrenceInputRestriction
          (occurrencePartitionOfData ⟨middle, input⟩) = input := by
        apply finpartition_eq_of_part_eq
        intro a
        ext b
        rw [mem_occurrenceInputRestriction_part_iff,
          occurrencePartitionOfData_part_input,
          occurrencePartitionOfData_part_input]
        change Finset.map (inputPositionEmbedding q) (input.part a) =
            Finset.map (inputPositionEmbedding q) (input.part b) ↔
          b ∈ input.part a
        rw [Finset.map_inj]
        rw [Finpartition.mem_part_iff_part_eq_part input
          (Finset.mem_univ b) (Finset.mem_univ a)]
        exact eq_comm
      exact congrArg₂ OccurrencePartitionData.mk hmiddle hinput

private theorem occurrencePartitionOfData_ofPartition {q : ℕ}
    (σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4)))
    (hpure : OccurrencePartitionLayerPure σ) :
    occurrencePartitionOfData (occurrenceDataOfPartition σ) = σ := by
  classical
  apply finpartition_eq_of_part_eq
  intro z
  rcases hz : occurrencePositionEquiv q z with a | a
  · have hza : middlePositionEmbedding q a = z := by
      apply (occurrencePositionEquiv q).injective
      rw [occurrencePositionEquiv_middleEmbedding, hz]
    rw [← hza, occurrencePartitionOfData_part_middle]
    ext w
    rw [Finset.mem_map]
    constructor
    · rintro ⟨b, hb, hbw⟩
      change b ∈ (occurrenceMiddleRestriction σ).part a at hb
      rw [mem_occurrenceMiddleRestriction_part_iff] at hb
      rw [← hbw]
      exact (Finpartition.mem_part_iff_part_eq_part σ
        (Finset.mem_univ _) (Finset.mem_univ _)).mpr hb.symm
    · intro hw
      have hpart : σ.part (middlePositionEmbedding q a) ∈ σ.parts :=
        σ.part_mem.mpr (Finset.mem_univ _)
      have hanchorMiddle :
          projectionOccurrenceIsMiddle (middlePositionEmbedding q a) := by
        rw [projectionOccurrenceIsMiddle_iff_exists]
        exact ⟨a, occurrencePositionEquiv_middleEmbedding a⟩
      have hallMiddle : ∀ x : σ.part (middlePositionEmbedding q a),
          projectionOccurrenceIsMiddle x.1 := by
        rcases hpure _ hpart with hmiddle | hinput
        · exact hmiddle
        · exact False.elim (hinput
            ⟨middlePositionEmbedding q a, σ.mem_part (Finset.mem_univ _)⟩
            hanchorMiddle)
      have hwMiddle := hallMiddle ⟨w, hw⟩
      obtain ⟨b, hwb⟩ :=
        (projectionOccurrenceIsMiddle_iff_exists w).mp hwMiddle
      have hbw : middlePositionEmbedding q b = w := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_middleEmbedding, hwb]
      refine ⟨b, ?_, hbw⟩
      change b ∈ (occurrenceMiddleRestriction σ).part a
      rw [mem_occurrenceMiddleRestriction_part_iff]
      have hparts := (Finpartition.mem_part_iff_part_eq_part σ
        (Finset.mem_univ w) (Finset.mem_univ (middlePositionEmbedding q a))).mp hw
      rw [← hbw] at hparts
      exact hparts.symm

  · have hza : inputPositionEmbedding q a = z := by
      apply (occurrencePositionEquiv q).injective
      rw [occurrencePositionEquiv_inputEmbedding, hz]
    rw [← hza, occurrencePartitionOfData_part_input]
    ext w
    rw [Finset.mem_map]
    constructor
    · rintro ⟨b, hb, hbw⟩
      change b ∈ (occurrenceInputRestriction σ).part a at hb
      rw [mem_occurrenceInputRestriction_part_iff] at hb
      rw [← hbw]
      exact (Finpartition.mem_part_iff_part_eq_part σ
        (Finset.mem_univ _) (Finset.mem_univ _)).mpr hb.symm
    · intro hw
      have hpart : σ.part (inputPositionEmbedding q a) ∈ σ.parts :=
        σ.part_mem.mpr (Finset.mem_univ _)
      have hanchorInput :
          ¬projectionOccurrenceIsMiddle (inputPositionEmbedding q a) := by
        rw [projectionOccurrenceIsInput_iff_exists]
        exact ⟨a, occurrencePositionEquiv_inputEmbedding a⟩
      have hallInput : ∀ x : σ.part (inputPositionEmbedding q a),
          ¬projectionOccurrenceIsMiddle x.1 := by
        rcases hpure _ hpart with hmiddle | hinput
        · exact False.elim (hanchorInput (hmiddle
            ⟨inputPositionEmbedding q a, σ.mem_part (Finset.mem_univ _)⟩))
        · exact hinput
      have hwInput := hallInput ⟨w, hw⟩
      obtain ⟨b, hwb⟩ :=
        (projectionOccurrenceIsInput_iff_exists w).mp hwInput
      have hbw : inputPositionEmbedding q b = w := by
        apply (occurrencePositionEquiv q).injective
        rw [occurrencePositionEquiv_inputEmbedding, hwb]
      refine ⟨b, ?_, hbw⟩
      change b ∈ (occurrenceInputRestriction σ).part a
      rw [mem_occurrenceInputRestriction_part_iff]
      have hparts := (Finpartition.mem_part_iff_part_eq_part σ
        (Finset.mem_univ w) (Finset.mem_univ (inputPositionEmbedding q a))).mp hw
      rw [← hbw] at hparts
      exact hparts.symm

private abbrev LayerPureOccurrencePartition (q : ℕ) :=
  {σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4)) //
    OccurrencePartitionLayerPure σ}

private noncomputable def occurrenceDataPartitionEquiv (q : ℕ) :
    OccurrencePartitionData q ≃ LayerPureOccurrencePartition q where
  toFun D := ⟨occurrencePartitionOfData D, occurrencePartitionOfData_layerPure D⟩
  invFun σ := occurrenceDataOfPartition σ.1
  left_inv := occurrenceDataOfPartition_ofData
  right_inv σ := Subtype.ext (occurrencePartitionOfData_ofPartition σ.1 σ.2)

private theorem fixedLabelConnectedPartitionTerm_eq_zero_of_not_layerPure
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m)
    (sigma : Finpartition (Finset.univ : Finset (Fin q × Fin 4)))
    (hpure : ¬OccurrencePartitionLayerPure sigma) :
    fixedLabelConnectedPartitionTerm labels sigma = 0 := by
  classical
  simp only [OccurrencePartitionLayerPure] at hpure
  push Not at hpure
  obtain ⟨B, hB, hnotPure⟩ := hpure
  rw [fixedLabelConnectedPartitionTerm]
  by_cases hconnected : ProductPartitionConnected sigma (entryFactorPartition q)
  · rw [if_pos hconnected]
    apply Finset.prod_eq_zero hB
    rw [occurrenceBlockCumulantValue]
    exact if_neg (fun h ↦ hnotPure h.1)
  · exact if_neg hconnected

private theorem fintype_sum_eq_subtype_sum_of_zero
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (p : alpha → Prop) [DecidablePred p] (F : alpha → M)
    (hzero : ∀ a, ¬p a → F a = 0) :
    (∑ a, F a) = ∑ a : {a // p a}, F a.1 := by
  have hcomplement : (∑ a : {a // ¬p a}, F a.1) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hzero a.1 a.2
  calc
    (∑ a, F a) =
        (∑ a : {a // p a}, F a.1) + ∑ a : {a // ¬p a}, F a.1 :=
      (Fintype.sum_subtype_add_sum_subtype p F).symm
    _ = ∑ a : {a // p a}, F a.1 := by rw [hcomplement, add_zero]

private def occurrencePartitionDataProdEquiv (q : ℕ) :
    OccurrencePartitionData q ≃
      Finpartition (Finset.univ : Finset (Fin (2 * q))) ×
        Finpartition (Finset.univ : Finset (Fin (2 * q))) where
  toFun D := (D.middle, D.input)
  invFun P := ⟨P.1, P.2⟩
  left_inv D := by cases D; rfl
  right_inv P := by cases P; rfl

private noncomputable instance occurrencePartitionDataFintype (q : ℕ) :
    Fintype (OccurrencePartitionData q) :=
  Fintype.ofEquiv
    (Finpartition (Finset.univ : Finset (Fin (2 * q))) ×
      Finpartition (Finset.univ : Finset (Fin (2 * q))))
    (occurrencePartitionDataProdEquiv q).symm

private def OccurrenceLabelsConstant {m q : ℕ}
    (D : OccurrencePartitionData q)
    (labels : Fin q → ProjectionEntryLabel m) : Prop :=
  (∀ a b, D.middle.part a = D.middle.part b →
    projectionOccurrenceCoordinate labels (middlePositionEmbedding q a) =
      projectionOccurrenceCoordinate labels (middlePositionEmbedding q b)) ∧
  (∀ a b, D.input.part a = D.input.part b →
    projectionOccurrenceCoordinate labels (inputPositionEmbedding q a) =
      projectionOccurrenceCoordinate labels (inputPositionEmbedding q b))

private def labelsOfOccurrenceAssignment {m q : ℕ}
    (D : OccurrencePartitionData q)
    (c : OccurrenceVertex D → WalshIndex m) :
    Fin q → ProjectionEntryLabel m :=
  fun f ↦
    ((c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))),
      c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f)))),
     (c (Sum.inr (equalityVertexAt D.input (leftOccurrence f))),
      c (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))))

private theorem labelsOfOccurrenceAssignment_middle_coordinate
    {m q : ℕ} (D : OccurrencePartitionData q)
    (c : OccurrenceVertex D → WalshIndex m) (a : Fin (2 * q)) :
    projectionOccurrenceCoordinate (labelsOfOccurrenceAssignment D c)
        (middlePositionEmbedding q a) =
      c (Sum.inl (equalityVertexAt D.middle a)) := by
  obtain ⟨z, rfl⟩ := (pairOccurrenceEquiv q).surjective a
  rcases z with ⟨f, k⟩
  fin_cases k <;>
    simp [labelsOfOccurrenceAssignment, projectionOccurrenceCoordinate]

private theorem labelsOfOccurrenceAssignment_input_coordinate
    {m q : ℕ} (D : OccurrencePartitionData q)
    (c : OccurrenceVertex D → WalshIndex m) (a : Fin (2 * q)) :
    projectionOccurrenceCoordinate (labelsOfOccurrenceAssignment D c)
        (inputPositionEmbedding q a) =
      c (Sum.inr (equalityVertexAt D.input a)) := by
  obtain ⟨z, rfl⟩ := (pairOccurrenceEquiv q).surjective a
  rcases z with ⟨f, k⟩
  fin_cases k <;>
    simp [labelsOfOccurrenceAssignment, projectionOccurrenceCoordinate]

private theorem labelsOfOccurrenceAssignment_constant
    {m q : ℕ} (D : OccurrencePartitionData q)
    (c : OccurrenceVertex D → WalshIndex m) :
    OccurrenceLabelsConstant D (labelsOfOccurrenceAssignment D c) := by
  constructor
  · intro a b hab
    rw [labelsOfOccurrenceAssignment_middle_coordinate,
      labelsOfOccurrenceAssignment_middle_coordinate]
    congr 2
    exact Subtype.ext hab
  · intro a b hab
    rw [labelsOfOccurrenceAssignment_input_coordinate,
      labelsOfOccurrenceAssignment_input_coordinate]
    congr 2
    exact Subtype.ext hab

private noncomputable def partitionBlockRepresentative
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (P : Finpartition (Finset.univ : Finset alpha))
    (B : {B // B ∈ P.parts}) : alpha :=
  Classical.choose (P.nonempty_of_mem_parts B.2)

private theorem partitionBlockRepresentative_mem
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (P : Finpartition (Finset.univ : Finset alpha))
    (B : {B // B ∈ P.parts}) :
    partitionBlockRepresentative P B ∈ B.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts B.2)

private noncomputable def occurrenceAssignmentOfConstantLabels
    {m q : ℕ} (D : OccurrencePartitionData q)
    (L : {labels : Fin q → ProjectionEntryLabel m //
      OccurrenceLabelsConstant D labels}) :
    OccurrenceVertex D → WalshIndex m
  | Sum.inl B => projectionOccurrenceCoordinate L.1
      (middlePositionEmbedding q
        (partitionBlockRepresentative D.middle B))
  | Sum.inr B => projectionOccurrenceCoordinate L.1
      (inputPositionEmbedding q
        (partitionBlockRepresentative D.input B))

private theorem occurrenceAssignmentOfConstantLabels_middle
    {m q : ℕ} (D : OccurrencePartitionData q)
    (L : {labels : Fin q → ProjectionEntryLabel m //
      OccurrenceLabelsConstant D labels}) (a : Fin (2 * q)) :
    occurrenceAssignmentOfConstantLabels D L
        (Sum.inl (equalityVertexAt D.middle a)) =
      projectionOccurrenceCoordinate L.1 (middlePositionEmbedding q a) := by
  apply L.2.1
  exact (Finpartition.mem_part_iff_part_eq_part D.middle
    (Finset.mem_univ (partitionBlockRepresentative D.middle
      (equalityVertexAt D.middle a))) (Finset.mem_univ a)).mp
        (partitionBlockRepresentative_mem D.middle
          (equalityVertexAt D.middle a))

private theorem occurrenceAssignmentOfConstantLabels_input
    {m q : ℕ} (D : OccurrencePartitionData q)
    (L : {labels : Fin q → ProjectionEntryLabel m //
      OccurrenceLabelsConstant D labels}) (a : Fin (2 * q)) :
    occurrenceAssignmentOfConstantLabels D L
        (Sum.inr (equalityVertexAt D.input a)) =
      projectionOccurrenceCoordinate L.1 (inputPositionEmbedding q a) := by
  apply L.2.2
  exact (Finpartition.mem_part_iff_part_eq_part D.input
    (Finset.mem_univ (partitionBlockRepresentative D.input
      (equalityVertexAt D.input a))) (Finset.mem_univ a)).mp
        (partitionBlockRepresentative_mem D.input
          (equalityVertexAt D.input a))

private noncomputable def occurrenceAssignmentLabelEquiv
    (m : ℕ) {q : ℕ} (D : OccurrencePartitionData q) :
    (OccurrenceVertex D → WalshIndex m) ≃
      {labels : Fin q → ProjectionEntryLabel m //
        OccurrenceLabelsConstant D labels} where
  toFun c := ⟨labelsOfOccurrenceAssignment D c,
    labelsOfOccurrenceAssignment_constant D c⟩
  invFun := occurrenceAssignmentOfConstantLabels D
  left_inv c := by
    funext x
    rcases x with B | B
    · rw [occurrenceAssignmentOfConstantLabels]
      rw [labelsOfOccurrenceAssignment_middle_coordinate]
      congr 2
      apply Subtype.ext
      exact D.middle.part_eq_of_mem B.2
        (partitionBlockRepresentative_mem D.middle B)
    · rw [occurrenceAssignmentOfConstantLabels]
      rw [labelsOfOccurrenceAssignment_input_coordinate]
      congr 2
      apply Subtype.ext
      exact D.input.part_eq_of_mem B.2
        (partitionBlockRepresentative_mem D.input B)
  right_inv L := by
    apply Subtype.ext
    funext f
    apply Prod.ext
    · apply Prod.ext
      · simpa [labelsOfOccurrenceAssignment, projectionOccurrenceCoordinate] using
          occurrenceAssignmentOfConstantLabels_middle D L (leftOccurrence f)
      · simpa [labelsOfOccurrenceAssignment, projectionOccurrenceCoordinate] using
          occurrenceAssignmentOfConstantLabels_middle D L (rightOccurrence f)
    · apply Prod.ext
      · simpa [labelsOfOccurrenceAssignment, projectionOccurrenceCoordinate] using
          occurrenceAssignmentOfConstantLabels_input D L (leftOccurrence f)
      · simpa [labelsOfOccurrenceAssignment, projectionOccurrenceCoordinate] using
          occurrenceAssignmentOfConstantLabels_input D L (rightOccurrence f)

private theorem occurrenceLabelsConstant_iff_blocks
    {m q : ℕ} (D : OccurrencePartitionData q)
    (labels : Fin q → ProjectionEntryLabel m) :
    OccurrenceLabelsConstant D labels ↔
      ∀ B ∈ (occurrencePartitionOfData D).parts,
        OccurrenceBlockLabelsConstant labels B := by
  classical
  constructor
  · rintro hconstant B hB z w
    rw [occurrencePartitionOfData_parts, occurrencePartitionParts,
      Finset.mem_union] at hB
    rcases hB with hB | hB
    · rw [Finset.mem_map] at hB
      obtain ⟨B0, hB0, rfl⟩ := hB
      obtain ⟨a, ha, haz⟩ := Finset.mem_map.mp z.2
      obtain ⟨b, hb, hbw⟩ := Finset.mem_map.mp w.2
      rw [← haz, ← hbw]
      apply hconstant.1
      rw [D.middle.part_eq_of_mem hB0 ha,
        D.middle.part_eq_of_mem hB0 hb]
    · rw [Finset.mem_map] at hB
      obtain ⟨B0, hB0, rfl⟩ := hB
      obtain ⟨a, ha, haz⟩ := Finset.mem_map.mp z.2
      obtain ⟨b, hb, hbw⟩ := Finset.mem_map.mp w.2
      rw [← haz, ← hbw]
      apply hconstant.2
      rw [D.input.part_eq_of_mem hB0 ha,
        D.input.part_eq_of_mem hB0 hb]
  · intro hblocks
    constructor
    · intro a b hab
      let B := (D.middle.part a).map (middlePositionEmbedding q)
      have hB : B ∈ (occurrencePartitionOfData D).parts := by
        rw [occurrencePartitionOfData_parts, occurrencePartitionParts]
        exact Finset.mem_union_left _ (Finset.mem_map.mpr
          ⟨D.middle.part a,
            D.middle.part_mem.mpr (Finset.mem_univ a), rfl⟩)
      have haB : middlePositionEmbedding q a ∈ B :=
        Finset.mem_map.mpr ⟨a, D.middle.mem_part (Finset.mem_univ a), rfl⟩
      have hbB : middlePositionEmbedding q b ∈ B :=
        Finset.mem_map.mpr ⟨b, by
          rw [Finpartition.mem_part_iff_part_eq_part D.middle
            (Finset.mem_univ b) (Finset.mem_univ a)]
          exact hab.symm, rfl⟩
      exact hblocks B hB ⟨_, haB⟩ ⟨_, hbB⟩
    · intro a b hab
      let B := (D.input.part a).map (inputPositionEmbedding q)
      have hB : B ∈ (occurrencePartitionOfData D).parts := by
        rw [occurrencePartitionOfData_parts, occurrencePartitionParts]
        exact Finset.mem_union_right _ (Finset.mem_map.mpr
          ⟨D.input.part a,
            D.input.part_mem.mpr (Finset.mem_univ a), rfl⟩)
      have haB : inputPositionEmbedding q a ∈ B :=
        Finset.mem_map.mpr ⟨a, D.input.mem_part (Finset.mem_univ a), rfl⟩
      have hbB : inputPositionEmbedding q b ∈ B :=
        Finset.mem_map.mpr ⟨b, by
          rw [Finpartition.mem_part_iff_part_eq_part D.input
            (Finset.mem_univ b) (Finset.mem_univ a)]
          exact hab.symm, rfl⟩
      exact hblocks B hB ⟨_, haB⟩ ⟨_, hbB⟩

private theorem occurrencePartitionParts_disjoint {q : ℕ}
    (D : OccurrencePartitionData q) :
    Disjoint
      (D.middle.parts.map (middleBlockEmbedding q))
      (D.input.parts.map (inputBlockEmbedding q)) := by
  classical
  rw [Finset.disjoint_left]
  intro B hmiddle hinput
  rw [Finset.mem_map] at hmiddle hinput
  obtain ⟨B0, hB0, rfl⟩ := hmiddle
  obtain ⟨C0, hC0, hBC⟩ := hinput
  change Finset.map (inputPositionEmbedding q) C0 =
    Finset.map (middlePositionEmbedding q) B0 at hBC
  obtain ⟨a, ha⟩ := D.middle.nonempty_of_mem_parts hB0
  have hma : middlePositionEmbedding q a ∈
      Finset.map (middlePositionEmbedding q) B0 :=
    Finset.mem_map.mpr ⟨a, ha, rfl⟩
  rw [← hBC] at hma
  obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hma
  have hfalse : Sum.inr b = Sum.inl a := by
    rw [← occurrencePositionEquiv_inputEmbedding b,
      ← occurrencePositionEquiv_middleEmbedding a]
    exact congrArg (occurrencePositionEquiv q) hba
  cases hfalse

private noncomputable def occurrenceCoefficient {q : ℕ}
    (D : OccurrencePartitionData q) : ℝ :=
  (∏ B : {B // B ∈ D.middle.parts}, rademacherCumulant B.1.card) *
    ∏ B : {B // B ∈ D.input.parts}, rademacherCumulant B.1.card

private theorem occurrenceBlockProduct_of_constant
    {m q : ℕ} (D : OccurrencePartitionData q)
    (labels : Fin q → ProjectionEntryLabel m)
    (hconstant : OccurrenceLabelsConstant D labels) :
    (∏ B ∈ (occurrencePartitionOfData D).parts,
      occurrenceBlockCumulantValue labels B) = occurrenceCoefficient D := by
  classical
  have hvalue : ∀ B ∈ (occurrencePartitionOfData D).parts,
      occurrenceBlockCumulantValue labels B = rademacherCumulant B.card := by
    intro B hB
    rw [occurrenceBlockCumulantValue]
    exact if_pos ⟨occurrencePartitionOfData_layerPure D B hB,
      (occurrenceLabelsConstant_iff_blocks D labels).mp hconstant B hB⟩
  calc
    (∏ B ∈ (occurrencePartitionOfData D).parts,
        occurrenceBlockCumulantValue labels B) =
        ∏ B ∈ (occurrencePartitionOfData D).parts,
          rademacherCumulant B.card := by
      apply Finset.prod_congr rfl
      exact hvalue
    _ = (∏ B ∈ D.middle.parts, rademacherCumulant B.card) *
          ∏ B ∈ D.input.parts, rademacherCumulant B.card := by
      rw [occurrencePartitionOfData_parts, occurrencePartitionParts,
        Finset.prod_union (occurrencePartitionParts_disjoint D)]
      congr 1
      · rw [Finset.prod_map]
        apply Finset.prod_congr rfl
        intro B hB
        change rademacherCumulant
          (Finset.map (middlePositionEmbedding q) B).card = _
        rw [Finset.card_map]
      · rw [Finset.prod_map]
        apply Finset.prod_congr rfl
        intro B hB
        change rademacherCumulant
          (Finset.map (inputPositionEmbedding q) B).card = _
        rw [Finset.card_map]
    _ = occurrenceCoefficient D := by
      rw [occurrenceCoefficient]
      congr 1
      · exact Finset.prod_subtype D.middle.parts (fun _ ↦ Iff.rfl)
          (fun B ↦ rademacherCumulant B.card)
      · exact Finset.prod_subtype D.input.parts (fun _ ↦ Iff.rfl)
          (fun B ↦ rademacherCumulant B.card)

private theorem occurrenceBlockProduct_eq_zero_of_not_constant
    {m q : ℕ} (D : OccurrencePartitionData q)
    (labels : Fin q → ProjectionEntryLabel m)
    (hconstant : ¬OccurrenceLabelsConstant D labels) :
    (∏ B ∈ (occurrencePartitionOfData D).parts,
      occurrenceBlockCumulantValue labels B) = 0 := by
  classical
  have hnotAll : ¬(∀ B ∈ (occurrencePartitionOfData D).parts,
      OccurrenceBlockLabelsConstant labels B) := by
    exact fun h ↦ hconstant
      ((occurrenceLabelsConstant_iff_blocks D labels).mpr h)
  push Not at hnotAll
  obtain ⟨B, hB, hnotB⟩ := hnotAll
  apply Finset.prod_eq_zero hB
  rw [occurrenceBlockCumulantValue]
  exact if_neg (fun h ↦ hnotB h.2)

private theorem prod_equalityVertices_indicator
    {q : ℕ} (P : Finpartition (Finset.univ : Finset (Fin (2 * q))))
    (a : Fin (2 * q)) (F : EqualityVertex P → ℝ) :
    (∏ B : EqualityVertex P, if a ∈ B.1 then F B else 1) =
      F (equalityVertexAt P a) := by
  classical
  have ha : a ∈ (equalityVertexAt P a).1 :=
    P.mem_part (Finset.mem_univ a)
  calc
    (∏ B : EqualityVertex P, if a ∈ B.1 then F B else 1) =
        if a ∈ (equalityVertexAt P a).1 then
          F (equalityVertexAt P a) else 1 := by
      apply Finset.prod_eq_single (equalityVertexAt P a)
      · intro B hB hne
        rw [if_neg]
        intro haB
        apply hne
        apply Subtype.ext
        exact (P.part_eq_of_mem B.2 haB).symm
      · simp
    _ = F (equalityVertexAt P a) := if_pos ha

private theorem occurrenceMiddleCharacterProduct_reindex
    {m q : ℕ} (D : OccurrencePartitionData q)
    (i j : Fin q → WalshIndex m)
    (c : OccurrenceVertex D → WalshIndex m) :
    (∏ f,
        walshCharacter (i f)
            (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f)))) *
          walshCharacter (j f)
            (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))))) =
      ∏ B : EqualityVertex D.middle,
        ∏ f,
          (if leftOccurrence f ∈ B.1 then
              walshCharacter (i f) (c (Sum.inl B)) else 1) *
            (if rightOccurrence f ∈ B.1 then
              walshCharacter (j f) (c (Sum.inl B)) else 1) := by
  classical
  let A : EqualityVertex D.middle → Fin q → ℝ := fun B f ↦
    if leftOccurrence f ∈ B.1 then
      walshCharacter (i f) (c (Sum.inl B)) else 1
  let C : EqualityVertex D.middle → Fin q → ℝ := fun B f ↦
    if rightOccurrence f ∈ B.1 then
      walshCharacter (j f) (c (Sum.inl B)) else 1
  have hA : ∀ f, (∏ B, A B f) =
      walshCharacter (i f)
        (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f)))) := by
    intro f
    exact prod_equalityVertices_indicator D.middle (leftOccurrence f)
      (fun B ↦ walshCharacter (i f) (c (Sum.inl B)))
  have hC : ∀ f, (∏ B, C B f) =
      walshCharacter (j f)
        (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f)))) := by
    intro f
    exact prod_equalityVertices_indicator D.middle (rightOccurrence f)
      (fun B ↦ walshCharacter (j f) (c (Sum.inl B)))
  symm
  calc
    (∏ B, ∏ f, A B f * C B f) =
        (∏ B, ∏ f, A B f) * (∏ B, ∏ f, C B f) := by
      simp_rw [Finset.prod_mul_distrib]
    _ = (∏ f, ∏ B, A B f) * (∏ f, ∏ B, C B f) := by
      congr 1 <;> rw [Finset.prod_comm]
    _ = (∏ f, walshCharacter (i f)
          (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))))) *
        ∏ f, walshCharacter (j f)
          (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f)))) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro f hf
        exact hA f
      · apply Finset.prod_congr rfl
        intro f hf
        exact hC f
    _ = ∏ f,
        walshCharacter (i f)
            (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f)))) *
          walshCharacter (j f)
            (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f)))) := by
      rw [Finset.prod_mul_distrib]

private noncomputable def occurrenceContractionSummand
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m)
    (c : OccurrenceVertex D → WalshIndex m) : ℝ :=
  (∏ f,
    normalizedWalsh m
        (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))))
        (c (Sum.inr (equalityVertexAt D.input (leftOccurrence f)))) *
      (V * V.transpose)
        (c (Sum.inr (equalityVertexAt D.input (leftOccurrence f))))
        (c (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))) *
      normalizedWalsh m
        (c (Sum.inr (equalityVertexAt D.input (rightOccurrence f))))
        (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))))) *
    ∏ B : EqualityVertex D.middle,
      ∏ f,
        (if leftOccurrence f ∈ B.1 then
          walshCharacter (i f) (c (Sum.inl B)) else 1) *
        (if rightOccurrence f ∈ B.1 then
          walshCharacter (j f) (c (Sum.inl B)) else 1)

private theorem occurrenceContraction_eq_sum_summand
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    occurrenceContraction D V i j =
      ∑ c : OccurrenceVertex D → WalshIndex m,
        occurrenceContractionSummand D V i j c := by
  rfl

private theorem projectionCoefficientProduct_labelsOfOccurrenceAssignment
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m)
    (c : OccurrenceVertex D → WalshIndex m) :
    (∏ f, projectionEntryCoefficient V (i f) (j f)
      (labelsOfOccurrenceAssignment D c f)) =
      occurrenceContractionSummand D V i j c := by
  classical
  let A : Fin q → ℝ := fun f ↦
    walshCharacter (i f)
        (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f)))) *
      walshCharacter (j f)
        (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))))
  let E : Fin q → ℝ := fun f ↦
    normalizedWalsh m
        (c (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))))
        (c (Sum.inr (equalityVertexAt D.input (leftOccurrence f)))) *
      (V * V.transpose)
        (c (Sum.inr (equalityVertexAt D.input (leftOccurrence f))))
        (c (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))) *
      normalizedWalsh m
        (c (Sum.inr (equalityVertexAt D.input (rightOccurrence f))))
        (c (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))))
  have hpoint : ∀ f,
      projectionEntryCoefficient V (i f) (j f)
          (labelsOfOccurrenceAssignment D c f) = A f * E f := by
    intro f
    simp only [projectionEntryCoefficient, labelsOfOccurrenceAssignment, A, E]
    ring
  calc
    (∏ f, projectionEntryCoefficient V (i f) (j f)
        (labelsOfOccurrenceAssignment D c f)) =
        ∏ f, A f * E f := by
      apply Finset.prod_congr rfl
      intro f hf
      exact hpoint f
    _ = (∏ f, A f) * ∏ f, E f := Finset.prod_mul_distrib
    _ = (∏ B : EqualityVertex D.middle,
          ∏ f,
            (if leftOccurrence f ∈ B.1 then
              walshCharacter (i f) (c (Sum.inl B)) else 1) *
            (if rightOccurrence f ∈ B.1 then
              walshCharacter (j f) (c (Sum.inl B)) else 1)) *
        ∏ f, E f := by
      rw [occurrenceMiddleCharacterProduct_reindex D i j c]
    _ = occurrenceContractionSummand D V i j c := by
      rw [occurrenceContractionSummand]
      ring

private theorem fixedOccurrenceDataLabelSum
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    (∑ labels : Fin q → ProjectionEntryLabel m,
        (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
          ∏ B ∈ (occurrencePartitionOfData D).parts,
            occurrenceBlockCumulantValue labels B) =
      occurrenceCoefficient D * occurrenceContraction D V i j := by
  classical
  let F : (Fin q → ProjectionEntryLabel m) → ℝ := fun labels ↦
    (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
      ∏ B ∈ (occurrencePartitionOfData D).parts,
        occurrenceBlockCumulantValue labels B
  have hzero : ∀ labels, ¬OccurrenceLabelsConstant D labels → F labels = 0 := by
    intro labels hnot
    change (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
      (∏ B ∈ (occurrencePartitionOfData D).parts,
        occurrenceBlockCumulantValue labels B) = 0
    rw [occurrenceBlockProduct_eq_zero_of_not_constant D labels hnot, mul_zero]
  calc
    (∑ labels : Fin q → ProjectionEntryLabel m,
        (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
          ∏ B ∈ (occurrencePartitionOfData D).parts,
            occurrenceBlockCumulantValue labels B) = ∑ labels, F labels := rfl
    _ = ∑ L : {labels // OccurrenceLabelsConstant D labels}, F L.1 :=
      fintype_sum_eq_subtype_sum_of_zero
        (OccurrenceLabelsConstant D) F hzero
    _ = ∑ c : OccurrenceVertex D → WalshIndex m,
        F (labelsOfOccurrenceAssignment D c) := by
      exact (Fintype.sum_equiv (occurrenceAssignmentLabelEquiv m D)
        (fun c ↦ F (labelsOfOccurrenceAssignment D c))
        (fun L ↦ F L.1) (fun _ ↦ rfl)).symm
    _ = ∑ c : OccurrenceVertex D → WalshIndex m,
        occurrenceCoefficient D * occurrenceContractionSummand D V i j c := by
      apply Finset.sum_congr rfl
      intro c hc
      change (∏ f, projectionEntryCoefficient V (i f) (j f)
          (labelsOfOccurrenceAssignment D c f)) *
        (∏ B ∈ (occurrencePartitionOfData D).parts,
          occurrenceBlockCumulantValue (labelsOfOccurrenceAssignment D c) B) = _
      rw [occurrenceBlockProduct_of_constant D
        (labelsOfOccurrenceAssignment D c)
        (labelsOfOccurrenceAssignment_constant D c),
        projectionCoefficientProduct_labelsOfOccurrenceAssignment D V i j c]
      ring
    _ = occurrenceCoefficient D *
        ∑ c : OccurrenceVertex D → WalshIndex m,
          occurrenceContractionSummand D V i j c := by
      rw [Finset.mul_sum]
    _ = occurrenceCoefficient D * occurrenceContraction D V i j := by
      rw [occurrenceContraction_eq_sum_summand]

private noncomputable def occurrenceDataTerm
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) : ℝ := by
  classical
  exact if ProductOccurrenceConnected D then
      occurrenceCoefficient D * occurrenceContraction D V i j
    else 0

private theorem fixedOccurrenceDataConnectedLabelSum
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    (∑ labels : Fin q → ProjectionEntryLabel m,
      (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
        fixedLabelConnectedPartitionTerm labels
          (occurrencePartitionOfData D)) = occurrenceDataTerm D V i j := by
  classical
  simp only [fixedLabelConnectedPartitionTerm, occurrenceDataTerm]
  by_cases hconnected : ProductOccurrenceConnected D
  · rw [if_pos hconnected]
    have hpartition :=
      (occurrenceProductConnected_iff_partitionConnected D).mp hconnected
    simp_rw [if_pos hpartition]
    exact fixedOccurrenceDataLabelSum D V i j
  · rw [if_neg hconnected]
    have hpartition : ¬ProductPartitionConnected
        (occurrencePartitionOfData D) (entryFactorPartition q) :=
      fun h ↦ hconnected
        ((occurrenceProductConnected_iff_partitionConnected D).mpr h)
    simp_rw [if_neg hpartition]
    simp

private theorem fixedLabelConnectedPartitionSum_reindex
    {m q : ℕ} (labels : Fin q → ProjectionEntryLabel m) :
    (∑ sigma : Finpartition (Finset.univ : Finset (Fin q × Fin 4)),
        fixedLabelConnectedPartitionTerm labels sigma) =
      ∑ D : OccurrencePartitionData q,
        fixedLabelConnectedPartitionTerm labels (occurrencePartitionOfData D) := by
  classical
  calc
    (∑ sigma : Finpartition (Finset.univ : Finset (Fin q × Fin 4)),
        fixedLabelConnectedPartitionTerm labels sigma) =
        ∑ sigma : LayerPureOccurrencePartition q,
          fixedLabelConnectedPartitionTerm labels sigma.1 := by
      exact fintype_sum_eq_subtype_sum_of_zero
        OccurrencePartitionLayerPure
        (fixedLabelConnectedPartitionTerm labels)
        (fixedLabelConnectedPartitionTerm_eq_zero_of_not_layerPure labels)
    _ = ∑ D : OccurrencePartitionData q,
        fixedLabelConnectedPartitionTerm labels (occurrencePartitionOfData D) := by
      exact (Fintype.sum_equiv (occurrenceDataPartitionEquiv q)
        (fun D ↦ fixedLabelConnectedPartitionTerm labels
          (occurrencePartitionOfData D))
        (fun sigma ↦ fixedLabelConnectedPartitionTerm labels sigma.1)
        (fun _ ↦ rfl)).symm

private theorem fullLabelPartitionSum_eq_occurrenceDataSum
    {m r q : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    (∑ labels : Fin q → ProjectionEntryLabel m,
      (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
        ∑ sigma : Finpartition (Finset.univ : Finset (Fin q × Fin 4)),
          fixedLabelConnectedPartitionTerm labels sigma) =
      ∑ D : OccurrencePartitionData q, occurrenceDataTerm D V i j := by
  classical
  calc
    (∑ labels : Fin q → ProjectionEntryLabel m,
      (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
        ∑ sigma : Finpartition (Finset.univ : Finset (Fin q × Fin 4)),
          fixedLabelConnectedPartitionTerm labels sigma) =
      ∑ labels : Fin q → ProjectionEntryLabel m,
        (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
          ∑ D : OccurrencePartitionData q,
            fixedLabelConnectedPartitionTerm labels
              (occurrencePartitionOfData D) := by
      apply Finset.sum_congr rfl
      intro labels hlabels
      rw [fixedLabelConnectedPartitionSum_reindex]
    _ = ∑ labels : Fin q → ProjectionEntryLabel m,
        ∑ D : OccurrencePartitionData q,
          (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
            fixedLabelConnectedPartitionTerm labels
              (occurrencePartitionOfData D) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ D : OccurrencePartitionData q,
        ∑ labels : Fin q → ProjectionEntryLabel m,
          (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
            fixedLabelConnectedPartitionTerm labels
              (occurrencePartitionOfData D) := by
      rw [Finset.sum_comm]
    _ = ∑ D : OccurrencePartitionData q, occurrenceDataTerm D V i j := by
      apply Finset.sum_congr rfl
      intro D hD
      exact fixedOccurrenceDataConnectedLabelSum D V i j

/-- The occurrence data underlying a pair of even sign-occurrence
partitions.  The first component is the middle-sign layer and the second is
the input-sign layer. -/
def occurrenceDataOfEvenPair {q : ℕ}
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q) :
    OccurrencePartitionData q :=
  ⟨P.1.1, P.2.1⟩

private def OccurrenceDataEven {q : ℕ}
    (D : OccurrencePartitionData q) : Prop :=
  (∀ B ∈ D.middle.parts, Even B.card) ∧
    ∀ B ∈ D.input.parts, Even B.card

private def evenOccurrenceDataEquiv (q : ℕ) :
    {D : OccurrencePartitionData q // OccurrenceDataEven D} ≃
      EvenOccurrencePartition q × EvenOccurrencePartition q where
  toFun D := (⟨D.1.middle, D.2.1⟩, ⟨D.1.input, D.2.2⟩)
  invFun P := ⟨occurrenceDataOfEvenPair P, ⟨P.1.2, P.2.2⟩⟩
  left_inv D := by
    rcases D with ⟨⟨middle, input⟩, heven⟩
    rfl
  right_inv P := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

private theorem occurrenceCoefficient_eq_zero_of_not_even {q : ℕ}
    (D : OccurrencePartitionData q) (hnotEven : ¬OccurrenceDataEven D) :
    occurrenceCoefficient D = 0 := by
  classical
  by_cases hmiddle : ∀ B ∈ D.middle.parts, Even B.card
  · have hnotInput : ¬(∀ B ∈ D.input.parts, Even B.card) :=
      fun hinput ↦ hnotEven ⟨hmiddle, hinput⟩
    push Not at hnotInput
    obtain ⟨B, hB, hodd⟩ := hnotInput
    have hrademacher : rademacherCumulant B.card = 0 :=
      rademacherCumulant_eq_zero_of_odd
        (Nat.not_even_iff_odd.mp hodd)
    have hproduct :
        (∏ C : {C // C ∈ D.input.parts},
          rademacherCumulant C.1.card) = 0 := by
      apply Finset.prod_eq_zero
        (s := (Finset.univ : Finset {C // C ∈ D.input.parts}))
        (Finset.mem_univ ⟨B, hB⟩)
      exact hrademacher
    rw [occurrenceCoefficient, hproduct, mul_zero]
  · push Not at hmiddle
    obtain ⟨B, hB, hodd⟩ := hmiddle
    have hrademacher : rademacherCumulant B.card = 0 :=
      rademacherCumulant_eq_zero_of_odd
        (Nat.not_even_iff_odd.mp hodd)
    have hproduct :
        (∏ C : {C // C ∈ D.middle.parts},
          rademacherCumulant C.1.card) = 0 := by
      apply Finset.prod_eq_zero
        (s := (Finset.univ : Finset {C // C ∈ D.middle.parts}))
        (Finset.mem_univ ⟨B, hB⟩)
      exact hrademacher
    rw [occurrenceCoefficient, hproduct, zero_mul]

private theorem occurrenceDataTerm_eq_zero_of_not_even
    {m r q : ℕ} (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m)
    (hnotEven : ¬OccurrenceDataEven D) :
    occurrenceDataTerm D V i j = 0 := by
  classical
  rw [occurrenceDataTerm]
  by_cases hconnected : ProductOccurrenceConnected D
  · rw [if_pos hconnected,
      occurrenceCoefficient_eq_zero_of_not_even D hnotEven, zero_mul]
  · exact if_neg hconnected

/-- Product of the two layers' one-coordinate Rademacher cumulants. -/
noncomputable def evenOccurrenceCoefficient {q : ℕ}
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q) : ℝ :=
  (∏ B : {B // B ∈ P.1.1.parts}, rademacherCumulant B.1.card) *
    ∏ B : {B // B ∈ P.2.1.parts}, rademacherCumulant B.1.card

/-- One connected-even occurrence-pair contribution. -/
noncomputable def jointEntryOccurrenceTerm {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m)
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q) : ℝ := by
  classical
  exact if ProductOccurrenceConnected (occurrenceDataOfEvenPair P) then
    evenOccurrenceCoefficient P *
      occurrenceContraction (occurrenceDataOfEvenPair P) V i j
  else 0

private theorem occurrenceCoefficient_ofEvenPair {q : ℕ}
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q) :
    occurrenceCoefficient (occurrenceDataOfEvenPair P) =
      evenOccurrenceCoefficient P := by
  rcases P with ⟨⟨Pmiddle, hmiddle⟩, ⟨Pinput, hinput⟩⟩
  rfl

private theorem occurrenceDataTerm_ofEvenPair
    {m r q : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m)
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q) :
    occurrenceDataTerm (occurrenceDataOfEvenPair P) V i j =
      jointEntryOccurrenceTerm V i j P := by
  classical
  simp only [occurrenceDataTerm, jointEntryOccurrenceTerm]
  by_cases hconnected : ProductOccurrenceConnected
      ({middle := P.1.1, input := P.2.1} : OccurrencePartitionData q) <;>
    simp [occurrenceCoefficient_ofEvenPair P]

private theorem occurrenceDataSum_eq_evenOccurrencePairSum
    {m r q : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    (∑ D : OccurrencePartitionData q, occurrenceDataTerm D V i j) =
      ∑ P : EvenOccurrencePartition q × EvenOccurrencePartition q,
        jointEntryOccurrenceTerm V i j P := by
  classical
  calc
    (∑ D : OccurrencePartitionData q, occurrenceDataTerm D V i j) =
        ∑ D : {D : OccurrencePartitionData q // OccurrenceDataEven D},
          occurrenceDataTerm D.1 V i j := by
      exact fintype_sum_eq_subtype_sum_of_zero OccurrenceDataEven
        (fun D ↦ occurrenceDataTerm D V i j)
        (fun D ↦ occurrenceDataTerm_eq_zero_of_not_even D V i j)
    _ = ∑ P : EvenOccurrencePartition q × EvenOccurrencePartition q,
        occurrenceDataTerm (occurrenceDataOfEvenPair P) V i j := by
      exact Fintype.sum_equiv (evenOccurrenceDataEquiv q)
        (fun D ↦ occurrenceDataTerm D.1 V i j)
        (fun P ↦ occurrenceDataTerm (occurrenceDataOfEvenPair P) V i j)
        (fun _ ↦ rfl)
    _ = ∑ P : EvenOccurrencePartition q × EvenOccurrencePartition q,
        jointEntryOccurrenceTerm V i j P := by
      apply Finset.sum_congr rfl
      intro P hP
      exact occurrenceDataTerm_ofEvenPair V i j P

/-- The literal finite occurrence-partition expansion used by the paper.
This definition names the remaining combinatorial identity without weakening
it: only pairs of even layer partitions occur, and the product-join predicate
is exactly the connectedness condition from the finite product-cumulant
formula. -/
noncomputable def HasJointEntryOccurrenceExpansion {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) : Prop :=
  jointCumulant
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) *
        randomProjection d.1 d.2 V (i f) (j f)) =
    ∑ P : EvenOccurrencePartition q × EvenOccurrencePartition q,
      jointEntryOccurrenceTerm V i j P

/-- The remaining finite reindexing after all analytic and cumulant algebra has
been eliminated.  Its left side is the fully evaluated label/partition
expansion; its right side is the occurrence-graph contraction sum. -/
private noncomputable def HasJointEntryOccurrenceReindex {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) : Prop :=
  (∑ labels : Fin q → ProjectionEntryLabel m,
      (∏ f, projectionEntryCoefficient V (i f) (j f) (labels f)) *
        ∑ σ : Finpartition (Finset.univ : Finset (Fin q × Fin 4)),
          fixedLabelConnectedPartitionTerm labels σ) =
    ∑ P : EvenOccurrencePartition q × EvenOccurrencePartition q,
      jointEntryOccurrenceTerm V i j P

private theorem hasJointEntryOccurrenceExpansion_iff_reindex
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    HasJointEntryOccurrenceExpansion V i j ↔
      HasJointEntryOccurrenceReindex V i j := by
  rw [HasJointEntryOccurrenceExpansion, HasJointEntryOccurrenceReindex,
    joint_entry_label_expansion]
  simp_rw [joint_entry_sign_evaluated_partition_expansion]

private theorem hasJointEntryOccurrenceReindex
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    HasJointEntryOccurrenceReindex V i j := by
  rw [HasJointEntryOccurrenceReindex,
    fullLabelPartitionSum_eq_occurrenceDataSum V i j,
    occurrenceDataSum_eq_evenOccurrencePairSum V i j]

/-- Exact finite reindexing of the joint-entry cumulant into connected pairs
of even occurrence partitions. -/
theorem hasJointEntryOccurrenceExpansion
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    HasJointEntryOccurrenceExpansion V i j :=
  (hasJointEntryOccurrenceExpansion_iff_reindex V i j).2
    (hasJointEntryOccurrenceReindex V i j)

/-- The exact graph-rank statement needed by the occurrence contractions.
It is a parameter here so this module does not import the still-open I07
wrapper through `Statements`. -/
def GraphRankContractionPrinciple : Prop :=
  ∀ {ι ε : Type} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (r : ℕ),
    GraphConnected src dst →
    (∀ v, Even (graphDegree src dst v)) →
    (∀ v, 0 < graphDegree src dst v) →
    (∀ e, euclideanOperatorNorm (M e) ≤ 1) →
    (∀ v a, |w v a| ≤ 1) →
    (1 ≤ r ∧ HasRankProjectionEdge dim src dst M r) →
    |graphContraction dim src dst M w| ≤ r

private theorem evenOccurrenceCoefficient_abs_le
    {q : ℕ} (P : EvenOccurrencePartition q × EvenOccurrencePartition q) :
    |evenOccurrenceCoefficient P| ≤ ((2 * q : ℕ) : ℝ) ^ (8 * q) := by
  let C : ℝ := ((2 * q : ℕ) : ℝ) ^ (4 * q)
  have hleft :
      |∏ B : {B // B ∈ P.1.1.parts}, rademacherCumulant B.1.card| ≤ C :=
    (rademacher_cumulant_bound q).2.2 P.1
  have hright :
      |∏ B : {B // B ∈ P.2.1.parts}, rademacherCumulant B.1.card| ≤ C :=
    (rademacher_cumulant_bound q).2.2 P.2
  rw [evenOccurrenceCoefficient, abs_mul]
  calc
    _ ≤ C * C := mul_le_mul hleft hright (abs_nonneg _) (by positivity)
    _ = ((2 * q : ℕ) : ℝ) ^ (8 * q) := by
      simp only [C, ← pow_add]
      congr 1
      omega

private theorem occurrenceDataOfEvenPair_blocks
    {q : ℕ} (P : EvenOccurrencePartition q × EvenOccurrencePartition q) :
    (∀ B ∈ (occurrenceDataOfEvenPair P).middle.parts,
      0 < B.card ∧ Even B.card) ∧
    (∀ B ∈ (occurrenceDataOfEvenPair P).input.parts,
      0 < B.card ∧ Even B.card) := by
  constructor
  · intro B hB
    exact ⟨Finset.card_pos.mpr (P.1.1.nonempty_of_mem_parts hB), P.1.2 B hB⟩
  · intro B hB
    exact ⟨Finset.card_pos.mpr (P.2.1.nonempty_of_mem_parts hB), P.2.2 B hB⟩

private theorem occurrenceContraction_abs_le_rank
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m)
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q)
    (hconnected : ProductOccurrenceConnected (occurrenceDataOfEvenPair P)) :
    |occurrenceContraction (occurrenceDataOfEvenPair P) V i j| ≤ r := by
  obtain ⟨hblocksMiddle, hblocksInput⟩ := occurrenceDataOfEvenPair_blocks P
  obtain ⟨_, hconn, hdegree, _, _, _, hnorm, hweight, hrank, heq⟩ :=
    occurrence_partitions_form_connected_even_graph hq
      (occurrenceDataOfEvenPair P) V hV i j
      hblocksMiddle hblocksInput hconnected
  rw [heq]
  exact hgraph
    (ι := OccurrenceVertex (occurrenceDataOfEvenPair P))
    (ε := OccurrenceEdge q)
    (fun _ : OccurrenceVertex (occurrenceDataOfEvenPair P) ↦ walshCard m)
    (occurrenceSrc (occurrenceDataOfEvenPair P))
    (occurrenceDst (occurrenceDataOfEvenPair P))
    (occurrenceEdgeMatrix (occurrenceDataOfEvenPair P) V)
    (occurrenceVertexWeight (occurrenceDataOfEvenPair P) i j) r
    hconn (fun v ↦ (hdegree v).2) (fun v ↦ (hdegree v).1)
    hnorm hweight ⟨hr, hrank⟩

private theorem joint_entry_occurrence_term_abs_le
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m)
    (P : EvenOccurrencePartition q × EvenOccurrencePartition q) :
    |jointEntryOccurrenceTerm V i j P| ≤
      ((2 * q : ℕ) : ℝ) ^ (8 * q) * r := by
  classical
  rw [jointEntryOccurrenceTerm]
  by_cases hconnected : ProductOccurrenceConnected (occurrenceDataOfEvenPair P)
  · rw [if_pos hconnected, abs_mul]
    exact mul_le_mul (evenOccurrenceCoefficient_abs_le P)
      (occurrenceContraction_abs_le_rank hgraph hq hr V hV i j P hconnected)
      (abs_nonneg _) (by positivity)
  · rw [if_neg hconnected, abs_zero]
    exact mul_nonneg (by positivity) (Nat.cast_nonneg r)

private theorem randomProjection_rank_zero
    {m : ℕ} (V : Matrix (WalshIndex m) (Fin 0) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) :
    randomProjection d₁ d₂ V = 0 := by
  have hV : V = 0 := by
    ext a b
    exact Fin.elim0 b
  rw [hV]
  simp [randomProjection, transformedFrame]

private theorem jointCumulant_zero
    {Ω : Type*} [Fintype Ω] {q : ℕ} (hq : 1 ≤ q) :
    jointCumulant (Ω := Ω)
      (fun (_ : Fin q) (_ : Ω) ↦ (0 : ℝ)) = 0 := by
  let _ : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hq0 : q ≠ 0 := by omega
  simpa [jointCumulant, hq0] using
    (jointCumulantOn_const_family_mul (Ω := Ω) (ι := Fin q)
      (fun _ ↦ (0 : ℝ)) (fun _ _ ↦ (1 : ℝ)))

theorem joint_entry_cumulant_bound_of_occurrence_expansion
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m) (hq : 1 ≤ q)
    (hexpansion : HasJointEntryOccurrenceExpansion V i j) :
    |jointCumulant
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) *
        randomProjection d.1 d.2 V (i f) (j f))| ≤
      ((2 * q : ℕ) : ℝ) ^ (12 * q) * r := by
  classical
  by_cases hr0 : r = 0
  · subst r
    have hzeroVariables :
        (fun f (d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m)) ↦
          (walshCard m : ℝ) * randomProjection d.1 d.2 V (i f) (j f)) =
        (fun _ _ ↦ (0 : ℝ)) := by
      funext f d
      rw [randomProjection_rank_zero V d.1 d.2]
      simp
    rw [hzeroVariables, jointCumulant_zero hq]
    simp
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    rw [hexpansion]
    let T : EvenOccurrencePartition q × EvenOccurrencePartition q → ℝ :=
      fun P ↦ jointEntryOccurrenceTerm V i j P
    calc
      |∑ P, T P| ≤ ∑ P, |T P| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _P : EvenOccurrencePartition q × EvenOccurrencePartition q,
          ((2 * q : ℕ) : ℝ) ^ (8 * q) * r := by
        apply Finset.sum_le_sum
        intro P _
        exact joint_entry_occurrence_term_abs_le hgraph hq hr V hV i j P
      _ = (Fintype.card
            (EvenOccurrencePartition q × EvenOccurrencePartition q) : ℝ) *
          (((2 * q : ℕ) : ℝ) ^ (8 * q) * r) := by simp
      _ ≤ (((2 * q : ℕ) : ℝ) ^ (4 * q)) *
          (((2 * q : ℕ) : ℝ) ^ (8 * q) * r) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (rademacher_cumulant_bound q).2.1
        · positivity
      _ = ((2 * q : ℕ) : ℝ) ^ (12 * q) * r := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega

theorem joint_entry_cumulant_assembly_of_occurrence_expansion
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m) (hq : 1 ≤ q)
    (hexpansion : HasJointEntryOccurrenceExpansion V i j) :
    |jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) *
        randomProjection d.1 d.2 V (i f) (j f))| ≤
        ((2 * q : ℕ) : ℝ) ^ (12 * q) * r ∧
    ((∑ f, (i f + j f)) ≠ 0 →
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ (walshCard m : ℝ) *
          randomProjection d.1 d.2 V (i f) (j f)) = 0) ∧
    (∀ a b, signPairExpectation
      (fun d₁ d₂ ↦ randomProjection d₁ d₂ V a b) =
        if a = b then (r : ℝ) / walshCard m else 0) := by
  exact ⟨joint_entry_cumulant_bound_of_occurrence_expansion
      hgraph V hV i j hq hexpansion,
    joint_entry_cumulant_vanish V i j,
    joint_entry_projection_mean V hV⟩

/-- The quantitative joint-entry cumulant bound, conditional only on the
still-separate graph-rank contraction principle.  The finite occurrence
expansion is proved internally above. -/
theorem joint_entry_cumulant_bound
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m) (hq : 1 ≤ q) :
    |jointCumulant
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) *
        randomProjection d.1 d.2 V (i f) (j f))| ≤
      ((2 * q : ℕ) : ℝ) ^ (12 * q) * r :=
  joint_entry_cumulant_bound_of_occurrence_expansion
    hgraph V hV i j hq (hasJointEntryOccurrenceExpansion V i j)

/-- Joint-entry cumulant assembly with the exact occurrence reindexing
discharged.  The graph-rank principle remains explicit because I07 is a
separate open obligation. -/
theorem joint_entry_cumulant_assembly
    (hgraph : GraphRankContractionPrinciple)
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m) (hq : 1 ≤ q) :
    |jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) *
        randomProjection d.1 d.2 V (i f) (j f))| ≤
        ((2 * q : ℕ) : ℝ) ^ (12 * q) * r ∧
    ((∑ f, (i f + j f)) ≠ 0 →
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ (walshCard m : ℝ) *
          randomProjection d.1 d.2 V (i f) (j f)) = 0) ∧
    (∀ a b, signPairExpectation
      (fun d₁ d₂ ↦ randomProjection d₁ d₂ V a b) =
        if a = b then (r : ℝ) / walshCard m else 0) :=
  joint_entry_cumulant_assembly_of_occurrence_expansion
    hgraph V hV i j hq (hasJointEntryOccurrenceExpansion V i j)

#print axioms jointCumulantOn_sum_family
#print axioms joint_entry_cumulant_vanish
#print axioms joint_entry_projection_mean
#print axioms joint_entry_label_expansion
#print axioms joint_entry_sign_connected_partition_expansion
#print axioms joint_entry_sign_evaluated_partition_expansion
#print axioms hasJointEntryOccurrenceExpansion
#print axioms joint_entry_cumulant_bound
#print axioms joint_entry_cumulant_assembly
#print axioms joint_entry_cumulant_bound_of_occurrence_expansion
#print axioms joint_entry_cumulant_assembly_of_occurrence_expansion

end Problem56
