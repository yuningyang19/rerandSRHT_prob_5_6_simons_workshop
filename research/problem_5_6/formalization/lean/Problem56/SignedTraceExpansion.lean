import Problem56.AggregatePartitionCumulant
import Problem56.CumulantMoment
import Problem56.JointEntryCumulant
import Problem56.PointwiseVanishing
import Problem56.ProjectionMean
import Problem56.SelectorQuotient
import Problem56.SignedTraceExpectationExpansion
import Problem56.SignedTraceSummation
import Problem56.XorKernel

/-!
# Exact finite expansion behind the signed-trace estimate

This file supplies the finite algebra which precedes
`signedTrace_bound_of_master_geometric_bound`.  In particular, selector
averaging is performed with the literal product Bernoulli law, and the
absolute value is applied only after the signed trace has been averaged.
-/

open scoped BigOperators Matrix

namespace Problem56

set_option maxHeartbeats 8000000

noncomputable section

def centeredSelector (theta : ℝ) {alpha : Type*} (e : SignLayer alpha)
    (a : alpha) : ℝ :=
  (if e a then 1 else 0) - theta

private theorem bernoulliExpectation_sum
    {alpha kappa : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype kappa] (theta : ℝ) (F : kappa → SignLayer alpha → ℝ) :
    bernoulliExpectation theta (fun e ↦ ∑ k, F k e) =
      ∑ k, bernoulliExpectation theta (F k) := by
  classical
  unfold bernoulliExpectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem bernoulliExpectation_const_mul
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (theta c : ℝ) (F : SignLayer alpha → ℝ) :
    bernoulliExpectation theta (fun e ↦ c * F e) =
      c * bernoulliExpectation theta F := by
  classical
  unfold bernoulliExpectation
  calc
    (∑ e, bernoulliWeight theta e * (c * F e)) =
        ∑ e, c * (bernoulliWeight theta e * F e) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = c * ∑ e, bernoulliWeight theta e * F e := by
      rw [Finset.mul_sum]

private theorem product_fibers_apply
    {iota alpha beta : Type*} [Fintype iota] [Fintype alpha]
    [DecidableEq alpha] [CommMonoid beta]
    (label : iota → alpha) (f : iota → beta) :
    (∏ a : alpha, ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), f i) =
      ∏ i, f i := by
  simpa only [Finset.mem_univ, true_and] using
    (Finset.prod_fiberwise (Finset.univ : Finset iota) label f)

/-- Independence of the coordinates, proved directly from the finite product
Bernoulli weight.  No measure-theoretic independence interface is used. -/
theorem bernoulliExpectation_product_by_coordinate
    {iota alpha : Type*} [Fintype iota] [Fintype alpha]
    [DecidableEq alpha]
    (theta : ℝ) (label : iota → alpha) (f : iota → Bool → ℝ) :
    bernoulliExpectation theta
        (fun e ↦ ∏ i, f i (e (label i))) =
      ∏ a : alpha,
        ((1 - theta) *
            ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), f i false +
          theta *
            ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), f i true) := by
  classical
  unfold bernoulliExpectation bernoulliWeight
  calc
    (∑ e : SignLayer alpha,
        (∏ a, if e a then theta else 1 - theta) *
          ∏ i, f i (e (label i))) =
      ∑ e : SignLayer alpha,
        ∏ a,
          ((if e a then theta else 1 - theta) *
            ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a),
              f i (e a)) := by
        apply Finset.sum_congr rfl
        intro e _
        have hfiber :
            (∏ i, f i (e (label i))) =
              ∏ a : alpha,
                ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), f i (e a) := by
          rw [← product_fibers_apply label (fun i ↦ f i (e (label i)))]
          apply Finset.prod_congr rfl
          intro a _
          apply Finset.prod_congr rfl
          intro i hi
          have hlabel : label i = a := (Finset.mem_filter.mp hi).2
          rw [hlabel]
        rw [hfiber, Finset.prod_mul_distrib]
    _ = ∏ a : alpha, ∑ b : Bool,
          ((if b then theta else 1 - theta) *
            ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), f i b) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      simp
      ring

private abbrev PartitionBlock {iota : Type*} [Fintype iota]
    [DecidableEq iota]
    (P : Finpartition (Finset.univ : Finset iota)) :=
  {B : Finset iota // B ∈ P.parts}

private def partitionVertexAt
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (P : Finpartition (Finset.univ : Finset iota)) (i : iota) :
    PartitionBlock P :=
  ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩

private noncomputable def partitionBlockRepresentative
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (P : Finpartition (Finset.univ : Finset iota))
    (B : PartitionBlock P) : iota :=
  Classical.choose (P.nonempty_of_mem_parts B.2)

private theorem partitionBlockRepresentative_mem
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (P : Finpartition (Finset.univ : Finset iota))
    (B : PartitionBlock P) :
    partitionBlockRepresentative P B ∈ B.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts B.2)

private noncomputable def equalityPartition
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha] (label : iota → alpha) :
    Finpartition (Finset.univ : Finset iota) :=
  Finpartition.ofSetoid (Setoid.ker label)

private theorem equalityPartition_part_eq_iff
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha] (label : iota → alpha) (i j : iota) :
    (equalityPartition label).part i = (equalityPartition label).part j ↔
      label i = label j := by
  calc
    (equalityPartition label).part i = (equalityPartition label).part j ↔
        j ∈ (equalityPartition label).part i := by
      rw [Finpartition.mem_part_iff_part_eq_part (equalityPartition label)
        (Finset.mem_univ j) (Finset.mem_univ i)]
      exact eq_comm
    _ ↔ label j = label i := by
      change j ∈ (Finpartition.ofSetoid (Setoid.ker label)).part i ↔ _
      rw [Finpartition.mem_part_ofSetoid_iff_rel]
      exact eq_comm
    _ ↔ label i = label j := by
      exact eq_comm

private theorem finpartition_eq_of_part_eq
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (P Q : Finpartition (Finset.univ : Finset iota))
    (h : ∀ i, P.part i = Q.part i) : P = Q := by
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB hi, h i]
    exact Q.part_mem.mpr (Finset.mem_univ i)
  · intro hB
    obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB hi, ← h i]
    exact P.part_mem.mpr (Finset.mem_univ i)

private abbrev InjectivePartitionLabeling
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (P : Finpartition (Finset.univ : Finset iota)) (alpha : Type*) :=
  {lab : PartitionBlock P → alpha // Function.Injective lab}

private def labelOfPartition
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    (P : Finpartition (Finset.univ : Finset iota))
    (lab : PartitionBlock P → alpha) : iota → alpha :=
  fun i ↦ lab (partitionVertexAt P i)

private noncomputable def partitionLabelingOfFunction
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha] (label : iota → alpha) :
    PartitionBlock (equalityPartition label) → alpha :=
  fun B ↦ label (partitionBlockRepresentative (equalityPartition label) B)

private theorem partitionLabelingOfFunction_injective
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha] (label : iota → alpha) :
    Function.Injective (partitionLabelingOfFunction label) := by
  intro B C hBC
  let P := equalityPartition label
  let b := partitionBlockRepresentative P B
  let c := partitionBlockRepresentative P C
  have hb : b ∈ B.1 := partitionBlockRepresentative_mem P B
  have hc : c ∈ C.1 := partitionBlockRepresentative_mem P C
  have hparts : P.part b = P.part c :=
    (equalityPartition_part_eq_iff label b c).mpr hBC
  apply Subtype.ext
  calc
    B.1 = P.part b := (P.part_eq_of_mem B.2 hb).symm
    _ = P.part c := hparts
    _ = C.1 := P.part_eq_of_mem C.2 hc

private theorem labelOf_partitionLabelingOfFunction
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha] (label : iota → alpha) :
    labelOfPartition (equalityPartition label)
        (partitionLabelingOfFunction label) = label := by
  funext i
  let P := equalityPartition label
  let B := partitionVertexAt P i
  let b := partitionBlockRepresentative P B
  have hbB : b ∈ B.1 := partitionBlockRepresentative_mem P B
  have hiB : i ∈ B.1 := P.mem_part (Finset.mem_univ i)
  have hpart : P.part b = P.part i := by
    rw [← Finpartition.mem_part_iff_part_eq_part P
      (Finset.mem_univ b) (Finset.mem_univ i)]
    exact hbB
  exact (equalityPartition_part_eq_iff label b i).mp hpart

private theorem equalityPartition_labelOfPartition
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha]
    (P : Finpartition (Finset.univ : Finset iota))
    (lab : PartitionBlock P → alpha) (hinj : Function.Injective lab) :
    equalityPartition (labelOfPartition P lab) = P := by
  apply finpartition_eq_of_part_eq
  intro i
  ext j
  calc
    j ∈ (equalityPartition (labelOfPartition P lab)).part i ↔
        labelOfPartition P lab j = labelOfPartition P lab i := by
      change j ∈ (Finpartition.ofSetoid
        (Setoid.ker (labelOfPartition P lab))).part i ↔ _
      rw [Finpartition.mem_part_ofSetoid_iff_rel]
      exact eq_comm
    _ ↔ partitionVertexAt P j = partitionVertexAt P i := hinj.eq_iff
    _ ↔ P.part j = P.part i := by
      simp only [partitionVertexAt, Subtype.mk.injEq]
    _ ↔ j ∈ P.part i := by
      rw [Finpartition.mem_part_iff_part_eq_part P
        (Finset.mem_univ j) (Finset.mem_univ i)]

private noncomputable def functionPartitionEquiv
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype alpha] [DecidableEq alpha] :
    (iota → alpha) ≃
      (Σ P : Finpartition (Finset.univ : Finset iota),
        InjectivePartitionLabeling P alpha) where
  toFun label := ⟨equalityPartition label,
    ⟨partitionLabelingOfFunction label,
      partitionLabelingOfFunction_injective label⟩⟩
  invFun data := labelOfPartition data.1 data.2.1
  left_inv := labelOf_partitionLabelingOfFunction
  right_inv data := by
    rcases data with ⟨P, lab⟩
    change (⟨equalityPartition (labelOfPartition P lab.1),
      (⟨partitionLabelingOfFunction (labelOfPartition P lab.1),
        partitionLabelingOfFunction_injective (labelOfPartition P lab.1)⟩ :
          InjectivePartitionLabeling
            (equalityPartition (labelOfPartition P lab.1)) alpha)⟩ :
      Σ Q : Finpartition (Finset.univ : Finset iota),
        InjectivePartitionLabeling Q alpha) = ⟨P, lab⟩
    generalize hf : labelOfPartition P lab.1 = f
    change (⟨equalityPartition f,
      (⟨partitionLabelingOfFunction f,
        partitionLabelingOfFunction_injective f⟩ :
          InjectivePartitionLabeling (equalityPartition f) alpha)⟩ :
      Σ Q : Finpartition (Finset.univ : Finset iota),
        InjectivePartitionLabeling Q alpha) = ⟨P, lab⟩
    have hP : equalityPartition f = P := by
      rw [← hf]
      exact equalityPartition_labelOfPartition P lab.1 lab.2
    apply Sigma.ext hP
    cases hP
    apply heq_of_eq
    apply Subtype.ext
    dsimp only
    funext B
    let b := partitionBlockRepresentative (equalityPartition f) B
    have hb : b ∈ B.1 :=
      partitionBlockRepresentative_mem (equalityPartition f) B
    change f b = lab.1 B
    rw [← congrFun hf b]
    change lab.1 (partitionVertexAt (equalityPartition f) b) = lab.1 B
    exact congrArg lab.1 (Subtype.ext
      ((equalityPartition f).part_eq_of_mem B.2 hb))

private def selectorCoordinateFactor
    {iota alpha : Type*} [Fintype iota] [Fintype alpha]
    [DecidableEq alpha]
    (theta : ℝ) (label : iota → alpha) (a : alpha) : ℝ :=
  (1 - theta) *
      ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), (-theta) +
    theta *
      ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a), (1 - theta)

private def selectorMoment
    {iota alpha : Type*} [Fintype iota] [Fintype alpha]
    [DecidableEq alpha]
    (theta : ℝ) (label : iota → alpha) : ℝ :=
  bernoulliExpectation theta
    (fun e ↦ ∏ i, centeredSelector theta e (label i))

private theorem selectorMoment_eq_product_coordinate
    {iota alpha : Type*} [Fintype iota] [Fintype alpha]
    [DecidableEq alpha]
    (theta : ℝ) (label : iota → alpha) :
    selectorMoment theta label =
      ∏ a, selectorCoordinateFactor theta label a := by
  unfold selectorMoment
  calc
    bernoulliExpectation theta
        (fun e ↦ ∏ i, centeredSelector theta e (label i)) =
      ∏ a : alpha,
        ((1 - theta) *
            ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a),
              ((if false then 1 else 0) - theta) +
          theta *
            ∏ i ∈ (Finset.univ.filter fun i ↦ label i = a),
              ((if true then 1 else 0) - theta)) := by
      change bernoulliExpectation theta
          (fun e ↦ ∏ i, ((if e (label i) then 1 else 0) - theta)) = _
      exact bernoulliExpectation_product_by_coordinate theta label
        (fun _i b ↦ (if b then 1 else 0) - theta)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      simp [selectorCoordinateFactor]

private theorem labelOfPartition_fiber_eq_block
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha]
    (P : Finpartition (Finset.univ : Finset iota))
    (lab : InjectivePartitionLabeling P alpha) (B : PartitionBlock P) :
    (Finset.univ.filter fun i ↦ labelOfPartition P lab.1 i = lab.1 B) = B.1 := by
  ext i
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, labelOfPartition]
  constructor
  · intro hi
    have hv : partitionVertexAt P i = B := lab.2 hi
    change i ∈ B.1
    rw [← hv]
    exact P.mem_part (Finset.mem_univ i)
  · intro hi
    apply congrArg lab.1
    apply Subtype.ext
    exact (P.part_eq_of_mem B.2 hi)

private theorem labelOfPartition_fiber_eq_empty
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [DecidableEq alpha]
    (P : Finpartition (Finset.univ : Finset iota))
    (lab : InjectivePartitionLabeling P alpha) (a : alpha)
    (ha : a ∉ Finset.univ.image lab.1) :
    (Finset.univ.filter fun i ↦ labelOfPartition P lab.1 i = a) = ∅ := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  intro hi
  apply ha
  rw [Finset.mem_image]
  exact ⟨partitionVertexAt P i, Finset.mem_univ _, hi⟩

private theorem selectorCoordinateFactor_of_block
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype alpha] [DecidableEq alpha]
    (theta : ℝ) (P : Finpartition (Finset.univ : Finset iota))
    (lab : InjectivePartitionLabeling P alpha) (B : PartitionBlock P) :
    selectorCoordinateFactor theta (labelOfPartition P lab.1) (lab.1 B) =
      theta * (1 - theta) ^ B.1.card +
        (1 - theta) * (-theta) ^ B.1.card := by
  rw [selectorCoordinateFactor, labelOfPartition_fiber_eq_block P lab B]
  simp only [Finset.prod_const, mul_comm]
  ring

private theorem selectorCoordinateFactor_of_unused
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype alpha] [DecidableEq alpha]
    (theta : ℝ) (P : Finpartition (Finset.univ : Finset iota))
    (lab : InjectivePartitionLabeling P alpha) (a : alpha)
    (ha : a ∉ Finset.univ.image lab.1) :
    selectorCoordinateFactor theta (labelOfPartition P lab.1) a = 1 := by
  rw [selectorCoordinateFactor, labelOfPartition_fiber_eq_empty P lab a ha]
  simp

private theorem selectorMoment_eq_zero_of_singleton
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype alpha] [DecidableEq alpha]
    (theta : ℝ) (P : Finpartition (Finset.univ : Finset iota))
    (lab : InjectivePartitionLabeling P alpha)
    (B : Finset iota) (hB : B ∈ P.parts) (hcard : B.card = 1) :
    selectorMoment theta (labelOfPartition P lab.1) = 0 := by
  rw [selectorMoment_eq_product_coordinate]
  apply Finset.prod_eq_zero (Finset.mem_univ (lab.1 ⟨B, hB⟩))
  rw [selectorCoordinateFactor_of_block theta P lab ⟨B, hB⟩, hcard]
  ring

private theorem product_indicator_eq_pow_card_image
    {iota alpha : Type*} [Fintype iota] [Fintype alpha]
    [DecidableEq alpha]
    (theta : ℝ) (lab : iota → alpha) :
    (∏ a : alpha, if a ∈ Finset.univ.image lab then theta else 1) =
      theta ^ (Finset.univ.image lab).card := by
  classical
  let S := Finset.univ.image lab
  calc
    (∏ a : alpha, if a ∈ S then theta else 1) = ∏ _a ∈ S, theta := by
      rw [Finset.prod_ite]
      simp
    _ = theta ^ S.card := by simp

private theorem centeredBernoulliMomentBound
    (theta : ℝ) (b : ℕ) (hzero : 0 < theta)
    (hone : theta ≤ 1 / 2) (hb : 2 ≤ b) :
    |theta * (1 - theta) ^ b + (1 - theta) * (-theta) ^ b| ≤ theta := by
  have htheta : 0 ≤ theta := hzero.le
  have hthetale : theta ≤ 1 := by linarith
  have honeneg : 0 ≤ 1 - theta := by linarith
  have honele : 1 - theta ≤ 1 := by linarith
  have hptheta : theta ^ b ≤ theta ^ 2 :=
    pow_le_pow_of_le_one htheta hthetale hb
  have hpone : (1 - theta) ^ b ≤ (1 - theta) ^ 2 :=
    pow_le_pow_of_le_one honeneg honele hb
  calc
    |theta * (1 - theta) ^ b + (1 - theta) * (-theta) ^ b| ≤
        |theta * (1 - theta) ^ b| +
          |(1 - theta) * (-theta) ^ b| := abs_add_le _ _
    _ = theta * (1 - theta) ^ b + (1 - theta) * theta ^ b := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      simp only [abs_of_nonneg htheta, abs_of_nonneg honeneg, abs_neg]
    _ ≤ theta * (1 - theta) ^ 2 + (1 - theta) * theta ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpone htheta)
        (mul_le_mul_of_nonneg_left hptheta honeneg)
    _ = theta * (1 - theta) := by ring
    _ ≤ theta := by nlinarith

private theorem selectorMoment_abs_le
    {iota alpha : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype alpha] [DecidableEq alpha]
    (theta : ℝ) (hzero : 0 < theta) (hone : theta ≤ 1 / 2)
    (P : Finpartition (Finset.univ : Finset iota))
    (lab : InjectivePartitionLabeling P alpha)
    (hnonsingleton : ∀ B ∈ P.parts, 2 ≤ B.card) :
    |selectorMoment theta (labelOfPartition P lab.1)| ≤
      theta ^ P.parts.card := by
  classical
  rw [selectorMoment_eq_product_coordinate,
    Finset.abs_prod Finset.univ
      (selectorCoordinateFactor theta (labelOfPartition P lab.1))]
  calc
    (∏ a, |selectorCoordinateFactor theta
        (labelOfPartition P lab.1) a|) ≤
        ∏ a, if a ∈ Finset.univ.image lab.1 then theta else 1 := by
      apply Finset.prod_le_prod
      · intro a _
        exact abs_nonneg _
      · intro a _
        by_cases ha : a ∈ Finset.univ.image lab.1
        · rw [if_pos ha]
          obtain ⟨B, _, hBa⟩ := Finset.mem_image.mp ha
          subst a
          rw [selectorCoordinateFactor_of_block theta P lab B]
          exact centeredBernoulliMomentBound theta B.1.card
            hzero hone (hnonsingleton B.1 B.2)
        · rw [if_neg ha, selectorCoordinateFactor_of_unused theta P lab a ha,
            abs_one]
    _ = theta ^ (Finset.univ.image lab.1).card :=
      product_indicator_eq_pow_card_image theta lab.1
    _ = theta ^ P.parts.card := by
      congr 1
      rw [Finset.card_image_of_injective Finset.univ lab.2,
        Finset.card_univ]
      simp [PartitionBlock]

private abbrev SurvivingSelectorPartition (p : ℕ) :=
  {P : Finpartition (Finset.univ : Finset (Fin (2 * p))) //
    ∀ B ∈ P.parts, 2 ≤ B.card}

private abbrev BoundedSelectorData (p : ℕ) :=
  Σ s : Fin p, Σ t : Fin (p + 1), SelectorEqualityData p s.1 t.1

private theorem survivingSelector_parts_card_le
    {p : ℕ} (P : SurvivingSelectorPartition p) :
    P.1.parts.card ≤ p := by
  have hsumle :
      (∑ _B ∈ P.1.parts, 2) ≤ ∑ B ∈ P.1.parts, B.card := by
    apply Finset.sum_le_sum
    intro B hB
    exact P.2 B hB
  rw [P.1.sum_card_parts] at hsumle
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hsumle
  apply Nat.le_of_mul_le_mul_right (c := 2) (hc := by omega)
  simpa only [Nat.cast_id, Nat.mul_comm] using hsumle

private theorem survivingSelector_parts_card_pos
    {p : ℕ} (hp : 1 ≤ p) (P : SurvivingSelectorPartition p) :
    0 < P.1.parts.card := by
  apply Finset.card_pos.mpr
  apply P.1.parts_nonempty
  exact Finset.ne_empty_of_mem
    (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))

private theorem survivingSelector_odd_card_le
    {p : ℕ} (P : SurvivingSelectorPartition p) :
    (equalityOddIncidentVertices P.1).card ≤ p := by
  calc
    (equalityOddIncidentVertices P.1).card ≤ P.1.parts.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ p := survivingSelector_parts_card_le P

private noncomputable def boundedSelectorDataOf
    {p : ℕ} (hp : 1 ≤ p) (P : SurvivingSelectorPartition p) :
    BoundedSelectorData p := by
  let s := p - P.1.parts.card
  let t := (equalityOddIncidentVertices P.1).card
  have hpartsle := survivingSelector_parts_card_le P
  have hpartspos := survivingSelector_parts_card_pos hp P
  have hslt : s < p := by omega
  have htlt : t < p + 1 := by
    exact Nat.lt_succ_of_le (survivingSelector_odd_card_le P)
  refine ⟨⟨s, hslt⟩, ⟨⟨t, htlt⟩, ⟨P.1, P.2, ?_, rfl⟩⟩⟩
  dsimp only [s]
  omega

private def survivingSelectorPartitionOf
    {p : ℕ} (D : BoundedSelectorData p) :
    SurvivingSelectorPartition p :=
  ⟨D.2.2.1, D.2.2.2.1⟩

private theorem boundedSelectorDataOf_left_inv
    {p : ℕ} (hp : 1 ≤ p) :
    Function.LeftInverse survivingSelectorPartitionOf
      (@boundedSelectorDataOf p hp) := by
  intro P
  apply Subtype.ext
  rfl

private theorem boundedSelectorDataOf_injective
    {p : ℕ} (hp : 1 ≤ p) :
    Function.Injective (@boundedSelectorDataOf p hp) :=
  (boundedSelectorDataOf_left_inv hp).injective

private theorem fintype_sum_le_sum_of_injective
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq beta]
    (f : alpha → beta) (hf : Function.Injective f)
    (g : alpha → ℝ) (G : beta → ℝ)
    (hg : ∀ a, g a ≤ G (f a)) (hG : ∀ b, 0 ≤ G b) :
    (∑ a, g a) ≤ ∑ b, G b := by
  calc
    (∑ a, g a) ≤ ∑ a, G (f a) := by
      apply Finset.sum_le_sum
      intro a _
      exact hg a
    _ = ∑ b ∈ Finset.univ.image f, G b := by
      rw [Finset.sum_image]
      exact hf.injOn
    _ ≤ ∑ b ∈ (Finset.univ : Finset beta), G b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr fun _ _ ↦ Finset.mem_univ _
      · intro b _ _
        exact hG b
    _ = ∑ b, G b := rfl

private def xorKernelBitsEquiv
    {rho nu : Type*} [Fintype rho] [Fintype nu]
    [DecidableEq rho] [DecidableEq nu]
    (m : ℕ) (A : Matrix rho nu (ZMod 2)) :
    {x : nu → WalshIndex m //
      ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} ≃
      (Fin m → LinearMap.ker A.mulVecLin) where
  toFun x bit := ⟨fun j ↦ x.1 j bit, by simpa using x.2 bit⟩
  invFun y := ⟨fun j bit ↦ (y bit).1 j, fun bit ↦ by
    change A.mulVecLin (y bit).1 = 0
    exact (y bit).2⟩
  left_inv x := by
    apply Subtype.ext
    funext j bit
    rfl
  right_inv y := by
    funext bit
    apply Subtype.ext
    funext j
    rfl

theorem xorKernelSolutionCount
    {rho nu : Type*} [Fintype rho] [Fintype nu]
    [DecidableEq rho] [DecidableEq nu]
    (m : ℕ) (A : Matrix rho nu (ZMod 2)) :
    Fintype.card {x : nu → WalshIndex m //
      ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} =
      walshCard m ^ (Fintype.card nu - Matrix.rank A) := by
  classical
  letI : Fintype (LinearMap.ker A.mulVecLin) := Fintype.ofFinite _
  have hnull := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdomain : Module.finrank (ZMod 2) (nu → ZMod 2) = Fintype.card nu := by
    simpa using Module.finrank_fintype_fun_eq_card
      (R := ZMod 2) (M := ZMod 2) (K := ZMod 2) (V := nu → ZMod 2)
  have hker : Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
      Fintype.card nu - Matrix.rank A := by
    rw [hdomain] at hnull
    change Matrix.rank A +
      Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
        Fintype.card nu at hnull
    omega
  calc
    Fintype.card {x : nu → WalshIndex m //
        ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} =
      Fintype.card (Fin m → LinearMap.ker A.mulVecLin) :=
      Fintype.card_congr (xorKernelBitsEquiv m A)
    _ = Fintype.card (LinearMap.ker A.mulVecLin) ^ m := by simp
    _ = (2 ^ (Fintype.card nu - Matrix.rank A)) ^ m := by
      rw [Module.card_eq_pow_finrank
        (K := ZMod 2) (V := LinearMap.ker A.mulVecLin), hker]
      norm_num
    _ = (2 ^ m) ^ (Fintype.card nu - Matrix.rank A) := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    _ = walshCard m ^ (Fintype.card nu - Matrix.rank A) := by
      simp [walshCard, WalshIndex]

theorem entryConstraintMatrix_mulVec_apply
    {p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (x : EqualityVertex D.selector.1 → ZMod 2) (B : EntryBlock D) :
    (entryConstraintMatrix D).mulVec x B =
      ∑ e ∈ B.1,
        (x (equalityVertexAt D.selector.1 e) +
          x (equalityVertexAt D.selector.1 (cyclicSucc e))) := by
  classical
  simp only [Matrix.mulVec, dotProduct, entryConstraintMatrix]
  calc
    (∑ i, (∑ e ∈ B.1,
        ((if equalityVertexAt D.selector.1 e = i then 1 else 0) +
          if equalityVertexAt D.selector.1 (cyclicSucc e) = i then 1 else 0)) *
        x i) =
      ∑ i, ∑ e ∈ B.1,
        (((if equalityVertexAt D.selector.1 e = i then 1 else 0) +
          if equalityVertexAt D.selector.1 (cyclicSucc e) = i then 1 else 0) *
          x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ e ∈ B.1, ∑ i,
        (((if equalityVertexAt D.selector.1 e = i then 1 else 0) +
          if equalityVertexAt D.selector.1 (cyclicSucc e) = i then 1 else 0) *
          x i) := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      calc
        (∑ i,
            ((if equalityVertexAt D.selector.1 e = i then 1 else 0) +
              if equalityVertexAt D.selector.1 (cyclicSucc e) = i then 1 else 0) *
              x i) =
          ∑ i,
            ((if equalityVertexAt D.selector.1 e = i then 1 else 0) * x i +
              (if equalityVertexAt D.selector.1 (cyclicSucc e) = i then 1 else 0) *
                x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = (∑ i, (if equalityVertexAt D.selector.1 e = i then 1 else 0) * x i) +
            ∑ i, (if equalityVertexAt D.selector.1 (cyclicSucc e) = i then 1 else 0) *
              x i := Finset.sum_add_distrib
        _ = _ := by simp

private abbrev EntryXorConstraints
    {p s t m : ℕ} (D : EntryCumulantPartitionData p s t)
    (lab : EqualityVertex D.selector.1 → WalshIndex m) : Prop :=
  ∀ B ∈ D.entry.parts,
    (∑ e ∈ B,
      (lab (equalityVertexAt D.selector.1 e) +
        lab (equalityVertexAt D.selector.1 (cyclicSucc e)))) = 0

private theorem entryXorConstraints_iff_matrixKernel
    {p s t m : ℕ} (D : EntryCumulantPartitionData p s t)
    (lab : EqualityVertex D.selector.1 → WalshIndex m) :
    EntryXorConstraints D lab ↔
      ∀ bit,
        (entryConstraintMatrix D).mulVec (fun u ↦ lab u bit) = 0 := by
  constructor
  · intro h bit
    funext B
    rw [entryConstraintMatrix_mulVec_apply]
    have hB := h B.1 B.2
    change (∑ e ∈ B.1,
      (lab (equalityVertexAt D.selector.1 e) bit +
        lab (equalityVertexAt D.selector.1 (cyclicSucc e)) bit)) = 0
    simpa only [Finset.sum_apply, Pi.add_apply, Pi.zero_apply] using
      congrFun hB bit
  · intro h B hB
    funext bit
    have hrow := congrFun (h bit) (⟨B, hB⟩ : EntryBlock D)
    rw [entryConstraintMatrix_mulVec_apply] at hrow
    simpa only [Finset.sum_apply, Pi.add_apply, Pi.zero_apply] using hrow

theorem entryXorConstraintSolutionCount
    {p s t m : ℕ} (D : EntryCumulantPartitionData p s t) :
    Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
      EntryXorConstraints D lab} =
      walshCard m ^
        (D.selector.1.parts.card - Matrix.rank (entryConstraintMatrix D)) := by
  classical
  calc
    Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
        EntryXorConstraints D lab} =
      Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
        ∀ bit, (entryConstraintMatrix D).mulVec
          (fun u ↦ lab u bit) = 0} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight fun lab ↦
          entryXorConstraints_iff_matrixKernel D lab
    _ = walshCard m ^
        (Fintype.card (EqualityVertex D.selector.1) -
          Matrix.rank (entryConstraintMatrix D)) :=
      xorKernelSolutionCount m (entryConstraintMatrix D)
    _ = walshCard m ^
        (D.selector.1.parts.card - Matrix.rank (entryConstraintMatrix D)) := by
      congr 2
      simp [EqualityVertex]

private def entryCumulantProduct
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (x : Fin q → WalshIndex m)
    (P : Finpartition (Finset.univ : Finset (Fin q))) : ℝ :=
  ∏ B ∈ P.parts,
    jointCumulantOn (fun e : B ↦
      centeredRandomProjectionEntry V
        (x e.1) (x (cyclicSucc e.1)))

private theorem cyclicBlockXorSum_eq_finsetSum
    {m q : ℕ} (x : Fin q → WalshIndex m) (B : Finset (Fin q)) :
    (∑ f : Fin B.card,
      (cyclicBlockSourceLabels x B f + cyclicBlockTargetLabels x B f)) =
      ∑ e ∈ B, (x e + x (cyclicSucc e)) := by
  classical
  let e : Fin B.card ≃ B :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
  calc
    (∑ f : Fin B.card,
        (cyclicBlockSourceLabels x B f + cyclicBlockTargetLabels x B f)) =
        ∑ z : B, (x z.1 + x (cyclicSucc z.1)) := by
      apply Fintype.sum_equiv e
      intro f
      rfl
    _ = ∑ z ∈ B, (x z + x (cyclicSucc z)) := by
      rw [Finset.sum_subtype B (fun _ ↦ Iff.rfl)]

private theorem entryCumulantProduct_eq_zero_of_singleton
    {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (x : Fin q → WalshIndex m)
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : Finset (Fin q)) (hBP : B ∈ P.parts) (hB : B.card = 1) :
    entryCumulantProduct V x P = 0 := by
  unfold entryCumulantProduct
  apply Finset.prod_eq_zero hBP
  exact centeredProjection_blockCumulant_eq_zero_of_card_one V hV x B hB

private theorem entryXorConstraints_of_entryCumulantProduct_ne_zero
    (hgraph : GraphRankContractionPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (Q : SelectorEqualityData p s t)
    (lab : InjectivePartitionLabeling Q.1 (WalshIndex m))
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hnonsingleton : ∀ B ∈ P.parts, 2 ≤ B.card)
    (hne : entryCumulantProduct V (labelOfPartition Q.1 lab.1) P ≠ 0) :
    EntryXorConstraints (entryPartitionData Q P) lab.1 := by
  intro B hBP
  by_contra hxor
  apply hne
  have hxor' :
      (∑ f : Fin B.card,
        (cyclicBlockSourceLabels (labelOfPartition Q.1 lab.1) B f +
          cyclicBlockTargetLabels (labelOfPartition Q.1 lab.1) B f)) ≠ 0 := by
    rw [cyclicBlockXorSum_eq_finsetSum]
    change (∑ e ∈ B,
      (lab.1 (equalityVertexAt Q.1 e) +
        lab.1 (equalityVertexAt Q.1 (cyclicSucc e)))) ≠ 0 at hxor
    simpa only [labelOfPartition, partitionVertexAt, equalityVertexAt] using hxor
  exact centeredProjection_partitionCumulantProduct_eq_zero_of_block_xor
    hgraph V hV (labelOfPartition Q.1 lab.1) P B hBP
      (hnonsingleton B hBP) hxor'

private theorem sum_injective_labels_abs_entryCumulantProduct_le
    (hgraph : GraphRankContractionPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (Q : SelectorEqualityData p s t)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hnonsingleton : ∀ B ∈ P.parts, 2 ≤ B.card) :
    (∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
      |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) ≤
      (walshCard m : ℝ) ^
          (Q.1.parts.card -
            Matrix.rank (entryConstraintMatrix (entryPartitionData Q P))) *
        ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
        (entryPartitionCumulantConstant P : ℝ) *
        (r : ℝ) ^ P.parts.card := by
  classical
  let D : EntryCumulantPartitionData p s t := entryPartitionData Q P
  let C : ℝ :=
    ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
      (entryPartitionCumulantConstant P : ℝ) *
      (r : ℝ) ^ P.parts.card
  let includeLabel : InjectivePartitionLabeling Q.1 (WalshIndex m) →
      EqualityVertex D.selector.1 → WalshIndex m := fun lab ↦ lab.1
  have hinjective : Function.Injective includeLabel := by
    intro lab₁ lab₂ h
    exact Subtype.ext h
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  calc
    (∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
        |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) ≤
        ∑ lab : EqualityVertex D.selector.1 → WalshIndex m,
          if EntryXorConstraints D lab then C else 0 := by
      apply fintype_sum_le_sum_of_injective includeLabel hinjective
      · intro lab
        by_cases hxor : EntryXorConstraints D (includeLabel lab)
        · rw [if_pos hxor]
          exact centeredProjection_partitionCumulantProduct_bound
            hgraph V hV (labelOfPartition Q.1 lab.1) P hnonsingleton
        · rw [if_neg hxor]
          have hzero :
              entryCumulantProduct V (labelOfPartition Q.1 lab.1) P = 0 := by
            by_contra hne
            exact hxor
              (by simpa only [D, includeLabel, entryPartitionData] using
                (entryXorConstraints_of_entryCumulantProduct_ne_zero
                  hgraph V hV Q lab P hnonsingleton hne))
          rw [hzero, abs_zero]
      · intro lab
        split <;> positivity
    _ = (Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
          EntryXorConstraints D lab} : ℝ) * C := by
      change (∑ lab : EqualityVertex D.selector.1 → WalshIndex m,
        if EntryXorConstraints D lab then C else 0) = _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Fintype.card_subtype]
    _ = (walshCard m : ℝ) ^
          (Q.1.parts.card -
            Matrix.rank (entryConstraintMatrix (entryPartitionData Q P))) *
        ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
        (entryPartitionCumulantConstant P : ℝ) *
        (r : ℝ) ^ P.parts.card := by
      rw [entryXorConstraintSolutionCount]
      simp only [Nat.cast_pow]
      dsimp only [C, D]
      have hselectorParts :
          (entryPartitionData Q P).selector.1.parts.card = Q.1.parts.card := rfl
      rw [hselectorParts]
      ring

private theorem partition_parts_card_le_half
    {p : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hnonsingleton : ∀ B ∈ P.parts, 2 ≤ B.card) :
    P.parts.card ≤ p := by
  have hsumle :
      (∑ _B ∈ P.parts, 2) ≤ ∑ B ∈ P.parts, B.card := by
    apply Finset.sum_le_sum
    intro B hB
    exact hnonsingleton B hB
  rw [P.sum_card_parts] at hsumle
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hsumle
  apply Nat.le_of_mul_le_mul_right (c := 2) (hc := by omega)
  simpa only [Nat.cast_id, Nat.mul_comm] using hsumle

private theorem partition_parts_card_pos
    {p : ℕ} (hp : 1 ≤ p)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) :
    0 < P.parts.card := by
  apply Finset.card_pos.mpr
  apply P.parts_nonempty
  exact Finset.ne_empty_of_mem
    (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))

private theorem exists_singleton_part_of_not_nonsingleton
    {p : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hnot : ¬ ∀ B ∈ P.parts, 2 ≤ B.card) :
    ∃ B ∈ P.parts, B.card = 1 := by
  push_neg at hnot
  obtain ⟨B, hBP, hBlt⟩ := hnot
  have hBpos : 0 < B.card :=
    Finset.card_pos.mpr (P.nonempty_of_mem_parts hBP)
  exact ⟨B, hBP, by omega⟩

private abbrev SurvivingAdmissibleEntryPartition
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :=
  {P : Finpartition (Finset.univ : Finset (Fin (2 * p))) //
    (∀ B ∈ P.parts, 2 ≤ B.card) ∧
      AdmissibleEntryPairBlocks (entryPartitionData Q P)}

private abbrev BoundedAggregateData
    {p s t : ℕ} (Q : SelectorEqualityData p s t) :=
  Σ d : Fin p, Σ h : Fin (p - s + 1), AggregateEntryPartition Q d.1 h.1

private noncomputable def boundedAggregateDataOf
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t)
    (A : SurvivingAdmissibleEntryPartition Q) :
    BoundedAggregateData Q := by
  let d := p - A.1.parts.card
  let D := entryPartitionData Q A.1
  let h := Matrix.rank (entryConstraintMatrix D)
  have hpartsle : A.1.parts.card ≤ p :=
    partition_parts_card_le_half A.1 A.2.1
  have hpartspos : 0 < A.1.parts.card :=
    partition_parts_card_pos hp A.1
  have hdlt : d < p := by
    dsimp only [d]
    omega
  have hrankle : h ≤ Q.1.parts.card := by
    dsimp only [h]
    calc
      Matrix.rank (entryConstraintMatrix D) ≤
          Fintype.card (EqualityVertex D.selector.1) :=
        Matrix.rank_le_card_width (entryConstraintMatrix D)
      _ = Q.1.parts.card := by
        dsimp only [D, entryPartitionData, EqualityVertex]
        exact Fintype.card_coe Q.1.parts
  have hQpartsle : Q.1.parts.card ≤ p := by
    rw [Q.2.2.1]
    omega
  have hhlt : h < p - s + 1 := by
    apply Nat.lt_succ_of_le
    simpa only [Q.2.2.1] using hrankle
  refine ⟨⟨d, hdlt⟩, ⟨⟨h, hhlt⟩, ⟨A.1, A.2.1, A.2.2, ?_, ?_⟩⟩⟩
  · dsimp only [d]
    omega
  · rfl

private def survivingAdmissibleEntryPartitionOf
    {p s t : ℕ} {Q : SelectorEqualityData p s t}
    (D : BoundedAggregateData Q) :
    SurvivingAdmissibleEntryPartition Q :=
  ⟨D.2.2.1, D.2.2.2.1, D.2.2.2.2.1⟩

private theorem boundedAggregateDataOf_left_inv
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t) :
    Function.LeftInverse survivingAdmissibleEntryPartitionOf
      (boundedAggregateDataOf hp Q) := by
  intro A
  apply Subtype.ext
  rfl

private theorem boundedAggregateDataOf_injective
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t) :
    Function.Injective (boundedAggregateDataOf hp Q) :=
  (boundedAggregateDataOf_left_inv hp Q).injective

@[simp] private theorem boundedAggregateDataOf_d
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t)
    (A : SurvivingAdmissibleEntryPartition Q) :
    (boundedAggregateDataOf hp Q A).1.1 = p - A.1.parts.card := rfl

@[simp] private theorem boundedAggregateDataOf_h
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t)
    (A : SurvivingAdmissibleEntryPartition Q) :
    (boundedAggregateDataOf hp Q A).2.1.1 =
      Matrix.rank (entryConstraintMatrix (entryPartitionData Q A.1)) := rfl

@[simp] private theorem boundedAggregateDataOf_partition
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t)
    (A : SurvivingAdmissibleEntryPartition Q) :
    (boundedAggregateDataOf hp Q A).2.2.1 = A.1 := rfl

private theorem entryCumulantProduct_eq_zero_of_not_surviving_admissible
    (hgraph : GraphRankContractionPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (Q : SelectorEqualityData p s t)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hbad : ¬ ((∀ B ∈ P.parts, 2 ≤ B.card) ∧
      AdmissibleEntryPairBlocks (entryPartitionData Q P)))
    (lab : InjectivePartitionLabeling Q.1 (WalshIndex m)) :
    entryCumulantProduct V (labelOfPartition Q.1 lab.1) P = 0 := by
  classical
  by_cases hnonsingleton : ∀ B ∈ P.parts, 2 ≤ B.card
  · have hnotadmissible :
        ¬ AdmissibleEntryPairBlocks (entryPartitionData Q P) := by
      intro h
      exact hbad ⟨hnonsingleton, h⟩
    by_contra hne
    apply hnotadmissible
    apply pointwise_vanishing_pair_blocks_admissible m p s t
      (entryPartitionData Q P) lab.1 lab.2
    intro B hBP _hcard
    exact entryXorConstraints_of_entryCumulantProduct_ne_zero
      hgraph V hV Q lab P hnonsingleton hne B hBP
  · obtain ⟨B, hBP, hB⟩ :=
      exists_singleton_part_of_not_nonsingleton P hnonsingleton
    exact entryCumulantProduct_eq_zero_of_singleton V hV
      (labelOfPartition Q.1 lab.1) P B hBP hB

private noncomputable def entryPartitionReindex
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) :
    (Finpartition (Finset.univ : Finset (Fin (2 * p)))) ⊕
      BoundedAggregateData Q := by
  classical
  exact if hgood :
        ((∀ B ∈ P.parts, 2 ≤ B.card) ∧
          AdmissibleEntryPairBlocks (entryPartitionData Q P))
    then Sum.inr (boundedAggregateDataOf hp Q ⟨P, hgood⟩)
    else Sum.inl P

private theorem entryPartitionReindex_injective
    {p s t : ℕ} (hp : 1 ≤ p) (Q : SelectorEqualityData p s t) :
    Function.Injective (entryPartitionReindex hp Q) := by
  classical
  intro P R hPR
  by_cases hP :
      (∀ B ∈ P.parts, 2 ≤ B.card) ∧
        AdmissibleEntryPairBlocks (entryPartitionData Q P)
  · by_cases hR :
        (∀ B ∈ R.parts, 2 ≤ B.card) ∧
          AdmissibleEntryPairBlocks (entryPartitionData Q R)
    · simp only [entryPartitionReindex, dif_pos hP, dif_pos hR] at hPR
      have hdata : boundedAggregateDataOf hp Q ⟨P, hP⟩ =
          boundedAggregateDataOf hp Q ⟨R, hR⟩ := Sum.inr.inj hPR
      have hsub : (⟨P, hP⟩ : SurvivingAdmissibleEntryPartition Q) =
          ⟨R, hR⟩ := boundedAggregateDataOf_injective hp Q hdata
      exact congrArg Subtype.val hsub
    · simp only [entryPartitionReindex, dif_pos hP, dif_neg hR] at hPR
      exact (Sum.inr_ne_inl hPR).elim
  · by_cases hR :
        (∀ B ∈ R.parts, 2 ≤ B.card) ∧
          AdmissibleEntryPairBlocks (entryPartitionData Q R)
    · simp only [entryPartitionReindex, dif_neg hP, dif_pos hR] at hPR
      exact (Sum.inl_ne_inr hPR).elim
    · simp only [entryPartitionReindex, dif_neg hP, dif_neg hR] at hPR
      exact Sum.inl.inj hPR

private def aggregateTargetWeight
    {m r p s t : ℕ} (Q : SelectorEqualityData p s t) :
    (Finpartition (Finset.univ : Finset (Fin (2 * p))) ⊕
      BoundedAggregateData Q) → ℝ
  | Sum.inl _ => 0
  | Sum.inr D =>
      (walshCard m : ℝ) ^ (Q.1.parts.card - D.2.1.1) *
        ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
        (entryPartitionCumulantConstant D.2.2.1 : ℝ) *
        (r : ℝ) ^ (p - D.1.1)

private theorem sum_entryPartitions_injectiveLabels_abs_le
    (hgraph : GraphRankContractionPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (hp : 1 ≤ p) (Q : SelectorEqualityData p s t) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
      ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
        |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) ≤
      ∑ d : Fin p, ∑ h : Fin (p - s + 1),
        (walshCard m : ℝ) ^ (p - s - h.1) *
          ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
          (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) *
          (r : ℝ) ^ (p - d.1) := by
  classical
  let sourceWeight :
      Finpartition (Finset.univ : Finset (Fin (2 * p))) → ℝ := fun P ↦
    ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
      |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|
  have htarget_nonneg : ∀ D, 0 ≤ aggregateTargetWeight (m := m) (r := r) Q D := by
    intro D
    rcases D with P | D
    · rfl
    · simp only [aggregateTargetWeight]
      positivity
  have hpointwise : ∀ P,
      sourceWeight P ≤
        aggregateTargetWeight (m := m) (r := r) Q
          (entryPartitionReindex hp Q P) := by
    intro P
    by_cases hgood :
        (∀ B ∈ P.parts, 2 ≤ B.card) ∧
          AdmissibleEntryPairBlocks (entryPartitionData Q P)
    · have hbound := sum_injective_labels_abs_entryCumulantProduct_le
        hgraph V hV Q P hgood.1
      have hreindex : entryPartitionReindex hp Q P =
          Sum.inr (boundedAggregateDataOf hp Q
            (⟨P, hgood⟩ : SurvivingAdmissibleEntryPartition Q)) := by
        simp only [entryPartitionReindex, dif_pos hgood]
      rw [hreindex]
      simp only [sourceWeight, aggregateTargetWeight,
        boundedAggregateDataOf_d, boundedAggregateDataOf_h,
        boundedAggregateDataOf_partition]
      have hpartsle : P.parts.card ≤ p :=
        partition_parts_card_le_half P hgood.1
      have hsub : p - (p - P.parts.card) = P.parts.card := by omega
      rw [hsub]
      exact hbound
    · have hzero : sourceWeight P = 0 := by
        unfold sourceWeight
        apply Finset.sum_eq_zero
        intro lab _
        rw [entryCumulantProduct_eq_zero_of_not_surviving_admissible
          hgraph V hV Q P hgood lab, abs_zero]
      rw [hzero]
      exact htarget_nonneg _
  calc
    (∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
        ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
          |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) =
        ∑ P, sourceWeight P := rfl
    _ ≤ ∑ D,
        aggregateTargetWeight (m := m) (r := r) Q D := by
      exact fintype_sum_le_sum_of_injective
        (entryPartitionReindex hp Q)
        (entryPartitionReindex_injective hp Q)
        sourceWeight
        (aggregateTargetWeight (m := m) (r := r) Q)
        hpointwise htarget_nonneg
    _ = ∑ D : BoundedAggregateData Q,
        (walshCard m : ℝ) ^ (Q.1.parts.card - D.2.1.1) *
          ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
          (entryPartitionCumulantConstant D.2.2.1 : ℝ) *
          (r : ℝ) ^ (p - D.1.1) := by
      rw [Fintype.sum_sum_type]
      simp [aggregateTargetWeight]
    _ = ∑ d : Fin p, ∑ h : Fin (p - s + 1),
        (walshCard m : ℝ) ^ (Q.1.parts.card - h.1) *
          ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
          (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) *
          (r : ℝ) ^ (p - d.1) := by
      simp_rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro h _
      have hcast :
          (∑ A : AggregateEntryPartition Q d.1 h.1,
              (entryPartitionCumulantConstant A.1 : ℝ)) =
            (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) := by
        unfold aggregateEntryPartitionCumulantSum
        norm_cast
      calc
        (∑ A : AggregateEntryPartition Q d.1 h.1,
            (walshCard m : ℝ) ^ (Q.1.parts.card - h.1) *
              ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
              (entryPartitionCumulantConstant A.1 : ℝ) *
              (r : ℝ) ^ (p - d.1)) =
            ((walshCard m : ℝ) ^ (Q.1.parts.card - h.1) *
              ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
              (r : ℝ) ^ (p - d.1)) *
              ∑ A : AggregateEntryPartition Q d.1 h.1,
                (entryPartitionCumulantConstant A.1 : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A _
          ring
        _ = _ := by rw [hcast]; ring
    _ = _ := by rw [Q.2.2.1]

private theorem selectorEntryContribution_abs_sum_le
    (hgraph : GraphRankContractionPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hp : 1 ≤ p) (Q : SelectorEqualityData p s t) :
    (∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
      |selectorMoment θ (labelOfPartition Q.1 lab.1) *
        ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
          entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) ≤
      θ ^ (p - s) *
        ∑ d : Fin p, ∑ h : Fin (p - s + 1),
          (walshCard m : ℝ) ^ (p - s - h.1) *
            ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
            (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) *
            (r : ℝ) ^ (p - d.1) := by
  classical
  let entrySum : InjectivePartitionLabeling Q.1 (WalshIndex m) → ℝ :=
    fun lab ↦
      ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
        entryCumulantProduct V (labelOfPartition Q.1 lab.1) P
  let entryAbsSum : InjectivePartitionLabeling Q.1 (WalshIndex m) → ℝ :=
    fun lab ↦
      ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
        |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|
  have hpointwise : ∀ lab,
      |selectorMoment θ (labelOfPartition Q.1 lab.1) * entrySum lab| ≤
        θ ^ (p - s) * entryAbsSum lab := by
    intro lab
    rw [abs_mul]
    have hselector := selectorMoment_abs_le θ hθ₀ hθ₁ Q.1 lab Q.2.1
    rw [Q.2.2.1] at hselector
    have hentry : |entrySum lab| ≤ entryAbsSum lab := by
      exact Finset.abs_sum_le_sum_abs _ _
    exact mul_le_mul hselector hentry (abs_nonneg _)
      (pow_nonneg hθ₀.le _)
  calc
    (∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
        |selectorMoment θ (labelOfPartition Q.1 lab.1) *
          ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) =
        ∑ lab,
          |selectorMoment θ (labelOfPartition Q.1 lab.1) * entrySum lab| := rfl
    _ ≤ ∑ lab, θ ^ (p - s) * entryAbsSum lab := by
      apply Finset.sum_le_sum
      intro lab _
      exact hpointwise lab
    _ = θ ^ (p - s) *
        ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
          ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
            |entryCumulantProduct V (labelOfPartition Q.1 lab.1) P| := by
      unfold entryAbsSum
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ θ ^ (p - s) *
        ∑ d : Fin p, ∑ h : Fin (p - s + 1),
          (walshCard m : ℝ) ^ (p - s - h.1) *
            ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
            (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) *
            (r : ℝ) ^ (p - d.1) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_entryPartitions_injectiveLabels_abs_le
          hgraph V hV hp Q
      · exact pow_nonneg hθ₀.le _

private theorem exact_dimension_factor
    (n r p s d h : ℕ) (θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hθ : 0 < θ)
    (hd : d ≤ p) (hsh : s + h ≤ p) :
    θ ^ (p - s) * (r : ℝ) ^ (p - d) *
        (n : ℝ) ^ (-(2 * p : ℤ)) * (n : ℝ) ^ (p - s - h) =
      (((r : ℝ) / n) * θ) ^ p *
        ((n : ℝ) * θ) ^ (-(s : ℤ)) *
        (r : ℝ) ^ (-(d : ℤ)) *
        (n : ℝ) ^ (-(h : ℤ)) := by
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

private theorem exact_dimension_factor_inv
    (n r p s d h : ℕ) (θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hθ : 0 < θ)
    (hd : d ≤ p) (hsh : s + h ≤ p) :
    θ ^ (p - s) * (n : ℝ) ^ (p - s - h) *
        ((n : ℝ)⁻¹) ^ (2 * p) * (r : ℝ) ^ (p - d) =
      (((r : ℝ) / n) * θ) ^ p *
        ((n : ℝ) * θ) ^ (-(s : ℤ)) *
        (r : ℝ) ^ (-(d : ℤ)) *
        (n : ℝ) ^ (-(h : ℤ)) := by
  calc
    θ ^ (p - s) * (n : ℝ) ^ (p - s - h) *
        ((n : ℝ)⁻¹) ^ (2 * p) * (r : ℝ) ^ (p - d) =
      θ ^ (p - s) * (r : ℝ) ^ (p - d) *
        (n : ℝ) ^ (-(2 * p : ℤ)) * (n : ℝ) ^ (p - s - h) := by
      have htwop : (2 : ℤ) * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by norm_num
      have hpow : ((n : ℝ)⁻¹) ^ (2 * p) =
          (n : ℝ) ^ (-(2 * p : ℤ)) := by
        rw [htwop, zpow_neg, zpow_natCast, inv_pow]
      rw [hpow]
      ring
    _ = _ := exact_dimension_factor n r p s d h θ hn hr hθ hd hsh

private theorem selectorEntryContribution_abs_sum_le_aggregateBound
    (hgraph : GraphRankContractionPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hp : 2 ≤ p) (hr₀ : 0 < r) (Q : SelectorEqualityData p s t) :
    (∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
      |selectorMoment θ (labelOfPartition Q.1 lab.1) *
        ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
          entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) ≤
      ((3 * K₂ : ℕ) : ℝ) ^ p *
        (((r : ℝ) / walshCard m) * θ) ^ p *
        ∑ d : Fin p, ∑ h : Fin (p - s + 1),
          if t ≤ 12 * d.1 + 4 * h.1 then
            ((4 * p + 1 : ℕ) : ℝ) ^
                (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) *
              (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
                (r : ℝ) ^ (-(d.1 : ℤ)) *
                (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
          else 0 := by
  classical
  have hn₀ : 0 < walshCard m := Fintype.card_pos
  have hs : s ≤ p := by
    have hpartspos : 0 < Q.1.parts.card :=
      partition_parts_card_pos (by omega) Q.1
    rw [Q.2.2.1] at hpartspos
    omega
  have hpre := selectorEntryContribution_abs_sum_le
    hgraph V hV θ hθ₀ hθ₁ (by omega) Q
  calc
    (∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
        |selectorMoment θ (labelOfPartition Q.1 lab.1) *
          ∑ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            entryCumulantProduct V (labelOfPartition Q.1 lab.1) P|) ≤
      θ ^ (p - s) *
        ∑ d : Fin p, ∑ h : Fin (p - s + 1),
          (walshCard m : ℝ) ^ (p - s - h.1) *
            ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
            (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) *
            (r : ℝ) ^ (p - d.1) := hpre
    _ ≤ ∑ d : Fin p, ∑ h : Fin (p - s + 1),
        ((3 * K₂ : ℕ) : ℝ) ^ p *
          (((r : ℝ) / walshCard m) * θ) ^ p *
          (if t ≤ 12 * d.1 + 4 * h.1 then
            ((4 * p + 1 : ℕ) : ℝ) ^
                (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) *
              (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
                (r : ℝ) ^ (-(d.1 : ℤ)) *
                (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
          else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro h _
      have hd : d.1 ≤ p - 1 := by omega
      have hsh : s + h.1 ≤ p := by omega
      by_cases ht : t ≤ 12 * d.1 + 4 * h.1
      · rw [if_pos ht]
        have haggNat := aggregate_partition_cumulant_bound
          (d := d.1) (h := h.1) hp hd Q
        have hagg :
            (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) ≤
              ((3 * K₂ : ℕ) : ℝ) ^ p *
                ((4 * p + 1 : ℕ) : ℝ) ^
                  (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) := by
          exact_mod_cast haggNat
        have hdim := exact_dimension_factor_inv
          (walshCard m) r p s d.1 h.1 θ hn₀ hr₀ hθ₀ (by omega) hsh
        have hdim_nonneg :
            0 ≤ θ ^ (p - s) * (walshCard m : ℝ) ^ (p - s - h.1) *
              ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
              (r : ℝ) ^ (p - d.1) := by positivity
        let dim : ℝ :=
          θ ^ (p - s) * (walshCard m : ℝ) ^ (p - s - h.1) *
            ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
            (r : ℝ) ^ (p - d.1)
        calc
          θ ^ (p - s) *
              ((walshCard m : ℝ) ^ (p - s - h.1) *
                ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
                (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) *
                (r : ℝ) ^ (p - d.1)) =
              dim * (aggregateEntryPartitionCumulantSum Q d.1 h.1 : ℝ) := by
            dsimp only [dim]
            ring
          _ ≤ dim * (((3 * K₂ : ℕ) : ℝ) ^ p *
                ((4 * p + 1 : ℕ) : ℝ) ^
                  (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1)) :=
            mul_le_mul_of_nonneg_left hagg hdim_nonneg
          _ = _ := by
            dsimp only [dim]
            rw [hdim]
            ring
      · rw [if_neg ht]
        have haggZero : aggregateEntryPartitionCumulantSum Q d.1 h.1 = 0 := by
          unfold aggregateEntryPartitionCumulantSum
          apply Finset.sum_eq_zero
          intro A _
          exfalso
          have htbound := (large_block_and_support_rank_bound hp hd
            (entryPartitionData Q A.1) A.2.1 A.2.2.1
              A.2.2.2.1 A.2.2.2.2).2.2.2.2.2
          exact ht htbound
        rw [haggZero]
        norm_num
    _ = ((3 * K₂ : ℕ) : ℝ) ^ p *
        (((r : ℝ) / walshCard m) * θ) ^ p *
        ∑ d : Fin p, ∑ h : Fin (p - s + 1),
          if t ≤ 12 * d.1 + 4 * h.1 then
            ((4 * p + 1 : ℕ) : ℝ) ^
                (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) *
              (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
                (r : ℝ) ^ (-(d.1 : ℤ)) *
                (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]

/-- Exact equality-partition and entry-cumulant expansion.  Both expectations
remain signed in this identity; absolute values enter only in the estimates
below. -/
theorem signBernoulliExpectation_trace_eq_partition_cumulant_sum
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ) (hp : 1 ≤ p) :
    signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p))) =
      ∑ data :
          (Σ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            InjectivePartitionLabeling P (WalshIndex m)),
        selectorMoment θ
            (labelOfPartition data.1 data.2.1) *
          ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            entryCumulantProduct V
              (labelOfPartition data.1 data.2.1) E := by
  classical
  rw [signBernoulliExpectation_trace_centered_product_pow_expansion V θ hp]
  let e := functionPartitionEquiv
    (iota := Fin (2 * p)) (alpha := WalshIndex m)
  exact Fintype.sum_equiv e
    (fun x : Fin (2 * p) → WalshIndex m ↦
      bernoulliExpectation θ (fun e ↦
        ∏ f : Fin (2 * p), centeredBernoulliValue θ e (x f)) *
      signPairExpectation (fun d₁ d₂ ↦
        ∏ f : Fin (2 * p),
          centeredRandomProjectionEntry V
            (x f) (x (cyclicSucc f)) (d₁, d₂)))
    (fun data ↦
      selectorMoment θ
          (labelOfPartition data.1 data.2.1) *
        ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
          entryCumulantProduct V
            (labelOfPartition data.1 data.2.1) E)
    (fun x ↦ by
      change selectorMoment θ x *
          signPairExpectation (fun d₁ d₂ ↦
            ∏ f : Fin (2 * p),
              centeredRandomProjectionEntry V
                (x f) (x (cyclicSucc f)) (d₁, d₂)) = _
      have hx : labelOfPartition (e x).1 (e x).2.1 = x := e.left_inv x
      rw [hx]
      congr 1
      exact signPairExpectation_cyclic_centeredProjection_product_expansion V x)

@[simp] private theorem boundedSelectorDataOf_s
    {p : ℕ} (hp : 1 ≤ p) (P : SurvivingSelectorPartition p) :
    (boundedSelectorDataOf hp P).1.1 = p - P.1.parts.card := rfl

@[simp] private theorem boundedSelectorDataOf_t
    {p : ℕ} (hp : 1 ≤ p) (P : SurvivingSelectorPartition p) :
    (boundedSelectorDataOf hp P).2.1.1 =
      (equalityOddIncidentVertices P.1).card := rfl

@[simp] private theorem boundedSelectorDataOf_selector
    {p : ℕ} (hp : 1 ≤ p) (P : SurvivingSelectorPartition p) :
    (boundedSelectorDataOf hp P).2.2.1 = P.1 := rfl

private noncomputable def selectorPartitionReindex
    {p : ℕ} (hp : 1 ≤ p)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) :
    (Finpartition (Finset.univ : Finset (Fin (2 * p)))) ⊕
      BoundedSelectorData p := by
  classical
  exact if hgood : ∀ B ∈ P.parts, 2 ≤ B.card
    then Sum.inr (boundedSelectorDataOf hp ⟨P, hgood⟩)
    else Sum.inl P

private theorem selectorPartitionReindex_injective
    {p : ℕ} (hp : 1 ≤ p) :
    Function.Injective (selectorPartitionReindex hp) := by
  classical
  intro P R hPR
  by_cases hP : ∀ B ∈ P.parts, 2 ≤ B.card
  · by_cases hR : ∀ B ∈ R.parts, 2 ≤ B.card
    · simp only [selectorPartitionReindex, dif_pos hP, dif_pos hR] at hPR
      have hdata : boundedSelectorDataOf hp ⟨P, hP⟩ =
          boundedSelectorDataOf hp ⟨R, hR⟩ := Sum.inr.inj hPR
      have hsub : (⟨P, hP⟩ : SurvivingSelectorPartition p) = ⟨R, hR⟩ :=
        boundedSelectorDataOf_injective hp hdata
      exact congrArg Subtype.val hsub
    · simp only [selectorPartitionReindex, dif_pos hP, dif_neg hR] at hPR
      exact (Sum.inr_ne_inl hPR).elim
  · by_cases hR : ∀ B ∈ R.parts, 2 ≤ B.card
    · simp only [selectorPartitionReindex, dif_neg hP, dif_pos hR] at hPR
      exact (Sum.inl_ne_inr hPR).elim
    · simp only [selectorPartitionReindex, dif_neg hP, dif_neg hR] at hPR
      exact Sum.inl.inj hPR

private def selectorPartitionContribution
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) : ℝ :=
  ∑ lab : InjectivePartitionLabeling P (WalshIndex m),
    |selectorMoment θ (labelOfPartition P lab.1) *
      ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
        entryCumulantProduct V (labelOfPartition P lab.1) E|

private def selectorTargetWeight
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ) :
    (Finpartition (Finset.univ : Finset (Fin (2 * p)))) ⊕
      BoundedSelectorData p → ℝ
  | Sum.inl _ => 0
  | Sum.inr D =>
      ∑ lab : InjectivePartitionLabeling D.2.2.1 (WalshIndex m),
        |selectorMoment θ (labelOfPartition D.2.2.1 lab.1) *
          ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            entryCumulantProduct V (labelOfPartition D.2.2.1 lab.1) E|

private theorem signedTrace_abs_le_boundedSelectorData
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ) (hp : 1 ≤ p) :
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p)))| ≤
      ∑ s : Fin p, ∑ t : Fin (p + 1),
        ∑ Q : SelectorEqualityData p s.1 t.1,
          ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
            |selectorMoment θ (labelOfPartition Q.1 lab.1) *
              ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
                entryCumulantProduct V
                  (labelOfPartition Q.1 lab.1) E| := by
  classical
  rw [signBernoulliExpectation_trace_eq_partition_cumulant_sum V θ hp]
  let sourceWeight :
      Finpartition (Finset.univ : Finset (Fin (2 * p))) → ℝ :=
    selectorPartitionContribution V θ
  have htarget_nonneg : ∀ D :
      (Finpartition (Finset.univ : Finset (Fin (2 * p)))) ⊕
        BoundedSelectorData p,
      0 ≤ selectorTargetWeight V θ D := by
    intro D
    rcases D with P | D
    · rfl
    · simp only [selectorTargetWeight]
      positivity
  have hpointwise : ∀ P,
      sourceWeight P ≤ selectorTargetWeight V θ
        (selectorPartitionReindex hp P) := by
    intro P
    by_cases hgood : ∀ B ∈ P.parts, 2 ≤ B.card
    · have hreindex : selectorPartitionReindex hp P =
          Sum.inr (boundedSelectorDataOf hp
            (⟨P, hgood⟩ : SurvivingSelectorPartition p)) := by
        simp only [selectorPartitionReindex, dif_pos hgood]
      rw [hreindex]
      simp only [sourceWeight, selectorPartitionContribution,
        selectorTargetWeight, boundedSelectorDataOf_selector]
      exact le_rfl
    · obtain ⟨B, hBP, hB⟩ :=
        exists_singleton_part_of_not_nonsingleton P hgood
      have hzero : sourceWeight P = 0 := by
        unfold sourceWeight selectorPartitionContribution
        apply Finset.sum_eq_zero
        intro lab _
        rw [selectorMoment_eq_zero_of_singleton θ P lab B hBP hB,
          zero_mul, abs_zero]
      rw [hzero]
      exact htarget_nonneg _
  calc
    |∑ data :
          (Σ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            InjectivePartitionLabeling P (WalshIndex m)),
        selectorMoment θ (labelOfPartition data.1 data.2.1) *
          ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            entryCumulantProduct V
              (labelOfPartition data.1 data.2.1) E| ≤
        ∑ data :
          (Σ P : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            InjectivePartitionLabeling P (WalshIndex m)),
          |selectorMoment θ (labelOfPartition data.1 data.2.1) *
            ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
              entryCumulantProduct V
                (labelOfPartition data.1 data.2.1) E| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ P, sourceWeight P := by
      simp_rw [Fintype.sum_sigma]
      rfl
    _ ≤ ∑ D, selectorTargetWeight V θ D :=
      fintype_sum_le_sum_of_injective
        (selectorPartitionReindex hp)
        (selectorPartitionReindex_injective hp)
        sourceWeight (selectorTargetWeight V θ)
        hpointwise htarget_nonneg
    _ = ∑ D : BoundedSelectorData p,
        ∑ lab : InjectivePartitionLabeling D.2.2.1 (WalshIndex m),
          |selectorMoment θ (labelOfPartition D.2.2.1 lab.1) *
            ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
              entryCumulantProduct V
                (labelOfPartition D.2.2.1 lab.1) E| := by
      rw [Fintype.sum_sum_type]
      simp [selectorTargetWeight]
    _ = _ := by simp_rw [Fintype.sum_sigma]

/-- The sole selector-graph input required by the signed-trace expansion. -/
def SelectorEqualityGraphCountPrinciple : Prop :=
  ∀ p s t : ℕ, 2 ≤ p →
    selectorEqualityCount p s t ≤
      8 * p * 3 ^ p * (4 * p + 1) ^ (74 * (s + t))

private theorem selectorEqualityData_contribution_sum_le
    (hgraph : GraphRankContractionPrinciple)
    (hselector : SelectorEqualityGraphCountPrinciple)
    {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hp : 2 ≤ p) (hr₀ : 0 < r) :
    (∑ Q : SelectorEqualityData p s t,
      ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
        |selectorMoment θ (labelOfPartition Q.1 lab.1) *
          ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
            entryCumulantProduct V (labelOfPartition Q.1 lab.1) E|) ≤
      (8 : ℝ) * p * (9 * K₂ : ℝ) ^ p *
        (((r : ℝ) / walshCard m) * θ) ^ p *
        ∑ d : Fin p, ∑ h : Fin (p - s + 1),
          if t ≤ 12 * d.1 + 4 * h.1 then
            ((4 * p + 1 : ℕ) : ℝ) ^
                (83 * s + 84 * d.1 + 12 * h.1 + 76 * t + 1) *
              (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
                (r : ℝ) ^ (-(d.1 : ℤ)) *
                (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
          else 0 := by
  classical
  let aggregateBound : ℝ :=
    ((3 * K₂ : ℕ) : ℝ) ^ p *
      (((r : ℝ) / walshCard m) * θ) ^ p *
      ∑ d : Fin p, ∑ h : Fin (p - s + 1),
        if t ≤ 12 * d.1 + 4 * h.1 then
          ((4 * p + 1 : ℕ) : ℝ) ^
              (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) *
            (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
              (r : ℝ) ^ (-(d.1 : ℤ)) *
              (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
        else 0
  have haggregate_nonneg : 0 ≤ aggregateBound := by
    dsimp only [aggregateBound]
    positivity
  have hcountNat := hselector p s t hp
  have hcount :
      (selectorEqualityCount p s t : ℝ) ≤
        (8 * p * 3 ^ p * (4 * p + 1) ^ (74 * (s + t)) : ℕ) := by
    exact_mod_cast hcountNat
  calc
    (∑ Q : SelectorEqualityData p s t,
        ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
          |selectorMoment θ (labelOfPartition Q.1 lab.1) *
            ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
              entryCumulantProduct V (labelOfPartition Q.1 lab.1) E|) ≤
        ∑ _Q : SelectorEqualityData p s t, aggregateBound := by
      apply Finset.sum_le_sum
      intro Q _
      exact selectorEntryContribution_abs_sum_le_aggregateBound
        hgraph V hV θ hθ₀ hθ₁ hp hr₀ Q
    _ = (selectorEqualityCount p s t : ℝ) * aggregateBound := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Nat.cast_ofNat]
      rfl
    _ ≤ (8 * p * 3 ^ p *
          (4 * p + 1) ^ (74 * (s + t)) : ℕ) * aggregateBound :=
      mul_le_mul_of_nonneg_right hcount haggregate_nonneg
    _ = _ := by
      dsimp only [aggregateBound]
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
        Nat.cast_ofNat]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro h _
      by_cases ht : t ≤ 12 * d.1 + 4 * h.1
      · rw [if_pos ht, if_pos ht]
        let L : ℝ := 4 * (p : ℝ) + 1
        let base : ℝ := (((r : ℝ) / walshCard m) * θ) ^ p
        let decay : ℝ :=
          ((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
            (r : ℝ) ^ (-(d.1 : ℤ)) *
            (walshCard m : ℝ) ^ (-(h.1 : ℤ))
        have hnine :
            (3 : ℝ) ^ p * (3 * (K₂ : ℝ)) ^ p =
              (9 * (K₂ : ℝ)) ^ p := by
          rw [← mul_pow]
          congr 1
          ring
        have hL :
            L ^ (74 * (s + t)) *
                L ^ (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) =
              L ^ (83 * s + 84 * d.1 + 12 * h.1 + 76 * t + 1) := by
          rw [← pow_add]
          congr 1
          omega
        change
          (8 : ℝ) * p * 3 ^ p * L ^ (74 * (s + t)) *
              ((3 * (K₂ : ℝ)) ^ p * base * (L ^
                (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1) * decay)) =
            8 * p * (9 * (K₂ : ℝ)) ^ p * base *
              (L ^ (83 * s + 84 * d.1 + 12 * h.1 + 76 * t + 1) * decay)
        calc
          _ = 8 * (p : ℝ) *
              (3 ^ p * (3 * (K₂ : ℝ)) ^ p) * base *
              ((L ^ (74 * (s + t)) * L ^
                (84 * d.1 + 12 * h.1 + 9 * s + 2 * t + 1)) * decay) := by
            ring
          _ = _ := by rw [hnine, hL]
      · rw [if_neg ht, if_neg ht]
        ring

private theorem fin_sum_indicator_pow_le_range
    (A : ℝ) (hA : 0 ≤ A) (p B : ℕ) :
    (∑ t : Fin (p + 1), if t.1 ≤ B then A ^ (76 * t.1) else 0) ≤
      ∑ t ∈ Finset.range (B + 1), A ^ (76 * t) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun t : ℕ ↦ if t ≤ B then A ^ (76 * t) else 0) (p + 1)]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_range]
    omega
  · intro t _ _
    positivity

private theorem finite_selector_t_power_bound
    (p r s d h : ℕ) (hp : 2 ≤ p)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    (∑ t : Fin (p + 1),
      if t.1 ≤ 12 * d + 4 * h then
        ((4 * p + 1 : ℕ) : ℝ) ^
          (83 * s + 84 * d + 12 * h + 76 * t.1 + 1)
      else 0) ≤
      2 * ((4 * p + 1 : ℕ) : ℝ) ^
        (83 * s + 996 * d + 316 * h + 1) := by
  let L : ℝ := ((4 * p + 1 : ℕ) : ℝ)
  let C : ℕ := 83 * s + 84 * d + 12 * h + 1
  have hL : 0 ≤ L := by positivity
  obtain ⟨_, _, _, _, hfinite, _, _, _⟩ :=
    trace_geometric_summation p r hp hr
  calc
    (∑ t : Fin (p + 1),
        if t.1 ≤ 12 * d + 4 * h then
          L ^ (83 * s + 84 * d + 12 * h + 76 * t.1 + 1)
        else 0) =
        L ^ C * ∑ t : Fin (p + 1),
          if t.1 ≤ 12 * d + 4 * h then L ^ (76 * t.1) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.1 ≤ 12 * d + 4 * h
      · rw [if_pos ht, if_pos ht, ← pow_add]
        congr 1
        dsimp only [C]
        omega
      · rw [if_neg ht, if_neg ht, mul_zero]
    _ ≤ L ^ C *
        ∑ t ∈ Finset.range (12 * d + 4 * h + 1), L ^ (76 * t) := by
      apply mul_le_mul_of_nonneg_left
      · exact fin_sum_indicator_pow_le_range L hL p (12 * d + 4 * h)
      · positivity
    _ ≤ L ^ C * (2 * L ^ (912 * d + 304 * h)) := by
      apply mul_le_mul_of_nonneg_left
      · exact hfinite d h
      · positivity
    _ = 2 * L ^ (83 * s + 996 * d + 316 * h + 1) := by
      rw [show 83 * s + 996 * d + 316 * h + 1 =
          C + (912 * d + 304 * h) by
        dsimp only [C]
        omega,
        pow_add]
      ring

private theorem three_parameter_reciprocal_decay_le
    (n r s d h : ℕ) (θ : ℝ)
    (hn : 0 < n) (hr : 0 < r)
    (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (n : ℝ) * θ) :
    (((n : ℝ) * θ) ^ (-(s : ℤ)) *
        (r : ℝ) ^ (-(d : ℤ)) *
        (n : ℝ) ^ (-(h : ℤ))) ≤
      ((r : ℝ)⁻¹) ^ (s + d + h) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnθ : 0 < (n : ℝ) * θ := mul_pos hnreal hθ₀
  have hθleone : θ ≤ 1 := hθ₁.trans (by norm_num)
  have hrn : (r : ℝ) ≤ n := by
    calc
      (r : ℝ) ≤ (n : ℝ) * θ := hκ
      _ ≤ n := by nlinarith
  have hinvθ : ((n : ℝ) * θ)⁻¹ ≤ (r : ℝ)⁻¹ :=
    (inv_le_inv₀ hnθ hrreal).2 hκ
  have hinvn : (n : ℝ)⁻¹ ≤ (r : ℝ)⁻¹ :=
    (inv_le_inv₀ hnreal hrreal).2 hrn
  have hs := pow_le_pow_left₀ (inv_nonneg.mpr hnθ.le) hinvθ s
  have hh := pow_le_pow_left₀ (inv_nonneg.mpr hnreal.le) hinvn h
  simp only [zpow_neg, zpow_natCast, ← inv_pow]
  calc
    ((n : ℝ) * θ)⁻¹ ^ s * (r : ℝ)⁻¹ ^ d * (n : ℝ)⁻¹ ^ h ≤
        (r : ℝ)⁻¹ ^ s * (r : ℝ)⁻¹ ^ d * (r : ℝ)⁻¹ ^ h := by
      gcongr
    _ = (r : ℝ)⁻¹ ^ (s + d + h) := by
      rw [pow_add, pow_add]

private theorem geometric_term_domination
    (m r p s d h : ℕ) (θ : ℝ)
    (hr : 0 < r) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ) :
    ((4 * p + 1 : ℕ) : ℝ) ^
          (83 * s + 996 * d + 316 * h + 1) *
        (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
          (r : ℝ) ^ (-(d : ℤ)) *
          (walshCard m : ℝ) ^ (-(h : ℤ))) ≤
      ((4 * p + 1 : ℕ) : ℝ) *
        ((((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r) ^ (s + d + h)) := by
  let L : ℝ := ((4 * p + 1 : ℕ) : ℝ)
  let k : ℕ := s + d + h
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast (show 1 ≤ 4 * p + 1 by omega)
  have hexponent :
      83 * s + 996 * d + 316 * h + 1 ≤ 1000 * k + 1 := by
    dsimp only [k]
    omega
  have hpow :
      L ^ (83 * s + 996 * d + 316 * h + 1) ≤ L ^ (1000 * k + 1) :=
    pow_le_pow_right₀ hL hexponent
  have hdecay := three_parameter_reciprocal_decay_le
    (walshCard m) r s d h θ Fintype.card_pos hr hθ₀ hθ₁ hκ
  have hleft_nonneg :
      0 ≤ L ^ (83 * s + 996 * d + 316 * h + 1) := by positivity
  have hright_nonneg : 0 ≤ ((r : ℝ)⁻¹) ^ k := by positivity
  calc
    L ^ (83 * s + 996 * d + 316 * h + 1) *
        (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
          (r : ℝ) ^ (-(d : ℤ)) *
          (walshCard m : ℝ) ^ (-(h : ℤ))) ≤
        L ^ (1000 * k + 1) * ((r : ℝ)⁻¹) ^ k :=
      mul_le_mul hpow hdecay (by positivity) (by positivity)
    _ = L * (L ^ 1000 / r) ^ k := by
      rw [show 1000 * k + 1 = 1 + 1000 * k by omega,
        pow_add, pow_mul, div_pow]
      simp only [pow_one, div_eq_mul_inv, inv_pow]
      ring

private theorem finite_selector_parameter_sum_le
    (m r p : ℕ) (θ : ℝ)
    (hp : 2 ≤ p) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    (∑ s : Fin p, ∑ t : Fin (p + 1),
      ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
        if t.1 ≤ 12 * d.1 + 4 * h.1 then
          ((4 * p + 1 : ℕ) : ℝ) ^
              (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1) *
            (((walshCard m : ℝ) * θ) ^ (-(s.1 : ℤ)) *
              (r : ℝ) ^ (-(d.1 : ℤ)) *
              (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
        else 0) ≤
      2 * ((4 * p + 1 : ℕ) : ℝ) *
        ∑ s : Fin p, ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
          ((((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r) ^
            (s.1 + d.1 + h.1)) := by
  have hr₀ : 0 < r := by
    have hlower : 0 < 2 * (4 * p + 1) ^ 1000 := by positivity
    exact lt_of_lt_of_le hlower hr
  let L : ℝ := ((4 * p + 1 : ℕ) : ℝ)
  let ρ : ℝ := L ^ 1000 / r
  calc
    (∑ s : Fin p, ∑ t : Fin (p + 1),
        ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
          if t.1 ≤ 12 * d.1 + 4 * h.1 then
            L ^ (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1) *
              (((walshCard m : ℝ) * θ) ^ (-(s.1 : ℤ)) *
                (r : ℝ) ^ (-(d.1 : ℤ)) *
                (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
          else 0) ≤
        ∑ s : Fin p, ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
          2 * L * ρ ^ (s.1 + d.1 + h.1) := by
      apply Finset.sum_le_sum
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro h _
      let decay : ℝ :=
        ((walshCard m : ℝ) * θ) ^ (-(s.1 : ℤ)) *
          (r : ℝ) ^ (-(d.1 : ℤ)) *
          (walshCard m : ℝ) ^ (-(h.1 : ℤ))
      have hdecay : 0 ≤ decay := by
        dsimp only [decay]
        positivity
      have htbound := finite_selector_t_power_bound
        p r s.1 d.1 h.1 hp hr
      have hgeom := geometric_term_domination
        m r p s.1 d.1 h.1 θ hr₀ hθ₀ hθ₁ hκ
      change
        (∑ t : Fin (p + 1),
          if t.1 ≤ 12 * d.1 + 4 * h.1 then
            L ^ (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1) * decay
          else 0) ≤ 2 * L * ρ ^ (s.1 + d.1 + h.1)
      calc
        (∑ t : Fin (p + 1),
            if t.1 ≤ 12 * d.1 + 4 * h.1 then
              L ^ (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1) * decay
            else 0) =
            (∑ t : Fin (p + 1),
              if t.1 ≤ 12 * d.1 + 4 * h.1 then
                L ^ (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1)
              else 0) * decay := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          by_cases ht : t.1 ≤ 12 * d.1 + 4 * h.1
          · rw [if_pos ht, if_pos ht]
          · rw [if_neg ht, if_neg ht, zero_mul]
        _ ≤ (2 * L ^ (83 * s.1 + 996 * d.1 + 316 * h.1 + 1)) *
              decay := mul_le_mul_of_nonneg_right htbound hdecay
        _ = 2 * (L ^ (83 * s.1 + 996 * d.1 + 316 * h.1 + 1) *
              decay) := by ring
        _ ≤ 2 * (L * ρ ^ (s.1 + d.1 + h.1)) := by
          apply mul_le_mul_of_nonneg_left
          · exact hgeom
          · norm_num
        _ = 2 * L * ρ ^ (s.1 + d.1 + h.1) := by ring
    _ = 2 * L *
        ∑ s : Fin p, ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
          ρ ^ (s.1 + d.1 + h.1) := by
      simp only [Finset.mul_sum]

private theorem finite_triple_geometric_le_tsum
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρlt : ρ < 1) (p : ℕ) :
    (∑ s : Fin p, ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
      ρ ^ (s.1 + d.1 + h.1)) ≤
      ∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h) := by
  let S : ℝ := ∑' j : ℕ, ρ ^ j
  have hgeom : Summable (fun j : ℕ ↦ ρ ^ j) :=
    summable_geometric_of_lt_one hρ hρlt
  have hinner : ∀ s d : ℕ,
      (∑' h : ℕ, ρ ^ (s + d + h)) = ρ ^ (s + d) * S := by
    intro s d
    calc
      (∑' h : ℕ, ρ ^ (s + d + h)) =
          ∑' h : ℕ, ρ ^ (s + d) * ρ ^ h := by
        apply tsum_congr
        intro h
        rw [← pow_add]
      _ = ρ ^ (s + d) * S := by rw [tsum_mul_left]
  have hinnerSummable : ∀ s d : ℕ,
      Summable (fun h : ℕ ↦ ρ ^ (s + d + h)) := by
    intro s d
    have hs := hgeom.mul_left (ρ ^ (s + d))
    simpa only [← pow_add] using hs
  have hmiddle : ∀ s : ℕ,
      (∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) = ρ ^ s * S * S := by
    intro s
    calc
      (∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) =
          ∑' d : ℕ, ρ ^ (s + d) * S := by
        apply tsum_congr
        exact hinner s
      _ = ∑' d : ℕ, (ρ ^ s * ρ ^ d) * S := by
        apply tsum_congr
        intro d
        rw [← pow_add]
      _ = ρ ^ s * S * S := by
        rw [tsum_mul_right, tsum_mul_left]
  have hmiddleSummable : ∀ s : ℕ,
      Summable (fun d : ℕ ↦ ∑' h : ℕ, ρ ^ (s + d + h)) := by
    intro s
    rw [show (fun d : ℕ ↦ ∑' h : ℕ, ρ ^ (s + d + h)) =
        (fun d : ℕ ↦ (ρ ^ s * ρ ^ d) * S) by
      funext d
      rw [hinner s d, ← pow_add]]
    exact (hgeom.mul_left (ρ ^ s)).mul_right S
  have houterSummable :
      Summable (fun s : ℕ ↦ ∑' d : ℕ, ∑' h : ℕ,
        ρ ^ (s + d + h)) := by
    rw [show (fun s : ℕ ↦ ∑' d : ℕ, ∑' h : ℕ,
          ρ ^ (s + d + h)) =
        (fun s : ℕ ↦ (ρ ^ s * S) * S) by
      funext s
      exact hmiddle s]
    exact (hgeom.mul_right S).mul_right S
  calc
    (∑ s : Fin p, ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
        ρ ^ (s.1 + d.1 + h.1)) ≤
        ∑ s : Fin p, ∑ d : Fin p, ∑' h : ℕ,
          ρ ^ (s.1 + d.1 + h) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro d _
      rw [Fin.sum_univ_eq_sum_range
        (fun h : ℕ ↦ ρ ^ (s.1 + d.1 + h)) (p - s.1 + 1)]
      exact (hinnerSummable s.1 d.1).sum_le_tsum _
        (fun h _ ↦ pow_nonneg hρ _)
    _ ≤ ∑ s : Fin p, ∑' d : ℕ, ∑' h : ℕ,
          ρ ^ (s.1 + d + h) := by
      apply Finset.sum_le_sum
      intro s _
      rw [Fin.sum_univ_eq_sum_range
        (fun d : ℕ ↦ ∑' h : ℕ, ρ ^ (s.1 + d + h)) p]
      exact (hmiddleSummable s.1).sum_le_tsum _
        (fun d _ ↦ tsum_nonneg (fun h ↦ pow_nonneg hρ _))
    _ ≤ ∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ,
          ρ ^ (s + d + h) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun s : ℕ ↦ ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)) p]
      exact houterSummable.sum_le_tsum _
        (fun s _ ↦ tsum_nonneg (fun d ↦
          tsum_nonneg (fun h ↦ pow_nonneg hρ _)))

/-- Master estimate obtained from the exact signed expansion, selector-graph
count, entry cumulants, and the finite geometric reindexing. -/
theorem signedTrace_master_geometric_bound
    (hgraph : GraphRankContractionPrinciple)
    (hselector : SelectorEqualityGraphCountPrinciple)
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hp : 2 ≤ p) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p)))| ≤
      16 * (p : ℝ) * (4 * p + 1) * (9 * K₂ : ℝ) ^ p *
        (((r : ℝ) / walshCard m) * θ) ^ p *
        (∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ,
          ((((4 * p + 1 : ℕ) : ℝ) ^ 1000 / r) ^ (s + d + h))) := by
  have hr₀ : 0 < r := by
    have hlower : 0 < 2 * (4 * p + 1) ^ 1000 := by positivity
    omega
  let L : ℝ := ((4 * p + 1 : ℕ) : ℝ)
  let base : ℝ := (((r : ℝ) / walshCard m) * θ) ^ p
  let ρ : ℝ := L ^ 1000 / r
  let finiteParameters : ℝ :=
    ∑ s : Fin p, ∑ t : Fin (p + 1),
      ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
        if t.1 ≤ 12 * d.1 + 4 * h.1 then
          L ^ (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1) *
            (((walshCard m : ℝ) * θ) ^ (-(s.1 : ℤ)) *
              (r : ℝ) ^ (-(d.1 : ℤ)) *
              (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
        else 0
  let finiteTriple : ℝ :=
    ∑ s : Fin p, ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
      ρ ^ (s.1 + d.1 + h.1)
  let infiniteTriple : ℝ :=
    ∑' s : ℕ, ∑' d : ℕ, ∑' h : ℕ, ρ ^ (s + d + h)
  have hpre := signedTrace_abs_le_boundedSelectorData
    (p := p) V θ (by omega)
  have hfinite : finiteParameters ≤ 2 * L * finiteTriple := by
    exact finite_selector_parameter_sum_le
      m r p θ hp hθ₀ hθ₁ hκ hr
  obtain ⟨hρ, hρhalf, _, _, _, _, _, _⟩ :=
    trace_geometric_summation p r hp hr
  have hρlt : ρ < 1 := hρhalf.trans_lt (by norm_num)
  have hinfinite : finiteTriple ≤ infiniteTriple := by
    exact finite_triple_geometric_le_tsum ρ hρ hρlt p
  have hprefactor_nonneg :
      0 ≤ (8 : ℝ) * p * (9 * K₂ : ℝ) ^ p * base := by
    dsimp only [base]
    positivity
  calc
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
        Matrix.trace
          (((randomProjection d₁ d₂ V -
                ((r : ℝ) / walshCard m) •
                  (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
              (bernoulliProjection e - θ •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
            (2 * p)))| ≤
        ∑ s : Fin p, ∑ t : Fin (p + 1),
          ∑ Q : SelectorEqualityData p s.1 t.1,
            ∑ lab : InjectivePartitionLabeling Q.1 (WalshIndex m),
              |selectorMoment θ (labelOfPartition Q.1 lab.1) *
                ∑ E : Finpartition (Finset.univ : Finset (Fin (2 * p))),
                  entryCumulantProduct V
                    (labelOfPartition Q.1 lab.1) E| := hpre
    _ ≤ ∑ s : Fin p, ∑ t : Fin (p + 1),
        (8 : ℝ) * p * (9 * K₂ : ℝ) ^ p * base *
          ∑ d : Fin p, ∑ h : Fin (p - s.1 + 1),
            if t.1 ≤ 12 * d.1 + 4 * h.1 then
              L ^ (83 * s.1 + 84 * d.1 + 12 * h.1 + 76 * t.1 + 1) *
                (((walshCard m : ℝ) * θ) ^ (-(s.1 : ℤ)) *
                  (r : ℝ) ^ (-(d.1 : ℤ)) *
                  (walshCard m : ℝ) ^ (-(h.1 : ℤ)))
            else 0 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      exact selectorEqualityData_contribution_sum_le
        hgraph hselector V hV θ hθ₀ hθ₁ hp hr₀
    _ = (8 : ℝ) * p * (9 * K₂ : ℝ) ^ p * base *
        finiteParameters := by
      dsimp only [finiteParameters]
      simp only [Finset.mul_sum]
    _ ≤ (8 : ℝ) * p * (9 * K₂ : ℝ) ^ p * base *
        (2 * L * finiteTriple) :=
      mul_le_mul_of_nonneg_left hfinite hprefactor_nonneg
    _ ≤ (8 : ℝ) * p * (9 * K₂ : ℝ) ^ p * base *
        (2 * L * infiniteTriple) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hinfinite (by positivity)
      · exact hprefactor_nonneg
    _ = 16 * (p : ℝ) * L * (9 * K₂ : ℝ) ^ p * base *
        infiniteTriple := by ring
    _ = _ := by
      dsimp only [L, base, infiniteTriple, ρ]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        Nat.cast_ofNat]

/-- The signed-trace inequality, parameterized only by the graph contraction
and selector equality-count principles. -/
theorem signedTrace_bound
    (hgraph : GraphRankContractionPrinciple)
    (hselector : SelectorEqualityGraphCountPrinciple)
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hp : 2 ≤ p) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p)))| ≤
      (K₀ : ℝ) ^ p * (((r : ℝ) / walshCard m) * θ) ^ p := by
  apply signedTrace_bound_of_master_geometric_bound p r
    (signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p))))
    ((((r : ℝ) / walshCard m) * θ) ^ p) hp hr
  · positivity
  · exact signedTrace_master_geometric_bound
      hgraph hselector V hV θ hp hθ₀ hθ₁ hκ hr


end

end Problem56
