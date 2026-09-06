import Problem56.CumulantMoment

/-!
Finite combinatorial bounds for the Rademacher cumulants in the frozen I13
interface.  The partition count is encoded by sending each point to the least
element of its block; this gives the sharp elementary `n ^ n` upper bound
without enumerating the doubly-exponential `Finpartition` Fintype instance.
-/

namespace Problem56

set_option maxHeartbeats 800000

open scoped BigOperators

open Finset

noncomputable def finpartitionRepresentativeCode {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Fin n → Fin n :=
  fun i ↦ (P.part i).min' ((P.part_nonempty).2 (Finset.mem_univ i))

private theorem representativeCode_mem_part {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (i : Fin n) :
    finpartitionRepresentativeCode P i ∈ P.part i := by
  exact Finset.min'_mem _ _

private theorem representativeCode_eq_iff_part_eq {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (i j : Fin n) :
    finpartitionRepresentativeCode P i = finpartitionRepresentativeCode P j ↔
      P.part i = P.part j := by
  constructor
  · intro h
    apply P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ i))
      (P.part_mem.2 (Finset.mem_univ j))
      (representativeCode_mem_part P i)
    rw [h]
    exact representativeCode_mem_part P j
  · rintro h
    simp only [finpartitionRepresentativeCode]
    congr

private theorem finpartitionRepresentativeCode_injective {n : ℕ} :
    Function.Injective
      (finpartitionRepresentativeCode :
        Finpartition (Finset.univ : Finset (Fin n)) → (Fin n → Fin n)) := by
  intro P Q hcode
  have hpart : ∀ i, P.part i = Q.part i := by
    intro i
    ext j
    rw [P.mem_part_iff_part_eq_part (Finset.mem_univ j) (Finset.mem_univ i),
      Q.mem_part_iff_part_eq_part (Finset.mem_univ j) (Finset.mem_univ i),
      ← representativeCode_eq_iff_part_eq P,
      ← representativeCode_eq_iff_part_eq Q]
    rw [congrFun hcode j, congrFun hcode i]
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    have hPi : P.part i = B := P.part_eq_of_mem hB hi
    rw [← hPi, hpart i]
    exact Q.part_mem.2 (Finset.mem_univ i)
  · intro hB
    obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hB
    have hQi : Q.part i = B := Q.part_eq_of_mem hB hi
    rw [← hQi, ← hpart i]
    exact P.part_mem.2 (Finset.mem_univ i)

theorem card_finpartition_univ_le_self_pow (n : ℕ) :
    Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) ≤ n ^ n := by
  calc
    Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) ≤
        Fintype.card (Fin n → Fin n) :=
      Fintype.card_le_of_injective finpartitionRepresentativeCode
        finpartitionRepresentativeCode_injective
    _ = n ^ n := by simp

private theorem abs_uniformExpectation_le_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (F : Ω → ℝ)
    (hF : ∀ ω, |F ω| ≤ 1) :
    |uniformExpectation F| ≤ 1 := by
  have hcardNat : 0 < Fintype.card Ω := Fintype.card_pos
  have hcard : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast hcardNat
  rw [uniformExpectation, abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  calc
    |∑ ω, F ω| ≤ ∑ ω, |F ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum fun ω _ ↦ hF ω
    _ = Fintype.card Ω := by simp
    _ = 1 * Fintype.card Ω := by ring

private theorem abs_uniformExpectation_rademacher_prod_le_one
    {n : ℕ} (B : Finset (Fin n)) :
    |uniformExpectation (Ω := Bool) (fun ξ ↦
      ∏ j ∈ B, if ξ then (-1 : ℝ) else 1)| ≤ 1 := by
  apply abs_uniformExpectation_le_one
  intro ξ
  rw [abs_prod]
  cases ξ <;> simp

private noncomputable def rademacherPartitionTerm (b : ℕ)
    (P : Finpartition (Finset.univ : Finset (Fin b))) : ℝ :=
  ((-1 : ℝ) ^ (P.parts.card - 1) *
    (Nat.factorial (P.parts.card - 1) : ℝ)) *
    ∏ B ∈ P.parts, uniformExpectation (fun ω : Bool ↦
      ∏ j ∈ B, if ω then (-1 : ℝ) else 1)

private theorem abs_rademacherPartitionTerm_le (b : ℕ)
    (P : Finpartition (Finset.univ : Finset (Fin b))) :
    |rademacherPartitionTerm b P| ≤ (b : ℝ) ^ b := by
  have hprod :
      |∏ B ∈ P.parts, uniformExpectation (fun ω : Bool ↦
        ∏ j ∈ B, if ω then (-1 : ℝ) else 1)| ≤ 1 := by
    rw [abs_prod]
    apply Finset.prod_le_one
    · intro B hB
      exact abs_nonneg _
    · intro B hB
      exact abs_uniformExpectation_rademacher_prod_le_one B
  have hparts : P.parts.card - 1 ≤ b :=
    (Nat.sub_le _ _).trans (by simpa using P.card_parts_le_card)
  have hfactNat : Nat.factorial (P.parts.card - 1) ≤ b ^ b :=
    (Nat.factorial_le hparts).trans b.factorial_le_pow
  calc
    |rademacherPartitionTerm b P| =
        (Nat.factorial (P.parts.card - 1) : ℝ) *
          |∏ B ∈ P.parts, uniformExpectation (fun ω : Bool ↦
            ∏ j ∈ B, if ω then (-1 : ℝ) else 1)| := by
      simp only [rademacherPartitionTerm, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (Nat.factorial (P.parts.card - 1) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (Nat.factorial (P.parts.card - 1) : ℝ) := by ring
    _ ≤ (b : ℝ) ^ b := by exact_mod_cast hfactNat

private theorem abs_jointCumulant_rademacher_le (b : ℕ) :
    |jointCumulant (Ω := Bool) (q := b)
      (fun _ ξ ↦ if ξ then (-1 : ℝ) else 1)| ≤ (b : ℝ) ^ (2 * b) := by
  change |∑ P : Finpartition (Finset.univ : Finset (Fin b)),
    rademacherPartitionTerm b P| ≤ _
  calc
    |∑ P : Finpartition (Finset.univ : Finset (Fin b)),
        rademacherPartitionTerm b P| ≤
        ∑ P : Finpartition (Finset.univ : Finset (Fin b)),
          |rademacherPartitionTerm b P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _P : Finpartition (Finset.univ : Finset (Fin b)), (b : ℝ) ^ b := by
      exact Finset.sum_le_sum fun P _ ↦ abs_rademacherPartitionTerm_le b P
    _ = (Fintype.card
          (Finpartition (Finset.univ : Finset (Fin b))) : ℝ) * (b : ℝ) ^ b := by
      simp
    _ ≤ (b ^ b : ℕ) * (b : ℝ) ^ b := by
      gcongr
      exact_mod_cast card_finpartition_univ_le_self_pow b
    _ = (b : ℝ) ^ (2 * b) := by
      norm_cast
      rw [← pow_add]
      congr 1
      omega

private theorem card_evenOccurrencePartition_le (b : ℕ) :
    Fintype.card (EvenOccurrencePartition b) ≤ (2 * b) ^ (2 * b) := by
  exact (Fintype.card_subtype_le _).trans
    (card_finpartition_univ_le_self_pow (2 * b))

private theorem card_evenOccurrencePartition_pair_le (b : ℕ) :
    Fintype.card (EvenOccurrencePartition b × EvenOccurrencePartition b) ≤
      (2 * b) ^ (4 * b) := by
  rw [Fintype.card_prod]
  calc
    Fintype.card (EvenOccurrencePartition b) *
        Fintype.card (EvenOccurrencePartition b) ≤
        (2 * b) ^ (2 * b) * (2 * b) ^ (2 * b) :=
      Nat.mul_le_mul (card_evenOccurrencePartition_le b)
        (card_evenOccurrencePartition_le b)
    _ = (2 * b) ^ (4 * b) := by
      rw [← pow_add]
      congr 1
      omega

private theorem abs_rademacherCumulant_block_le
    (b : ℕ) (P : EvenOccurrencePartition b)
    (B : {B // B ∈ P.1.parts}) :
    |rademacherCumulant B.1.card| ≤
      ((2 * b : ℕ) : ℝ) ^ (2 * B.1.card) := by
  have hcardNat : B.1.card ≤ 2 * b := by
    calc
      B.1.card ≤ (Finset.univ : Finset (Fin (2 * b))).card :=
        Finset.card_le_card (P.1.le B.2)
      _ = 2 * b := by simp
  calc
    |rademacherCumulant B.1.card| ≤
        (B.1.card : ℝ) ^ (2 * B.1.card) := by
      exact abs_jointCumulant_rademacher_le B.1.card
    _ ≤ ((2 * b : ℕ) : ℝ) ^ (2 * B.1.card) := by
      gcongr

private theorem abs_rademacherCumulant_block_product_le
    (b : ℕ) (P : EvenOccurrencePartition b) :
    |∏ B : {B // B ∈ P.1.parts}, rademacherCumulant B.1.card| ≤
      ((2 * b : ℕ) : ℝ) ^ (4 * b) := by
  rw [abs_prod]
  calc
    ∏ B : {B // B ∈ P.1.parts}, |rademacherCumulant B.1.card| ≤
        ∏ B : {B // B ∈ P.1.parts},
          ((2 * b : ℕ) : ℝ) ^ (2 * B.1.card) := by
      exact Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _)
        (fun B _ ↦ abs_rademacherCumulant_block_le b P B)
    _ = ∏ B ∈ P.1.parts,
          ((2 * b : ℕ) : ℝ) ^ (2 * B.card) := by
      exact (Finset.prod_subtype P.1.parts (fun _ ↦ Iff.rfl)
        (fun B ↦ ((2 * b : ℕ) : ℝ) ^ (2 * B.card))).symm
    _ = ((2 * b : ℕ) : ℝ) ^
          (∑ B ∈ P.1.parts, 2 * B.card) := by
      exact Finset.prod_pow_eq_pow_sum P.1.parts (fun B ↦ 2 * B.card) _
    _ = ((2 * b : ℕ) : ℝ) ^ (4 * b) := by
      congr 1
      calc
        ∑ B ∈ P.1.parts, 2 * B.card =
            2 * ∑ B ∈ P.1.parts, B.card := by
          rw [Finset.mul_sum]
        _ = 2 * (2 * b) := by rw [P.1.sum_card_parts]; simp
        _ = 4 * b := by omega

/-- Exact aggregate helper for the frozen I13 interface. -/
theorem rademacher_cumulant_bound (b : ℕ) :
    |jointCumulant (Ω := Bool) (q := b)
      (fun _ ξ ↦ if ξ then (-1 : ℝ) else 1)| ≤ (b : ℝ) ^ (2 * b) ∧
    Fintype.card (EvenOccurrencePartition b × EvenOccurrencePartition b) ≤
      (2 * b) ^ (4 * b) ∧
    (∀ P : EvenOccurrencePartition b,
      |∏ B : {B // B ∈ P.1.parts}, rademacherCumulant B.1.card| ≤
        ((2 * b : ℕ) : ℝ) ^ (4 * b)) := by
  exact ⟨abs_jointCumulant_rademacher_le b,
    card_evenOccurrencePartition_pair_le b,
    abs_rademacherCumulant_block_product_le b⟩

#print axioms card_finpartition_univ_le_self_pow
#print axioms abs_jointCumulant_rademacher_le
#print axioms rademacher_cumulant_bound

end Problem56
