import Problem56.PaperV6.BinaryBridges

open scoped BigOperators Matrix Classical
namespace Problem56.PaperV6

 theorem aggregate_parameters {p s t d h : ℕ} (hp : 2 ≤ p)
    {Q : SelectorEqualityData p s t} (A : AggregateEntryPartition Q d h) :
    d ≤ p - 1 ∧ s + h ≤ p := by
  have hpos := entry_parts_card_pos (by omega) A.1
  have hblocks := A.2.2.2.1
  have hQpos := entry_parts_card_pos (by omega) Q.1
  have hQcard := Q.2.2.1
  have hrank : h ≤ Q.1.parts.card := by
    rw [← A.2.2.2.2]
    exact (Matrix.rank_le_card_width _).trans_eq (Fintype.card_coe Q.1.parts)
  omega

theorem entry_weighted_count : EntryWeightedCountExpected := by
  classical
  intro p s t hp Q d h
  constructor
  · by_cases hn : Nonempty (AggregateEntryPartition Q d h)
    · obtain ⟨A⟩ := hn
      exact I28_aggregate_partition_cumulant_bound hp (aggregate_parameters hp A).1 Q
    · haveI : IsEmpty (AggregateEntryPartition Q d h) := not_nonempty_iff.mp hn
      simp [aggregateEntryPartitionCumulantSum]
  · rintro ⟨A⟩
    exact (I24_large_block_and_support_rank_bound hp (aggregate_parameters hp A).1
      (entryPartitionData Q A.1) A.2.1 A.2.2.1 A.2.2.2.1 A.2.2.2.2).2.2.2.2.2

theorem paperSelectorCoefficient_abs_le {p s t : ℕ}
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (Q : SelectorEqualityData p s t) :
    |paperSelectorCoefficient θ Q| ≤ θ ^ (p - s) := by
  classical
  unfold paperSelectorCoefficient
  rw [Finset.abs_prod]
  calc
    (∏ B ∈ Q.1.parts, |θ * (1 - θ) ^ B.card + (1 - θ) * (-θ) ^ B.card|) ≤
      ∏ _B ∈ Q.1.parts, θ := by
        apply Finset.prod_le_prod
        · intro B hB
          exact abs_nonneg _
        · intro B hB
          exact I17_centered_bernoulli_moment_bound θ B.card hθ hθ' (Q.2.1 B hB)
    _ = θ ^ (p - s) := by rw [Finset.prod_const, Q.2.2.1]

/-- Reproved finite-sum helper from B's SignedTraceExpansion, 556--576. -/
theorem paper_sum_le_of_injective
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (g : α → ℝ) (G : β → ℝ)
    (hg : ∀ a, g a ≤ G (f a)) (hG : ∀ b, 0 ≤ G b) :
    (∑ a, g a) ≤ ∑ b, G b := by
  calc
    (∑ a, g a) ≤ ∑ a, G (f a) := Finset.sum_le_sum fun a _ ↦ hg a
    _ = ∑ b ∈ Finset.univ.image f, G b := by
      rw [Finset.sum_image]; exact hf.injOn
    _ ≤ ∑ b ∈ (Finset.univ : Finset β), G b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr fun _ _ ↦ Finset.mem_univ _
      · intro b _ _; exact hG b
    _ = _ := rfl

/-- B's XOR support argument, with the actual paper product and label type. -/
theorem paper_product_xor_of_ne_zero {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (Q : SelectorEqualityData p s t) (lab : EqualityVertex Q.1 → WalshIndex m)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hn : ∀ B ∈ P.parts, 2 ≤ B.card)
    (hne : paperEntryCumulantProduct V Q lab P ≠ 0) :
    PaperXorConstraints (entryPartitionData Q P) lab := by
  intro B hB
  by_contra hx
  apply hne
  exact centeredProjection_partitionCumulantProduct_eq_zero_of_block_xor
    (show GraphRankContractionPrinciple from @graph_rank_contraction) V hV
    (fun e ↦ lab (equalityVertexAt Q.1 e)) P B hB (hn B hB)
    (by simpa only [paperBlock_xor_sum, entryPartitionData] using hx)

/-- Reuses B's cumulant estimate and exact XOR count; all absolute values are
inside the label sum. This is the fixed-partition form of B 800--870. -/
theorem paper_sum_injective_labels_bound {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (Q : SelectorEqualityData p s t)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p))))
    (hn : ∀ B ∈ P.parts, 2 ≤ B.card) :
    (∑ lab : {lab : EqualityVertex Q.1 → WalshIndex m // Function.Injective lab},
      |paperEntryCumulantProduct V Q lab.1 P|) ≤
      (walshCard m : ℝ) ^
        (Q.1.parts.card - Matrix.rank (entryConstraintMatrix (entryPartitionData Q P))) *
      ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
      (entryPartitionCumulantConstant P : ℝ) * (r : ℝ) ^ P.parts.card := by
  classical
  let D : EntryCumulantPartitionData p s t := entryPartitionData Q P
  let C : ℝ := ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
    (entryPartitionCumulantConstant P : ℝ) * (r : ℝ) ^ P.parts.card
  let includeLabel : {lab : EqualityVertex Q.1 → WalshIndex m // Function.Injective lab} →
    EqualityVertex D.selector.1 → WalshIndex m := fun lab ↦ lab.1
  calc
    _ ≤ ∑ lab : EqualityVertex D.selector.1 → WalshIndex m,
        if PaperXorConstraints D lab then C else 0 := by
      apply paper_sum_le_of_injective includeLabel Subtype.val_injective
      · intro lab
        by_cases hx : PaperXorConstraints D (includeLabel lab)
        · rw [if_pos hx]
          exact centeredProjection_partitionCumulantProduct_bound
            (show GraphRankContractionPrinciple from @graph_rank_contraction) V hV
            (fun e ↦ lab.1 (equalityVertexAt Q.1 e)) P hn
        · rw [if_neg hx]
          have hz : paperEntryCumulantProduct V Q lab.1 P = 0 := by
            by_contra hne
            exact hx (by
              simpa only [D, includeLabel, entryPartitionData] using
                paper_product_xor_of_ne_zero V hV Q lab.1 P hn hne)
          rw [hz, abs_zero]
      · intro lab
        split
        · dsimp only [C]; positivity
        · exact le_rfl
    _ = (Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
        PaperXorConstraints (m := m) D lab} : ℝ) * C := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Fintype.card_subtype]
    _ = _ := by
      rw [(binary_count m p s t D).1]
      simp only [Nat.cast_pow]
      dsimp only [C, D, entryPartitionData]
      ring

/-- Normalization transport through I29, retaining all negative powers. -/
theorem paper_dimension_factor (n r p s d h : ℕ) (θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hθ : 0 < θ)
    (hd : d ≤ p) (hsh : s + h ≤ p) :
    θ ^ (p - s) * (n : ℝ) ^ (p - s - h) *
      ((n : ℝ)⁻¹) ^ (2 * p) * (r : ℝ) ^ (p - d) =
      (((r : ℝ) / n) * θ) ^ p * ((n : ℝ) * θ) ^ (-(s : ℤ)) *
        (r : ℝ) ^ (-(d : ℤ)) * (n : ℝ) ^ (-(h : ℤ)) := by
  have htwop : (2 : ℤ) * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by norm_num
  have hpow : ((n : ℝ)⁻¹) ^ (2 * p) = (n : ℝ) ^ (-(2 * p : ℤ)) := by
    rw [htwop, zpow_neg, zpow_natCast, inv_pow]
  calc
    _ = θ ^ (p - s) * (r : ℝ) ^ (p - d) *
      (n : ℝ) ^ (-(2 * p : ℤ)) * (n : ℝ) ^ (p - s - h) := by rw [hpow]; ring
    _ = _ := I29_exact_dimension_factor n r p s d h θ hn hr hθ hd hsh

theorem paperEntry_fixed_class_sum_bound {m r p s t d h : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (Q : SelectorEqualityData p s t) :
    (∑ P : AggregateEntryPartition Q d h,
      ∑ lab : {lab : EqualityVertex Q.1 → WalshIndex m // Function.Injective lab},
        |paperEntryCumulantProduct V Q lab.1 P.1|) ≤
      (walshCard m : ℝ) ^ (p - s - h) *
        ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
        (aggregateEntryPartitionCumulantSum Q d h : ℝ) * (r : ℝ) ^ (p - d) := by
  classical
  calc
    _ ≤ ∑ P : AggregateEntryPartition Q d h,
        (walshCard m : ℝ) ^ (Q.1.parts.card - h) *
          ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
          (entryPartitionCumulantConstant P.1 : ℝ) * (r : ℝ) ^ (p - d) := by
      apply Finset.sum_le_sum
      intro P _
      have hb := paper_sum_injective_labels_bound V hV Q P.1 P.2.1
      simpa only [P.2.2.2.1, P.2.2.2.2] using hb
    _ = _ := by
      rw [Q.2.2.1]
      unfold aggregateEntryPartitionCumulantSum
      push_cast
      simp only [Finset.mul_sum, Finset.sum_mul]

theorem entry_absolute_contribution : EntryAbsoluteContributionExpected := by
  classical
  intro m r p s t hp hr V hV θ hθ hθ' Q d h
  by_cases hn : Nonempty (AggregateEntryPartition Q d h)
  · obtain ⟨A⟩ := hn
    obtain ⟨hd, hsh⟩ := aggregate_parameters hp A
    have hsum := paperEntry_fixed_class_sum_bound V hV Q (d := d) (h := h)
    have hcoeff := paperSelectorCoefficient_abs_le θ hθ hθ' Q
    have haggNat := (entry_weighted_count p s t hp Q d h).1
    have hagg : (aggregateEntryPartitionCumulantSum Q d h : ℝ) ≤
        ((3 * K₂ : ℕ) : ℝ) ^ p *
          ((4 * p + 1 : ℕ) : ℝ) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) := by
      exact_mod_cast haggNat
    have hdim := paper_dimension_factor
      (walshCard m) r p s d h θ Fintype.card_pos (by omega) hθ (by omega) hsh
    let dim : ℝ := θ ^ (p - s) * (walshCard m : ℝ) ^ (p - s - h) *
      ((walshCard m : ℝ)⁻¹) ^ (2 * p) * (r : ℝ) ^ (p - d)
    have hdimnonneg : 0 ≤ dim := by dsimp [dim]; positivity
    calc
      paperEntryAbsoluteContribution V θ Q d h ≤
        θ ^ (p - s) * ((walshCard m : ℝ) ^ (p - s - h) *
          ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
          (aggregateEntryPartitionCumulantSum Q d h : ℝ) * (r : ℝ) ^ (p - d)) := by
        exact mul_le_mul hcoeff hsum (by positivity) (by positivity)
      _ = dim * (aggregateEntryPartitionCumulantSum Q d h : ℝ) := by dsimp [dim]; ring
      _ ≤ dim * (((3 * K₂ : ℕ) : ℝ) ^ p *
          ((4 * p + 1 : ℕ) : ℝ) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1)) :=
        mul_le_mul_of_nonneg_left hagg hdimnonneg
      _ = _ := by dsimp only [dim]; rw [hdim]; ring
  · haveI : IsEmpty (AggregateEntryPartition Q d h) := not_nonempty_iff.mp hn
    simp only [paperEntryAbsoluteContribution, Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    positivity

end Problem56.PaperV6
