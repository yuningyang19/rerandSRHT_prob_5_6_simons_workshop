import Problem56.Definitions

/-! Counting large-block patterns by a padded canonical encoding. -/

open scoped BigOperators

namespace Problem56

private theorem largeBlockPattern_support_card_le {p d : ℕ}
    (pattern : LargeBlockPattern p d) : pattern.1.1.card ≤ 6 * d := by
  classical
  let S := pattern.1.1
  let P := pattern.1.2
  have hblocks : P.parts.card ≤ 2 * d := by
    calc
      P.parts.card = ∑ _B ∈ P.parts, 1 := by simp
      _ ≤ ∑ B ∈ P.parts, (B.card - 2) := by
        apply Finset.sum_le_sum
        intro B hB
        have hlarge : 3 ≤ B.card := pattern.2.1 B hB
        omega
      _ = 2 * d := pattern.2.2
  change S.card ≤ 6 * d
  calc
    S.card = ∑ B ∈ P.parts, B.card := P.sum_card_parts.symm
    _ = ∑ B ∈ P.parts, ((B.card - 2) + 2) := by
      apply Finset.sum_congr rfl
      intro B hB
      have hlarge : 3 ≤ B.card := pattern.2.1 B hB
      omega
    _ = (∑ B ∈ P.parts, (B.card - 2)) + 2 * P.parts.card := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ = 2 * d + 2 * P.parts.card := by rw [pattern.2.2]
    _ ≤ 6 * d := by omega

private def largeBlockRepresentative {p : ℕ} {S : Finset (Fin (2 * p))}
    (P : Finpartition S) (x : Fin (2 * p)) (hx : x ∈ S) : Fin (2 * p) :=
  (P.part x).min' ((P.part_nonempty).2 hx)

private theorem largeBlockRepresentative_eq_iff {p : ℕ}
    {S : Finset (Fin (2 * p))} (P : Finpartition S)
    {x y : Fin (2 * p)} (hx : x ∈ S) (hy : y ∈ S) :
    largeBlockRepresentative P x hx = largeBlockRepresentative P y hy ↔
      P.part x = P.part y := by
  constructor
  · intro h
    apply P.eq_of_mem_parts (a := largeBlockRepresentative P x hx)
      (P.part_mem.2 hx) (P.part_mem.2 hy)
    · exact Finset.min'_mem (P.part x) ((P.part_nonempty).2 hx)
    · rw [h]
      exact Finset.min'_mem (P.part y) ((P.part_nonempty).2 hy)
  · intro h
    unfold largeBlockRepresentative
    apply le_antisymm
    · apply Finset.min'_le
      rw [h]
      exact Finset.min'_mem _ _
    · apply Finset.min'_le
      rw [← h]
      exact Finset.min'_mem _ _

private def largeBlockPatternCode {p d : ℕ} (pattern : LargeBlockPattern p d) :
    Fin (6 * d) → (Option (Fin (2 * p)) × Option (Fin (2 * p))) := fun i ↦
  if hi : i.1 < pattern.1.1.card then
    let j : Fin pattern.1.1.card := ⟨i.1, hi⟩
    let x : Fin (2 * p) := pattern.1.1.orderEmbOfFin rfl j
    (some x, some (largeBlockRepresentative pattern.1.2 x
      (pattern.1.1.orderEmbOfFin_mem rfl j)))
  else
    (none, none)

private theorem largeBlockPatternCode_support {p d : ℕ}
    (pattern : LargeBlockPattern p d) (x : Fin (2 * p)) :
    x ∈ pattern.1.1 ↔ ∃ i, (largeBlockPatternCode pattern i).1 = some x := by
  constructor
  · intro hx
    let j : Fin pattern.1.1.card :=
      (pattern.1.1.orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hj : j.1 < 6 * d :=
      lt_of_lt_of_le j.2 (largeBlockPattern_support_card_le pattern)
    let i : Fin (6 * d) := ⟨j.1, hj⟩
    refine ⟨i, ?_⟩
    have henum : pattern.1.1.orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val
        ((pattern.1.1.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    simp [largeBlockPatternCode, i, j, henum]
  · rintro ⟨i, hi⟩
    simp only [largeBlockPatternCode] at hi
    split at hi
    · have hmem :=
        pattern.1.1.orderEmbOfFin_mem rfl
          (⟨i.1, ‹i.1 < pattern.1.1.card›⟩)
      have heq := Option.some.inj hi
      rw [heq] at hmem
      exact hmem
    · simp at hi

private theorem largeBlockPatternCode_injective {p d : ℕ} :
    Function.Injective
      (largeBlockPatternCode : LargeBlockPattern p d →
        Fin (6 * d) → (Option (Fin (2 * p)) × Option (Fin (2 * p)))) := by
  intro pattern₁ pattern₂ hcode
  have hsupport : pattern₁.1.1 = pattern₂.1.1 := by
    ext x
    rw [largeBlockPatternCode_support pattern₁ x,
      largeBlockPatternCode_support pattern₂ x]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hcode]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [hcode]; exact hi⟩
  rcases pattern₁ with ⟨⟨S, P⟩, hP⟩
  rcases pattern₂ with ⟨⟨T, Q⟩, hQ⟩
  dsimp only at hsupport
  subst T
  have hrepresentative : ∀ (x : Fin (2 * p)) (hx : x ∈ S),
      largeBlockRepresentative P x hx = largeBlockRepresentative Q x hx := by
    intro x hx
    let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hj : j.1 < 6 * d := lt_of_lt_of_le j.2
      (largeBlockPattern_support_card_le (⟨⟨S, P⟩, hP⟩ : LargeBlockPattern p d))
    let i : Fin (6 * d) := ⟨j.1, hj⟩
    have henum : S.orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    have hi : i.1 < S.card := j.2
    have hc := congrFun hcode i
    simpa [largeBlockPatternCode, i, j, hi, henum] using congrArg Prod.snd hc
  have hpart : ∀ x : Fin (2 * p), P.part x = Q.part x := by
    intro x
    by_cases hx : x ∈ S
    · ext y
      by_cases hy : y ∈ S
      · rw [P.mem_part_iff_part_eq_part hy hx,
          Q.mem_part_iff_part_eq_part hy hx,
          ← largeBlockRepresentative_eq_iff P hy hx,
          ← largeBlockRepresentative_eq_iff Q hy hx,
          hrepresentative y hy, hrepresentative x hx]
      · have hyP : y ∉ P.part x := fun h ↦ hy (P.part_subset x h)
        have hyQ : y ∉ Q.part x := fun h ↦ hy (Q.part_subset x h)
        simp [hyP, hyQ]
    · simp [P.part_eq_empty.2 hx, Q.part_eq_empty.2 hx]
  have hPQ : P = Q := by
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
      have hPx : P.part x = B := P.part_eq_of_mem hB hx
      rw [← hPx, hpart x]
      exact Q.part_mem.2 (P.le hB hx)
    · intro hB
      obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
      have hQx : Q.part x = B := Q.part_eq_of_mem hB hx
      rw [← hQx, ← hpart x]
      exact P.part_mem.2 (Q.le hB hx)
  subst Q
  rfl

theorem large_block_partition_constant_bound (p d : ℕ) :
    Fintype.card (LargeBlockPattern p d) ≤ (4 * p + 1) ^ (12 * d) ∧
    ∀ pattern : LargeBlockPattern p d,
      (4 * p) ^ (12 * pattern.1.1.card) ≤ (4 * p + 1) ^ (72 * d) := by
  constructor
  · calc
      Fintype.card (LargeBlockPattern p d) ≤
          Fintype.card (Fin (6 * d) →
            (Option (Fin (2 * p)) × Option (Fin (2 * p)))) :=
        Fintype.card_le_of_injective largeBlockPatternCode
          largeBlockPatternCode_injective
      _ = ((2 * p + 1) * (2 * p + 1)) ^ (6 * d) := by
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_option,
          Fintype.card_fin]
      _ = (2 * p + 1) ^ (12 * d) := by
        rw [mul_pow, ← pow_add]
        congr 1
        omega
      _ ≤ (4 * p + 1) ^ (12 * d) :=
        Nat.pow_le_pow_left (by omega) _
  · intro pattern
    exact pow_le_pow (by omega) (by omega)
      (by
        have := largeBlockPattern_support_card_le pattern
        omega)

end Problem56
