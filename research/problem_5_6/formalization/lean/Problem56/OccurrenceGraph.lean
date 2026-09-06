import Problem56.GraphOperatorL2
import Problem56.ProjectionMean

/-!
The occurrence graph attached to a pair of even occurrence partitions.

This file keeps the combinatorial incidence calculation literal: the three
edges attached to each factor remain separate, and a projection loop is
counted at both of its ends by `graphDegree`.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

private def occurrenceVertexOf {q : ℕ} (D : OccurrencePartitionData q) :
    ProductOccurrence q → OccurrenceVertex D
  | Sum.inl a => Sum.inl (equalityVertexAt D.middle a)
  | Sum.inr a => Sum.inr (equalityVertexAt D.input a)

private lemma occurrence_adjacent_left {q : ℕ} (D : OccurrencePartitionData q)
    (f : Fin q) :
    graphAdjacent (occurrenceSrc D) (occurrenceDst D)
      (Sum.inl (equalityVertexAt D.middle (leftOccurrence f)))
      (Sum.inr (equalityVertexAt D.input (leftOccurrence f))) := by
  refine ⟨(f, (0 : Fin 3)), Or.inl ⟨?_, ?_⟩⟩ <;>
    simp [occurrenceSrc, occurrenceDst]

private lemma occurrence_adjacent_projection {q : ℕ}
    (D : OccurrencePartitionData q) (f : Fin q) :
    graphAdjacent (occurrenceSrc D) (occurrenceDst D)
      (Sum.inr (equalityVertexAt D.input (leftOccurrence f)))
      (Sum.inr (equalityVertexAt D.input (rightOccurrence f))) := by
  refine ⟨(f, (1 : Fin 3)), Or.inl ⟨?_, ?_⟩⟩ <;>
    simp [occurrenceSrc, occurrenceDst]

private lemma occurrence_adjacent_right {q : ℕ} (D : OccurrencePartitionData q)
    (f : Fin q) :
    graphAdjacent (occurrenceSrc D) (occurrenceDst D)
      (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))
      (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))) := by
  refine ⟨(f, (2 : Fin 3)), Or.inl ⟨?_, ?_⟩⟩ <;>
    simp [occurrenceSrc, occurrenceDst]

private lemma occurrenceVertexOf_surjective {q : ℕ}
    (D : OccurrencePartitionData q) :
    Function.Surjective (occurrenceVertexOf D) := by
  intro v
  rcases v with u | u
  · obtain ⟨a, ha⟩ := D.middle.nonempty_of_mem_parts u.2
    refine ⟨Sum.inl a, ?_⟩
    change Sum.inl (equalityVertexAt D.middle a) = Sum.inl u
    congr 1
    apply Subtype.ext
    exact D.middle.part_eq_of_mem u.2 ha
  · obtain ⟨a, ha⟩ := D.input.nonempty_of_mem_parts u.2
    refine ⟨Sum.inr a, ?_⟩
    change Sum.inr (equalityVertexAt D.input a) = Sum.inr u
    congr 1
    apply Subtype.ext
    exact D.input.part_eq_of_mem u.2 ha

private lemma graphAdjacent_symm {ι ε : Type*} (src dst : ε → ι) {u v : ι} :
    graphAdjacent src dst u v → graphAdjacent src dst v u := by
  rintro ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

private lemma occurrenceVertexOf_join {q : ℕ} (D : OccurrencePartitionData q)
    {x y : ProductOccurrence q} (hxy : productJoinRelated D x y) :
    Relation.ReflTransGen (graphAdjacent (occurrenceSrc D) (occurrenceDst D))
      (occurrenceVertexOf D x) (occurrenceVertexOf D y) := by
  rcases x with a | a <;> rcases y with b | b
  · change D.middle.part a = D.middle.part b at hxy
    have hab : occurrenceVertexOf D (Sum.inl a) =
        occurrenceVertexOf D (Sum.inl b) := by
      change Sum.inl (equalityVertexAt D.middle a) =
        Sum.inl (equalityVertexAt D.middle b)
      congr 1
      exact Subtype.ext hxy
    rw [hab]
  · change ∃ f : Fin q,
      (a = leftOccurrence f ∧ b = leftOccurrence f) ∨
        (a = rightOccurrence f ∧ b = rightOccurrence f) at hxy
    obtain ⟨f, h | h⟩ := hxy
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.ReflTransGen.single (occurrence_adjacent_left D f)
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.ReflTransGen.single
        (graphAdjacent_symm _ _ (occurrence_adjacent_right D f))
  · change ∃ f : Fin q,
      (b = leftOccurrence f ∧ a = leftOccurrence f) ∨
        (b = rightOccurrence f ∧ a = rightOccurrence f) at hxy
    obtain ⟨f, h | h⟩ := hxy
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.ReflTransGen.single
        (graphAdjacent_symm _ _ (occurrence_adjacent_left D f))
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.ReflTransGen.single (occurrence_adjacent_right D f)
  · change D.input.part a = D.input.part b ∨
      ∃ f : Fin q, (a = leftOccurrence f ∧ b = rightOccurrence f) ∨
        (b = leftOccurrence f ∧ a = rightOccurrence f) at hxy
    rcases hxy with hab | ⟨f, h | h⟩
    · have huv : occurrenceVertexOf D (Sum.inr a) =
          occurrenceVertexOf D (Sum.inr b) := by
        change Sum.inr (equalityVertexAt D.input a) =
          Sum.inr (equalityVertexAt D.input b)
        congr 1
        exact Subtype.ext hab
      rw [huv]
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.ReflTransGen.single (occurrence_adjacent_projection D f)
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.ReflTransGen.single
        (graphAdjacent_symm _ _ (occurrence_adjacent_projection D f))

private theorem occurrence_graph_connected {q : ℕ}
    (D : OccurrencePartitionData q) (hjoin : ProductOccurrenceConnected D) :
    GraphConnected (occurrenceSrc D) (occurrenceDst D) := by
  intro u v
  obtain ⟨x, rfl⟩ := occurrenceVertexOf_surjective D u
  obtain ⟨y, rfl⟩ := occurrenceVertexOf_surjective D v
  exact Relation.ReflTransGen.lift' (occurrenceVertexOf D)
    (fun _ _ h ↦ occurrenceVertexOf_join D h) x y (hjoin x y)

private noncomputable def occurrenceFinEquiv (q : ℕ) :
    Fin 2 × Fin q ≃ Fin (2 * q) :=
  (Equiv.prodComm (Fin 2) (Fin q)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm q 2)))

@[simp] private lemma occurrenceFinEquiv_zero {q : ℕ} (f : Fin q) :
    occurrenceFinEquiv q (0, f) = leftOccurrence f := by
  apply Fin.ext
  simp [occurrenceFinEquiv, leftOccurrence, finProdFinEquiv]

@[simp] private lemma occurrenceFinEquiv_one {q : ℕ} (f : Fin q) :
    occurrenceFinEquiv q (1, f) = rightOccurrence f := by
  apply Fin.ext
  simp [occurrenceFinEquiv, rightOccurrence, finProdFinEquiv, Nat.add_comm]

private lemma occurrence_side_count {q : ℕ} (B : Finset (Fin (2 * q))) :
    ((Finset.univ : Finset (Fin q)).filter
        (fun f ↦ leftOccurrence f ∈ B)).card +
      ((Finset.univ : Finset (Fin q)).filter
        (fun f ↦ rightOccurrence f ∈ B)).card = B.card := by
  classical
  let E : {z : Fin 2 × Fin q // occurrenceFinEquiv q z ∈ B} ≃
      {t : Fin (2 * q) // t ∈ B} :=
    (occurrenceFinEquiv q).subtypeEquiv (fun _ ↦ Iff.rfl)
  have hcard : Fintype.card {z : Fin 2 × Fin q //
      occurrenceFinEquiv q z ∈ B} = B.card := by
    calc
      Fintype.card {z : Fin 2 × Fin q // occurrenceFinEquiv q z ∈ B} =
          Fintype.card {t : Fin (2 * q) // t ∈ B} :=
        Fintype.card_congr E
      _ = B.card := by
        rw [Fintype.card_subtype]
        simp
  rw [← hcard]
  rw [Fintype.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun s : Fin 2 ↦ fun f : Fin q ↦ occurrenceFinEquiv q (s, f) ∈ B))]
  simp only [Fintype.card_sigma, Fin.sum_univ_two]
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simp

private lemma occurrence_edge_tag_count {q : ℕ} (k : Fin 3)
    (P : Fin q → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (OccurrenceEdge q)).filter
        (fun e ↦ e.2 = k ∧ P e.1)).card =
      ((Finset.univ : Finset (Fin q)).filter P).card := by
  classical
  calc
    ((Finset.univ : Finset (OccurrenceEdge q)).filter
        (fun e ↦ e.2 = k ∧ P e.1)).card =
        (((Finset.univ : Finset (Fin q)).filter P) ×ˢ
          ((Finset.univ : Finset (Fin 3)).filter (fun t ↦ t = k))).card := by
      congr 1
      ext e
      simp [and_comm]
    _ = ((Finset.univ : Finset (Fin q)).filter P).card := by
      rw [Finset.card_product]
      have hk : (Finset.univ : Finset (Fin 3)).filter (fun t ↦ t = k) = {k} := by
        ext t
        simp
      rw [hk]
      simp

private lemma occurrence_two_edge_tag_count {q : ℕ} (k l : Fin 3)
    (hkl : k ≠ l) (P Q : Fin q → Prop) [DecidablePred P] [DecidablePred Q] :
    ((Finset.univ : Finset (OccurrenceEdge q)).filter
        (fun e ↦ (e.2 = k ∧ P e.1) ∨ (e.2 = l ∧ Q e.1))).card =
      ((Finset.univ : Finset (Fin q)).filter P).card +
        ((Finset.univ : Finset (Fin q)).filter Q).card := by
  classical
  let A := (Finset.univ : Finset (OccurrenceEdge q)).filter
    (fun e ↦ e.2 = k ∧ P e.1)
  let C := (Finset.univ : Finset (OccurrenceEdge q)).filter
    (fun e ↦ e.2 = l ∧ Q e.1)
  have hfilter : (Finset.univ : Finset (OccurrenceEdge q)).filter
      (fun e ↦ (e.2 = k ∧ P e.1) ∨ (e.2 = l ∧ Q e.1)) = A ∪ C := by
    ext e
    simp [A, C]
  have hdisj : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro e heA heC
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at heA
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at heC
    exact hkl (heA.1.symm.trans heC.1)
  rw [hfilter, Finset.card_union_of_disjoint hdisj]
  exact congrArg₂ (· + ·)
    (occurrence_edge_tag_count k P) (occurrence_edge_tag_count l Q)

private lemma occurrence_graphDegree_middle {q : ℕ}
    (D : OccurrencePartitionData q) (B : EqualityVertex D.middle) :
    graphDegree (occurrenceSrc D) (occurrenceDst D) (Sum.inl B) = B.1.card := by
  classical
  have hsrc :
      (Finset.univ : Finset (OccurrenceEdge q)).filter
          (fun e ↦ occurrenceSrc D e = Sum.inl B) =
        Finset.univ.filter
          (fun e ↦ e.2 = (0 : Fin 3) ∧ leftOccurrence e.1 ∈ B.1) := by
    ext e
    rcases e with ⟨f, k⟩
    fin_cases k <;>
      simp [occurrenceSrc, equalityVertexAt, Subtype.ext_iff,
        D.middle.part_eq_iff_mem B.2]
  have hdst :
      (Finset.univ : Finset (OccurrenceEdge q)).filter
          (fun e ↦ occurrenceDst D e = Sum.inl B) =
        Finset.univ.filter
          (fun e ↦ e.2 = (2 : Fin 3) ∧ rightOccurrence e.1 ∈ B.1) := by
    ext e
    rcases e with ⟨f, k⟩
    fin_cases k <;>
      simp [occurrenceDst, equalityVertexAt, Subtype.ext_iff,
        D.middle.part_eq_iff_mem B.2]
  rw [graphDegree, hsrc, hdst]
  calc
    _ = ((Finset.univ : Finset (Fin q)).filter
          (fun f ↦ leftOccurrence f ∈ B.1)).card +
        ((Finset.univ : Finset (Fin q)).filter
          (fun f ↦ rightOccurrence f ∈ B.1)).card :=
      congrArg₂ (· + ·)
        (occurrence_edge_tag_count (q := q) (0 : Fin 3)
          (fun f ↦ leftOccurrence f ∈ B.1))
        (occurrence_edge_tag_count (q := q) (2 : Fin 3)
          (fun f ↦ rightOccurrence f ∈ B.1))
    _ = B.1.card := occurrence_side_count B.1

private lemma occurrence_graphDegree_input {q : ℕ}
    (D : OccurrencePartitionData q) (B : EqualityVertex D.input) :
    graphDegree (occurrenceSrc D) (occurrenceDst D) (Sum.inr B) =
      2 * B.1.card := by
  classical
  have hsrc :
      (Finset.univ : Finset (OccurrenceEdge q)).filter
          (fun e ↦ occurrenceSrc D e = Sum.inr B) =
        Finset.univ.filter (fun e ↦
          (e.2 = (1 : Fin 3) ∧ leftOccurrence e.1 ∈ B.1) ∨
          (e.2 = (2 : Fin 3) ∧ rightOccurrence e.1 ∈ B.1)) := by
    ext e
    rcases e with ⟨f, k⟩
    fin_cases k <;>
      simp [occurrenceSrc, equalityVertexAt, Subtype.ext_iff,
        D.input.part_eq_iff_mem B.2]
  have hdst :
      (Finset.univ : Finset (OccurrenceEdge q)).filter
          (fun e ↦ occurrenceDst D e = Sum.inr B) =
        Finset.univ.filter (fun e ↦
          (e.2 = (0 : Fin 3) ∧ leftOccurrence e.1 ∈ B.1) ∨
          (e.2 = (1 : Fin 3) ∧ rightOccurrence e.1 ∈ B.1)) := by
    ext e
    rcases e with ⟨f, k⟩
    fin_cases k <;>
      simp [occurrenceDst, equalityVertexAt, Subtype.ext_iff,
        D.input.part_eq_iff_mem B.2]
  rw [graphDegree, hsrc, hdst]
  let L := ((Finset.univ : Finset (Fin q)).filter
    (fun f ↦ leftOccurrence f ∈ B.1)).card
  let R := ((Finset.univ : Finset (Fin q)).filter
    (fun f ↦ rightOccurrence f ∈ B.1)).card
  calc
    _ = (L + R) + (L + R) :=
      congrArg₂ (· + ·)
        (occurrence_two_edge_tag_count (q := q) (1 : Fin 3) (2 : Fin 3)
          (by decide) (fun f ↦ leftOccurrence f ∈ B.1)
          (fun f ↦ rightOccurrence f ∈ B.1))
        (occurrence_two_edge_tag_count (q := q) (0 : Fin 3) (1 : Fin 3)
          (by decide) (fun f ↦ leftOccurrence f ∈ B.1)
          (fun f ↦ rightOccurrence f ∈ B.1))
    _ = 2 * B.1.card := by
      have hsides : L + R = B.1.card := occurrence_side_count B.1
      omega

private lemma l2_opNorm_one_le_one (α : Type*) [Fintype α] [DecidableEq α] :
    ‖(1 : Matrix α α ℝ)‖ ≤ 1 := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      let _ : IsEmpty α := h
      have hz : (1 : Matrix α α ℝ) = 0 := Subsingleton.elim _ _
      rw [hz, norm_zero]
      norm_num
  | inr h =>
      let _ : Nonempty α := h
      rw [norm_one]

private lemma euclideanOperatorNorm_le_one_of_orthogonal
    {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ)
    (hA : A.transpose * A = 1) :
    euclideanOperatorNorm A ≤ 1 := by
  rw [euclideanOperatorNorm_eq_l2_opNorm]
  have hreal : A.conjTranspose = A.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [hreal, hA] at hsq
  have hone := l2_opNorm_one_le_one α
  nlinarith [norm_nonneg A]

private lemma euclideanOperatorNorm_le_one_of_projection
    {α : Type*} [Fintype α] [DecidableEq α] (P : Matrix α α ℝ)
    (hP : IsOrthogonalProjection P) :
    euclideanOperatorNorm P ≤ 1 := by
  rw [euclideanOperatorNorm_eq_l2_opNorm]
  have hreal : P.conjTranspose = P.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hreal, hP.1, hP.2] at hsq
  nlinarith [norm_nonneg P]

private lemma walshCharacter_comm {m : ℕ} (a b : WalshIndex m) :
    walshCharacter a b = walshCharacter b a := by
  have hdot : walshDot a b = walshDot b a := by
    simp only [walshDot]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  simp only [walshCharacter, hdot]

private lemma normalizedWalsh_symmetry (m : ℕ) :
    (normalizedWalsh m).transpose = normalizedWalsh m := by
  ext a b
  simp only [Matrix.transpose_apply, normalizedWalsh, walshCharacter_comm]

private lemma normalizedWalsh_involution (m : ℕ) :
    normalizedWalsh m * normalizedWalsh m = 1 := by
  classical
  ext a b
  have hcard : 0 < (walshCard m : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < walshCard m)
  have hsqrt : Real.sqrt (walshCard m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  simp only [Matrix.mul_apply, normalizedWalsh, Matrix.one_apply]
  calc
    (∑ x, walshCharacter a x / Real.sqrt (walshCard m : ℝ) *
        (walshCharacter x b / Real.sqrt (walshCard m : ℝ))) =
        (∑ x, walshCharacter a x * walshCharacter b x) /
          (walshCard m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [walshCharacter_comm x b]
      field_simp
      rw [Real.sq_sqrt hcard.le]
      ring
    _ = if a = b then 1 else 0 := by
      rw [sum_walshCharacter_pair]
      split_ifs <;> simp [hcard.ne']

private lemma normalizedWalsh_operatorNorm_le (m : ℕ) :
    euclideanOperatorNorm (normalizedWalsh m) ≤ 1 := by
  apply euclideanOperatorNorm_le_one_of_orthogonal
  rw [normalizedWalsh_symmetry, normalizedWalsh_involution]

private lemma frameProjection_isOrthogonalProjection
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (V : Matrix α (Fin r) ℝ) (hV : OrthonormalFrame V) :
    IsOrthogonalProjection (V * V.transpose) := by
  constructor
  · simp [Matrix.transpose_mul]
  · calc
      (V * V.transpose) * (V * V.transpose) =
          V * (V.transpose * V) * V.transpose := by
        simp only [Matrix.mul_assoc]
      _ = V * V.transpose := by rw [hV, Matrix.mul_one]

private lemma frameProjection_operatorNorm_le
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (V : Matrix α (Fin r) ℝ) (hV : OrthonormalFrame V) :
    euclideanOperatorNorm (V * V.transpose) ≤ 1 :=
  euclideanOperatorNorm_le_one_of_projection _
    (frameProjection_isOrthogonalProjection V hV)

private lemma reindex_isOrthogonalProjection
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (P : Matrix α α ℝ)
    (hP : IsOrthogonalProjection P) :
    IsOrthogonalProjection (Matrix.reindex e e P) := by
  constructor
  · rw [Matrix.transpose_reindex, hP.1]
  · change (Matrix.reindexRingEquiv ℝ e P) *
        (Matrix.reindexRingEquiv ℝ e P) = Matrix.reindexRingEquiv ℝ e P
    rw [← map_mul, hP.2]

private lemma reindex_orthogonal
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℝ)
    (hA : A.transpose * A = 1) :
    (Matrix.reindex e e A).transpose * Matrix.reindex e e A = 1 := by
  rw [Matrix.transpose_reindex]
  change (Matrix.reindexRingEquiv ℝ e A.transpose) *
      (Matrix.reindexRingEquiv ℝ e A) = 1
  rw [← map_mul, hA, map_one]

private lemma occurrenceEdgeMatrix_operatorNorm_le {m r q : ℕ}
    (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (e : OccurrenceEdge q) :
    euclideanOperatorNorm (occurrenceEdgeMatrix D V e) ≤ 1 := by
  classical
  by_cases he : e.2.1 = 1
  · apply euclideanOperatorNorm_le_one_of_projection
    have hreindex : occurrenceEdgeMatrix D V e =
        Matrix.reindex (walshFinEquiv m) (walshFinEquiv m)
          (V * V.transpose) := by
      ext a b
      simp [occurrenceEdgeMatrix, he, Matrix.reindex_apply]
    rw [hreindex]
    exact reindex_isOrthogonalProjection (walshFinEquiv m) _
      (frameProjection_isOrthogonalProjection V hV)
  · apply euclideanOperatorNorm_le_one_of_orthogonal
    have hreindex : occurrenceEdgeMatrix D V e =
        Matrix.reindex (walshFinEquiv m) (walshFinEquiv m)
          (normalizedWalsh m) := by
      ext a b
      simp [occurrenceEdgeMatrix, he, Matrix.reindex_apply]
    rw [hreindex]
    apply reindex_orthogonal
    rw [normalizedWalsh_symmetry, normalizedWalsh_involution]

private lemma abs_walshCharacter {m : ℕ} (a b : WalshIndex m) :
    |walshCharacter a b| = 1 := by
  simp only [walshCharacter]
  split_ifs <;> norm_num

private lemma occurrenceVertexWeight_abs_le {m q : ℕ}
    (D : OccurrencePartitionData q) (i j : Fin q → WalshIndex m)
    (v : OccurrenceVertex D) (a : Fin (walshCard m)) :
    |occurrenceVertexWeight D i j v a| ≤ 1 := by
  rcases v with B | B
  · simp only [occurrenceVertexWeight, Finset.abs_prod, abs_mul]
    apply le_of_eq
    apply Finset.prod_eq_one
    intro f _
    by_cases hl : leftOccurrence f ∈ B.1 <;>
      by_cases hr : rightOccurrence f ∈ B.1 <;>
        simp [hl, hr, abs_walshCharacter]
  · simp [occurrenceVertexWeight]

private lemma transportedFrame_orthonormal {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V) :
    OrthonormalFrame (transportedFrame V) := by
  classical
  unfold OrthonormalFrame at hV ⊢
  ext a b
  have hab := congrArg (fun A ↦ A a b) hV
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    transportedFrame] at hab ⊢
  calc
    (∑ x : Fin (walshCard m),
        V ((walshFinEquiv m).symm x) a *
          V ((walshFinEquiv m).symm x) b) =
        ∑ y : WalshIndex m, V y a * V y b := by
      symm
      exact Fintype.sum_equiv (walshFinEquiv m)
        (fun y : WalshIndex m ↦ V y a * V y b)
        (fun x : Fin (walshCard m) ↦
          V ((walshFinEquiv m).symm x) a *
            V ((walshFinEquiv m).symm x) b)
        (fun y ↦ by simp)
    _ = if a = b then 1 else 0 := hab

private lemma occurrence_hasRankProjectionEdge {m r q : ℕ} (hq : 1 ≤ q)
    (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V) :
    HasRankProjectionEdge (fun _ : OccurrenceVertex D ↦ walshCard m)
      (occurrenceSrc D) (occurrenceDst D) (occurrenceEdgeMatrix D V) r := by
  classical
  let f0 : Fin q := ⟨0, hq⟩
  let e0 : OccurrenceEdge q := (f0, (1 : Fin 3))
  refine ⟨e0, walshCard m, transportedFrame V, rfl, rfl,
    transportedFrame_orthonormal V hV, ?_⟩
  apply heq_of_eq
  ext a b
  simp [occurrenceEdgeMatrix, e0, transportedFrame,
    Matrix.mul_apply, Matrix.transpose_apply]

private noncomputable def occurrenceLabelEquiv {m q : ℕ}
    (D : OccurrencePartitionData q) :
    (OccurrenceVertex D → WalshIndex m) ≃
      (∀ _ : OccurrenceVertex D, Fin (walshCard m)) :=
  Equiv.piCongrRight (fun _ ↦ walshFinEquiv m)

@[simp] private lemma occurrenceLabelEquiv_apply {m q : ℕ}
    (D : OccurrencePartitionData q)
    (labels : OccurrenceVertex D → WalshIndex m) (v : OccurrenceVertex D) :
    occurrenceLabelEquiv D labels v = walshFinEquiv m (labels v) := rfl

private lemma occurrence_edge_product_reindex {m r q : ℕ}
    (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (labels : OccurrenceVertex D → WalshIndex m) :
    (∏ e, occurrenceEdgeMatrix D V e
      (occurrenceLabelEquiv D labels (occurrenceSrc D e))
      (occurrenceLabelEquiv D labels (occurrenceDst D e))) =
    ∏ f,
      normalizedWalsh m
          (labels (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))))
          (labels (Sum.inr (equalityVertexAt D.input (leftOccurrence f)))) *
        (V * V.transpose)
          (labels (Sum.inr (equalityVertexAt D.input (leftOccurrence f))))
          (labels (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))) *
        normalizedWalsh m
          (labels (Sum.inr (equalityVertexAt D.input (rightOccurrence f))))
          (labels (Sum.inl (equalityVertexAt D.middle (rightOccurrence f)))) := by
  classical
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro f _
  rw [Fin.prod_univ_three]
  simp [occurrenceEdgeMatrix, occurrenceSrc, occurrenceDst]

private lemma occurrence_vertex_product_reindex {m q : ℕ}
    (D : OccurrencePartitionData q) (i j : Fin q → WalshIndex m)
    (labels : OccurrenceVertex D → WalshIndex m) :
    (∏ v, occurrenceVertexWeight D i j v
      (occurrenceLabelEquiv D labels v)) =
    ∏ B : EqualityVertex D.middle,
      ∏ f,
        (if leftOccurrence f ∈ B.1 then
          walshCharacter (i f) (labels (Sum.inl B)) else 1) *
        (if rightOccurrence f ∈ B.1 then
          walshCharacter (j f) (labels (Sum.inl B)) else 1) := by
  classical
  rw [Fintype.prod_sum_type]
  simp [occurrenceVertexWeight]

private lemma occurrenceContraction_eq_graphContraction {m r q : ℕ}
    (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) :
    occurrenceContraction D V i j =
      graphContraction (fun _ : OccurrenceVertex D ↦ walshCard m)
        (occurrenceSrc D) (occurrenceDst D) (occurrenceEdgeMatrix D V)
        (occurrenceVertexWeight D i j) := by
  classical
  unfold occurrenceContraction graphContraction
  exact Fintype.sum_equiv (occurrenceLabelEquiv D)
    (fun labels : OccurrenceVertex D → WalshIndex m ↦
      (∏ f,
        normalizedWalsh m
            (labels (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))))
            (labels (Sum.inr (equalityVertexAt D.input (leftOccurrence f)))) *
          (V * V.transpose)
            (labels (Sum.inr (equalityVertexAt D.input (leftOccurrence f))))
            (labels (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))) *
          normalizedWalsh m
            (labels (Sum.inr (equalityVertexAt D.input (rightOccurrence f))))
            (labels (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))))) *
        ∏ B : EqualityVertex D.middle,
          ∏ f,
            (if leftOccurrence f ∈ B.1 then
              walshCharacter (i f) (labels (Sum.inl B)) else 1) *
            (if rightOccurrence f ∈ B.1 then
              walshCharacter (j f) (labels (Sum.inl B)) else 1))
    (fun labels : ∀ _ : OccurrenceVertex D, Fin (walshCard m) ↦
      (∏ e, occurrenceEdgeMatrix D V e
          (labels (occurrenceSrc D e)) (labels (occurrenceDst D e))) *
        ∏ v, occurrenceVertexWeight D i j v (labels v))
    (fun labels ↦ by
      rw [occurrence_edge_product_reindex,
        occurrence_vertex_product_reindex])

theorem occurrence_partitions_form_connected_even_graph
    {m r q : ℕ} (hq : 1 ≤ q) (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m)
    (hmiddle : ∀ B ∈ D.middle.parts, 0 < B.card ∧ Even B.card)
    (hinput : ∀ B ∈ D.input.parts, 0 < B.card ∧ Even B.card)
    (hjoin : ProductOccurrenceConnected D) :
    IsSurvivingOccurrencePartition D ∧
    GraphConnected (occurrenceSrc D) (occurrenceDst D) ∧
    (∀ v, 0 < graphDegree (occurrenceSrc D) (occurrenceDst D) v ∧
      Even (graphDegree (occurrenceSrc D) (occurrenceDst D) v)) ∧
    euclideanOperatorNorm (normalizedWalsh m) ≤ 1 ∧
    euclideanOperatorNorm (V * V.transpose) ≤ 1 ∧
    (∀ f B, |walshCharacter (i f) B| = 1 ∧ |walshCharacter (j f) B| = 1) ∧
    (∀ e, euclideanOperatorNorm (occurrenceEdgeMatrix D V e) ≤ 1) ∧
    (∀ v a, |occurrenceVertexWeight D i j v a| ≤ 1) ∧
    HasRankProjectionEdge (fun _ : OccurrenceVertex D ↦ walshCard m)
      (occurrenceSrc D) (occurrenceDst D) (occurrenceEdgeMatrix D V) r ∧
    occurrenceContraction D V i j =
      graphContraction (fun _ : OccurrenceVertex D ↦ walshCard m)
        (occurrenceSrc D) (occurrenceDst D) (occurrenceEdgeMatrix D V)
        (occurrenceVertexWeight D i j) := by
  classical
  have hconnected := occurrence_graph_connected D hjoin
  refine ⟨⟨hmiddle, hinput, hconnected⟩, hconnected, ?_,
    normalizedWalsh_operatorNorm_le m,
    frameProjection_operatorNorm_le V hV, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rcases v with B | B
    · rw [occurrence_graphDegree_middle]
      exact hmiddle B.1 B.2
    · rw [occurrence_graphDegree_input]
      have hB := hinput B.1 B.2
      constructor
      · omega
      · refine ⟨B.1.card, ?_⟩
        omega
  · intro f B
    exact ⟨abs_walshCharacter _ _, abs_walshCharacter _ _⟩
  · exact occurrenceEdgeMatrix_operatorNorm_le D V hV
  · exact occurrenceVertexWeight_abs_le D i j
  · exact occurrence_hasRankProjectionEdge hq D V hV
  · exact occurrenceContraction_eq_graphContraction D V i j

end Problem56
