import Problem56.Statements
import Problem56.PaperV6.GraphAndEntryExpected

open scoped BigOperators Matrix
namespace Problem56.PaperV6

theorem paperInputOutput_iff {ι ε : Type*} (src dst : ε → ι) (input output : ι) :
    PaperInputOutput src dst input output ↔
      input ≠ output ∧ MingoAdmissibleDAG src dst input output := by
  constructor
  · rintro ⟨hne, hac, _, _, hpath⟩
    refine ⟨hne, hac, ?_, ?_⟩
    · intro v
      exact Relation.reflTransGen_iff_eq_or_transGen.mp (hpath v).1
    · intro v
      simpa only [eq_comm] using
        Relation.reflTransGen_iff_eq_or_transGen.mp (hpath v).2
  · rintro ⟨hne, hdag⟩
    refine ⟨hne, hdag.1, ?_, ?_, ?_⟩
    · intro e he
      have hedge : Relation.TransGen (directedAdjacent src dst) (src e) input :=
        Relation.TransGen.single ⟨e, rfl, he⟩
      rcases hdag.2.1 (src e) with h | h
      · exact hdag.1 input (h ▸ hedge)
      · exact hdag.1 input (h.trans hedge)
    · intro e he
      have hedge : Relation.TransGen (directedAdjacent src dst) output (dst e) :=
        Relation.TransGen.single ⟨e, he, rfl⟩
      rcases hdag.2.2 (dst e) with h | h
      · exact hdag.1 output (h ▸ hedge)
      · exact hdag.1 output (hedge.trans h)
    · intro v
      constructor
      · exact Relation.reflTransGen_iff_eq_or_transGen.mpr (hdag.2.1 v)
      · apply Relation.reflTransGen_iff_eq_or_transGen.mpr
        simpa only [eq_comm] using hdag.2.2 v

theorem graph_orientation : GraphOrientationExpected := by
  intro ι ε _ _ _ dim src dst M w input output
  exact ⟨rfl, rfl, paperInputOutput_iff src dst input output⟩

theorem graph_boundary : GraphBoundaryExpected := by
  intro ι ε _ _ _ dim src dst M input output hne
  change graphContraction dim src dst (fun e ↦ (M e).transpose) (fun _ _ ↦ 1) = _
  rw [← sum_graphOperator_eq_graphContraction_one dim src dst
    (fun e ↦ (M e).transpose) input output]
  exact Finset.sum_comm

theorem graph_operator : GraphOperatorExpected := by
  intro ι ε _ _ _ dim src dst M input output hio
  change euclideanOperatorNorm
    (graphOperator dim src dst (fun e ↦ (M e).transpose) input output).transpose ≤ _
  rw [euclideanOperatorNorm_transpose]
  simpa only [euclideanOperatorNorm_transpose] using
    I04_mingo_speicher_graph_operator_specialization dim src dst
      (fun e ↦ (M e).transpose) input output
      ((paperInputOutput_iff src dst input output).mp hio).2

theorem transpose_heq_of_dims {a b n : ℕ} (ha : a = n) (hb : b = n)
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (h : HEq A B) : HEq A.transpose B.transpose := by
  subst a
  subst b
  cases h
  rfl

theorem graph_rank : GraphRankExpected := by
  intro ι ε _ _ _ dim src dst M w r hc he hp hn hw hr hedge
  change |graphContraction dim src dst (fun e ↦ (M e).transpose) w| ≤ _
  apply graph_rank_contraction dim src dst (fun e ↦ (M e).transpose) w r hc he hp
  · intro e
    simpa only [euclideanOperatorNorm_transpose] using hn e
  · exact hw
  · refine ⟨hr, ?_⟩
    rcases hedge with ⟨e, n, V, hs, ht, hV, hM⟩
    refine ⟨e, n, V, hs, ht, hV, ?_⟩
    have htranspose := transpose_heq_of_dims ht hs (M e) (V * V.transpose) hM
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using htranspose

end Problem56.PaperV6
